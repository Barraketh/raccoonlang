// Shared by the hardware probes in this directory (README.md): one kernel that interprets a `Plan` of tensor-memory
// stores, `tcgen05.mma`s and tensor-memory loads over a shared-memory image the host lays out, and the host code that
// lays out operands, runs each case in its own process and checks results. The probes differ only in their plans.
//
// The kernel is one CTA of 128 threads (four warps, one per 32-lane quadrant of tensor memory). In order:
//   1. copy the image (operands in the canonical 128-byte-swizzled layouts) into 1024-byte-aligned shared memory;
//      `fence.proxy.async.shared::cta`, so the tensor cores (the async proxy) see the generic stores;
//   2. warp 0 allocates `tmem_cols` columns; thread 0 initializes one mbarrier (count 1);
//   3. every thread writes its lane (row) of each store region with `tcgen05.st.32x32b`; `tcgen05.wait::st`;
//   4. `tcgen05.fence::before_thread_sync`, `__syncthreads`, `tcgen05.fence::after_thread_sync` (PTX §9.7.18.6.4.4,
//      "Non-pipelined instructions, different thread"); thread 0 issues the MMAs and commits them to the mbarrier;
//      every thread waits for it, with a clock64 bound, and fences `after_thread_sync`;
//   5. every thread reads its lane of each load region with `tcgen05.ld.32x32b` and `tcgen05.wait::ld`;
//   6. warp 0 deallocates.
// Thread 0 records the stage it reached in mapped host memory, which the host can still read when the kernel faults,
// so a failing case says how far it got. A wait that times out records that and traps.
//
// The inline assembly follows the TinyGEMM that `gpu/Gpu.rac` generates, whose encodings ran on a B200: the
// shared-memory descriptor (SBO 1024, version 1, 128-byte swizzle) and the instruction descriptor 136316048 (bf16 ×
// bf16 → f32, both K-major, M = N = 128). Each asm statement is on one line, so `gpu/stub/asm_calls.py` can rewrite it
// for a host compiler (`gpu/check.sh`).
#pragma once
#include <cuda_runtime.h>
#include <signal.h>
#include <sys/wait.h>
#include <unistd.h>
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cerrno>
#include <cstring>
#include <string>
#include <vector>

namespace probe {

// ---- The plan ------------------------------------------------------------------------------------------------------

constexpr uint32_t kMaxRegions = 4;
constexpr uint32_t kMaxMmas = 16;

// Columns [col, col + ncols) of all 128 lanes, accessed `width` columns per instruction (4, 8 or 32: the .x4, .x8 or .x32
// form, so the first instruction's address is `col` exactly). Lane r's words are data[offset + r·ncols + j].
struct Region {
  uint32_t col, ncols, width, offset;
};

// D (tensor-memory column d_col, lane 0) = A·B (+ D when `accumulate`). A is the tensor-memory column a_col when
// `a_tmem`, else the shared-memory matrix at image byte a_off with the given LBO and SBO (bytes); B likewise at b_off.
struct Mma {
  uint32_t d_col, a_tmem, a_col, a_off, a_lbo, a_sbo, b_off, b_lbo, b_sbo, idesc, accumulate;
};

struct Plan {
  uint32_t tmem_cols;    // allocated: a power of two, 32 to 512 (PTX §9.7.18.1.2)
  uint32_t image_bytes;  // a multiple of 16
  uint32_t n_st;
  Region st[kMaxRegions];
  uint32_t n_mma;
  Mma mma[kMaxMmas];
  uint32_t n_ld;
  Region ld[kMaxRegions];
};

// What thread 0 records in mapped host memory: diag[0] the last stage reached, diag[1] a timed-out wait, diag[2] the
// allocated tensor-memory address.
enum Stage : uint32_t { kLaunched = 1, kAllocated, kStored, kIssued, kCompleted, kLoaded, kFreed };

inline const char *stage_name(uint32_t s) {
  static const char *names[] = {"not started", "launched", "tensor memory allocated", "tensor-memory stores done",
                                "MMAs issued and committed", "MMAs completed", "tensor-memory loads done",
                                "tensor memory freed"};
  return s <= kFreed ? names[s] : "?";
}

// ---- Descriptors ---------------------------------------------------------------------------------------------------

// Shared-memory matrix descriptor (PTX §9.7.18.4.1, Table 50): start address >> 4 in bits 0–13, leading byte offset
// >> 4 in 16–29, stride byte offset >> 4 in 32–45, the fixed version 1 in 46–48, base offset 0 in 49–51 (every
// operand here starts 1024-byte aligned, or 32·s bytes into an aligned K-major atom as TinyGEMM's K steps do), LBO
// mode 0 (bit 52), swizzle mode 2 = 128-byte swizzle in 61–63. With lbo = 0 and sbo = 1024 this is exactly TinyGEMM's
// descriptor (Gpu.rac `smemDesc`: high word 4611756662049472512).
__host__ __device__ inline uint64_t smem_desc(uint32_t addr, uint32_t lbo, uint32_t sbo) {
  return uint64_t((addr & 0x3FFFFu) >> 4) | (uint64_t((lbo >> 4) & 0x3FFFu) << 16) |
         (uint64_t((sbo >> 4) & 0x3FFFu) << 32) | (1ull << 46) | (2ull << 61);
}

// Instruction descriptor for kind::f16 (PTX §9.7.18.4.2, Table 51): D format f32 = 1 in bits 4–5, A format bf16 = 1
// in 7–9, B format bf16 = 1 in 10–12, no negation (13, 14), transpose A = 0 (15: K-major, which A in tensor memory
// must be), transpose B in bit 16 (1: MN-major), N >> 3 in 17–22, M >> 4 in 24–28.
constexpr uint32_t idesc_bf16(uint32_t m, uint32_t n, bool b_mn_major) {
  return (1u << 4) | (1u << 7) | (1u << 10) | (b_mn_major ? 1u << 16 : 0u) | ((n >> 3) << 17) | ((m >> 4) << 24);
}
static_assert(idesc_bf16(128, 128, false) == 136316048u, "TinyGEMM's instruction descriptor, proven on hardware");

// ---- The kernel ----------------------------------------------------------------------------------------------------

__device__ __forceinline__ void tc_fence_before() {
  asm volatile("tcgen05.fence::before_thread_sync;" : : : "memory");
}

__device__ __forceinline__ void tc_fence_after() {
  asm volatile("tcgen05.fence::after_thread_sync;" : : : "memory");
}

__device__ __forceinline__ void tmem_st4(uint32_t taddr, const uint32_t *v) {
  asm volatile("tcgen05.st.sync.aligned.32x32b.x4.b32 [%0], {%1, %2, %3, %4};" : : "r"(taddr), "r"(v[0]), "r"(v[1]), "r"(v[2]), "r"(v[3]) : "memory");
}

__device__ __forceinline__ void tmem_st8(uint32_t taddr, const uint32_t *v) {
  asm volatile("tcgen05.st.sync.aligned.32x32b.x8.b32 [%0], {%1, %2, %3, %4, %5, %6, %7, %8};" : : "r"(taddr), "r"(v[0]), "r"(v[1]), "r"(v[2]), "r"(v[3]), "r"(v[4]), "r"(v[5]), "r"(v[6]), "r"(v[7]) : "memory");
}

__device__ __forceinline__ void tmem_st32(uint32_t taddr, const uint32_t *v) {
  asm volatile("tcgen05.st.sync.aligned.32x32b.x32.b32 [%0], {%1, %2, %3, %4, %5, %6, %7, %8, %9, %10, %11, %12, %13, %14, %15, %16, %17, %18, %19, %20, %21, %22, %23, %24, %25, %26, %27, %28, %29, %30, %31, %32};" : : "r"(taddr), "r"(v[0]), "r"(v[1]), "r"(v[2]), "r"(v[3]), "r"(v[4]), "r"(v[5]), "r"(v[6]), "r"(v[7]), "r"(v[8]), "r"(v[9]), "r"(v[10]), "r"(v[11]), "r"(v[12]), "r"(v[13]), "r"(v[14]), "r"(v[15]), "r"(v[16]), "r"(v[17]), "r"(v[18]), "r"(v[19]), "r"(v[20]), "r"(v[21]), "r"(v[22]), "r"(v[23]), "r"(v[24]), "r"(v[25]), "r"(v[26]), "r"(v[27]), "r"(v[28]), "r"(v[29]), "r"(v[30]), "r"(v[31]) : "memory");
}

__device__ __forceinline__ void tmem_ld4(uint32_t taddr, uint32_t *v) {
  asm volatile("tcgen05.ld.sync.aligned.32x32b.x4.b32 {%0, %1, %2, %3}, [%4];" : "=r"(v[0]), "=r"(v[1]), "=r"(v[2]), "=r"(v[3]) : "r"(taddr) : "memory");
}

__device__ __forceinline__ void tmem_ld8(uint32_t taddr, uint32_t *v) {
  asm volatile("tcgen05.ld.sync.aligned.32x32b.x8.b32 {%0, %1, %2, %3, %4, %5, %6, %7}, [%8];" : "=r"(v[0]), "=r"(v[1]), "=r"(v[2]), "=r"(v[3]), "=r"(v[4]), "=r"(v[5]), "=r"(v[6]), "=r"(v[7]) : "r"(taddr) : "memory");
}

__device__ __forceinline__ void tmem_ld32(uint32_t taddr, uint32_t *v) {
  asm volatile("tcgen05.ld.sync.aligned.32x32b.x32.b32 {%0, %1, %2, %3, %4, %5, %6, %7, %8, %9, %10, %11, %12, %13, %14, %15, %16, %17, %18, %19, %20, %21, %22, %23, %24, %25, %26, %27, %28, %29, %30, %31}, [%32];" : "=r"(v[0]), "=r"(v[1]), "=r"(v[2]), "=r"(v[3]), "=r"(v[4]), "=r"(v[5]), "=r"(v[6]), "=r"(v[7]), "=r"(v[8]), "=r"(v[9]), "=r"(v[10]), "=r"(v[11]), "=r"(v[12]), "=r"(v[13]), "=r"(v[14]), "=r"(v[15]), "=r"(v[16]), "=r"(v[17]), "=r"(v[18]), "=r"(v[19]), "=r"(v[20]), "=r"(v[21]), "=r"(v[22]), "=r"(v[23]), "=r"(v[24]), "=r"(v[25]), "=r"(v[26]), "=r"(v[27]), "=r"(v[28]), "=r"(v[29]), "=r"(v[30]), "=r"(v[31]) : "r"(taddr) : "memory");
}

// Spins on phase `parity` of the mbarrier at `bar` for at most `limit` cycles; false when the bound ran out.
__device__ __forceinline__ bool mbar_wait(uint32_t bar, uint32_t parity, long long limit) {
  const long long start = clock64();
  for (;;) {
    uint32_t done;
    asm volatile("{\n\t.reg .pred p;\n\tmbarrier.try_wait.parity.shared::cta.b64 p, [%1], %2;\n\tselp.u32 %0, 1, 0, p;\n\t}" : "=r"(done) : "r"(bar), "r"(parity) : "memory");
    if (done) return true;
    if (clock64() - start > limit) return false;
  }
}

__device__ __forceinline__ void record(volatile uint32_t *diag, uint32_t stage) {
  diag[0] = stage;
  __threadfence_system();
}

// About two seconds at the B200's clock: far beyond any MMA here, well inside the host's per-case alarm.
constexpr long long kWaitCycles = 4000000000ll;

__global__ void __launch_bounds__(128, 1) probe_kernel(const Plan plan, const uint4 *__restrict__ image, const uint32_t *__restrict__ st_data, uint32_t *__restrict__ ld_data, volatile uint32_t *diag) {
  extern __shared__ __align__(1024) unsigned char smem[];
  const uint32_t tid = threadIdx.x, warp = tid / 32;
  const uint32_t raw = static_cast<uint32_t>(__cvta_generic_to_shared(smem));
  const uint32_t pad = ((raw + 1023u) & ~1023u) - raw;  // the image starts 1024-byte aligned, as the swizzle needs
  const uint32_t image_addr = raw + pad;
  const uint32_t ctl = pad + plan.image_bytes;  // byte offset of the control block: the mbarrier, then the slot
  const uint32_t bar = raw + ctl, slot_addr = raw + ctl + 8;
  if (tid == 0) record(diag, kLaunched);

  uint4 *dst = reinterpret_cast<uint4 *>(smem + pad);
  for (uint32_t i = tid; i < plan.image_bytes / 16; i += 128) dst[i] = image[i];
  asm volatile("fence.proxy.async.shared::cta;" : : : "memory");
  __syncwarp();
  if (warp == 0) {
    asm volatile("tcgen05.alloc.cta_group::1.sync.aligned.shared::cta.b32 [%0], %1;" : : "r"(slot_addr), "r"(plan.tmem_cols) : "memory");
    asm volatile("tcgen05.relinquish_alloc_permit.cta_group::1.sync.aligned;" : : : "memory");
  }
  if (tid == 0) {
    asm volatile("mbarrier.init.shared::cta.b64 [%0], %1;" : : "r"(bar), "r"(1u) : "memory");
    asm volatile("fence.mbarrier_init.release.cluster;" : : : "memory");
  }
  tc_fence_before();
  __syncthreads();
  tc_fence_after();
  const uint32_t tmem = *reinterpret_cast<volatile uint32_t *>(smem + ctl + 8);
  const uint32_t lane_base = (warp * 32u) << 16;  // this warp's lane quadrant (PTX §9.7.18.8.1)
  if (tid == 0) {
    diag[2] = tmem;
    record(diag, kAllocated);
  }

  uint32_t v[32];
  for (uint32_t r = 0; r < plan.n_st; ++r) {
    const Region g = plan.st[r];
    for (uint32_t j = 0; j < g.ncols; j += g.width) {
      for (uint32_t q = 0; q < g.width; ++q) v[q] = st_data[g.offset + tid * g.ncols + j + q];
      __syncwarp();
      if (g.width == 32) tmem_st32(tmem + lane_base + g.col + j, v);
      else if (g.width == 8) tmem_st8(tmem + lane_base + g.col + j, v);
      else tmem_st4(tmem + lane_base + g.col + j, v);
    }
  }
  __syncwarp();
  asm volatile("tcgen05.wait::st.sync.aligned;" : : : "memory");
  tc_fence_before();
  __syncthreads();
  tc_fence_after();
  if (tid == 0) record(diag, kStored);

  if (plan.n_mma > 0) {
    if (tid == 0) {
      for (uint32_t s = 0; s < plan.n_mma; ++s) {
        const Mma m = plan.mma[s];
        const uint64_t b = smem_desc(image_addr + m.b_off, m.b_lbo, m.b_sbo);
        if (m.a_tmem) {
          asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::1.kind::f16 [%0], [%1], %2, %3, p;\n\t}" : : "r"(tmem + m.d_col), "r"(tmem + m.a_col), "l"(b), "r"(m.idesc), "r"(m.accumulate) : "memory");
        } else {
          const uint64_t a = smem_desc(image_addr + m.a_off, m.a_lbo, m.a_sbo);
          asm volatile("{\n\t.reg .pred p;\n\tsetp.ne.b32 p, %4, 0;\n\ttcgen05.mma.cta_group::1.kind::f16 [%0], %1, %2, %3, p;\n\t}" : : "r"(tmem + m.d_col), "l"(a), "l"(b), "r"(m.idesc), "r"(m.accumulate) : "memory");
        }
      }
      asm volatile("tcgen05.commit.cta_group::1.mbarrier::arrive::one.shared::cluster.b64 [%0];" : : "r"(bar) : "memory");
      record(diag, kIssued);
    }
    if (!mbar_wait(bar, 0, kWaitCycles)) {
      diag[1] = 1;
      __threadfence_system();
      __trap();
    }
    __syncwarp();
    tc_fence_after();
    if (tid == 0) record(diag, kCompleted);
  }

  for (uint32_t r = 0; r < plan.n_ld; ++r) {
    const Region g = plan.ld[r];
    for (uint32_t j = 0; j < g.ncols; j += g.width) {
      __syncwarp();
      if (g.width == 32) tmem_ld32(tmem + lane_base + g.col + j, v);
      else if (g.width == 8) tmem_ld8(tmem + lane_base + g.col + j, v);
      else tmem_ld4(tmem + lane_base + g.col + j, v);
      asm volatile("tcgen05.wait::ld.sync.aligned;" : : : "memory");
      for (uint32_t q = 0; q < g.width; ++q) ld_data[g.offset + tid * g.ncols + j + q] = v[q];
    }
  }
  if (tid == 0) record(diag, kLoaded);

  tc_fence_before();
  __syncthreads();
  tc_fence_after();
  if (warp == 0) {
    asm volatile("tcgen05.dealloc.cta_group::1.sync.aligned.b32 %0, %1;" : : "r"(tmem), "r"(plan.tmem_cols) : "memory");
  }
  if (tid == 0) {
    asm volatile("mbarrier.inval.shared::cta.b64 [%0];" : : "r"(bar) : "memory");
    record(diag, kFreed);
  }
}

// ---- Host: values ------------------------------------------------------------------------------------------------

inline uint32_t f32_bits(float f) {
  uint32_t u;
  std::memcpy(&u, &f, 4);
  return u;
}

inline float f32_value(uint32_t u) {
  float f;
  std::memcpy(&f, &u, 4);
  return f;
}

// Round to nearest even (every value the probes use is exact in bf16 anyway, except H5's random ones).
inline uint16_t bf16_bits(float f) {
  const uint32_t u = f32_bits(f);
  return uint16_t((u + 0x7FFFu + ((u >> 16) & 1u)) >> 16);
}

inline float bf16_value(uint16_t b) { return f32_value(uint32_t(b) << 16); }

// A small deterministic generator, so a failing case is reproducible.
struct Lcg {
  uint32_t s;
  uint32_t next() { return s = s * 1664525u + 1013904223u; }
  // A multiple of 1/4 in [-2, 2]: exact in bf16, and sums of 128 products of two of them are exact in f32.
  float quarter() { return float(int((next() >> 16) % 17) - 8) / 4.0f; }
  // An integer in [-2, 2].
  float small_int() { return float(int((next() >> 16) % 5) - 2); }
  // Uniform in [-a, a], rounded to bf16.
  float uniform_bf16(float a) { return bf16_value(bf16_bits(a * (float((next() >> 8) & 0xFFFFFF) / 8388608.0f - 1.0f))); }
};

// A row-major rows × cols matrix of floats.
struct Matrix {
  uint32_t rows, cols;
  std::vector<float> v;
  Matrix(uint32_t rows, uint32_t cols) : rows(rows), cols(cols), v(size_t(rows) * cols, 0.0f) {}
  float &at(uint32_t r, uint32_t c) { return v[size_t(r) * cols + c]; }
  float at(uint32_t r, uint32_t c) const { return v[size_t(r) * cols + c]; }
};

// ---- Host: the canonical shared-memory layouts (PTX §9.7.18.3.3) ---------------------------------------------------
//
// Both are what a TMA box of 64 bf16 × `rows` rows with CU_TENSOR_MAP_SWIZZLE_128B lays down, and what the design's
// rings hold (ATTENTION.md §2.2): rows of 128 bytes, and within each 1024-byte atom of 8 rows the 16-byte chunk c of
// row r stored at chunk c ^ (r mod 8). A matrix wider than 64 elements along its contiguous dimension is several such
// boxes, one after the other.

// K-major: element (r, k) of a matrix with `rows` rows and K contiguous; box k / 64. The descriptor: SBO 1024 (8-row
// groups), LBO unused; the K = 16 step s starts at box s / 4, plus 32·(s mod 4) bytes (TinyGEMM's `smemDesc`).
inline size_t kmajor_offset(uint32_t rows, uint32_t r, uint32_t k) {
  return size_t(k / 64) * rows * 128 + size_t(r) * 128 + ((((k % 64) / 8) ^ (r % 8)) * 16) + (k % 8) * 2;
}

// MN-major: element (k, n) of a K × N matrix stored with N contiguous, `krows` rows of K; box n / 64. The canonical
// layout ((T,8,m),(8,k)):((1,T,LBO),(8T,SBO)), T = 8 elements: LBO the distance between boxes (krows·128 bytes),
// SBO 1024 between groups of 8 rows of K; the K = 16 step s starts 2048·s bytes in (ATTENTION.md §2.3, A24).
inline size_t mnmajor_offset(uint32_t krows, uint32_t k, uint32_t n) {
  return size_t(n / 64) * krows * 128 + size_t(k) * 128 + ((((n % 64) / 8) ^ (k % 8)) * 16) + (n % 8) * 2;
}

struct Image {
  std::vector<uint8_t> bytes;
  explicit Image(size_t size) : bytes((size + 15) / 16 * 16, 0) {}
  void put(size_t off, float x) {
    const uint16_t b = bf16_bits(x);
    std::memcpy(&bytes[off], &b, 2);
  }
  // m (rows × K) K-major at byte `base`.
  void put_kmajor(size_t base, const Matrix &m) {
    for (uint32_t r = 0; r < m.rows; ++r)
      for (uint32_t k = 0; k < m.cols; ++k) put(base + kmajor_offset(m.rows, r, k), m.at(r, k));
  }
  // m (K × N) MN-major at byte `base`.
  void put_mnmajor(size_t base, const Matrix &m) {
    for (uint32_t k = 0; k < m.rows; ++k)
      for (uint32_t n = 0; n < m.cols; ++n) put(base + mnmajor_offset(m.rows, k, n), m.at(k, n));
  }
};

// The layouts above, checked against a second statement of them: the canonical layout's strides in the unswizzled
// offset, then the 128-byte swizzle as an address function (Swizzle<3,4,3>: bits 7–9 XORed into bits 4–6), which
// equals the chunk formula only because every box starts 1024-byte aligned. Also that each is a bijection onto its
// bytes. Pure host code; every probe runs it first.
inline bool layouts_selftest() {
  auto swizzle = [](size_t off) { return off ^ ((off >> 3) & 0x70); };
  const uint32_t rows = 128, K = 128;
  std::vector<uint8_t> seen(size_t(rows) * K * 2, 0);
  for (uint32_t r = 0; r < rows; ++r)
    for (uint32_t k = 0; k < K; ++k) {
      const size_t canonical = size_t(k / 64) * rows * 128 + size_t(r / 8) * 1024 + (r % 8) * 128 + (k % 64) * 2;
      const size_t off = kmajor_offset(rows, r, k);
      if (off != swizzle(canonical) || off % 2 || off >= seen.size() || seen[off]++) return false;
    }
  std::fill(seen.begin(), seen.end(), 0);
  const uint32_t lbo = rows * 128, sbo = 1024;
  for (uint32_t k = 0; k < K; ++k)
    for (uint32_t n = 0; n < 128; ++n) {
      const size_t canonical = (n % 8) * 2 + ((n % 64) / 8) * 16 + (n / 64) * lbo + (k % 8) * 128 + (k / 8) * sbo;
      const size_t off = mnmajor_offset(K, k, n);
      if (off != swizzle(canonical) || off % 2 || off >= seen.size() || seen[off]++) return false;
    }
  return true;
}

// ---- Host: running a plan ------------------------------------------------------------------------------------------

// The running case's mapped diagnostics, for the alarm handler to report when a kernel hangs.
inline volatile uint32_t *g_diag = nullptr;

// Prints a failed CUDA call and makes the enclosing function return false.
#define PROBE_CHECK(call)                                                                                            \
  do {                                                                                                               \
    cudaError_t status_ = (call);                                                                                    \
    if (status_ != cudaSuccess) {                                                                                    \
      std::printf("    CUDA error at %s:%d: %s: %s\n", __FILE__, __LINE__, #call, cudaGetErrorString(status_));     \
      return false;                                                                                                  \
    }                                                                                                                \
  } while (0)

// Runs `plan` once: `image` into shared memory, `st` the store regions' words, `ld` (resized to `ld_words`) the load
// regions' words. False, having printed why and how far the kernel got, on any CUDA error.
inline bool run_plan(const Plan &plan, const Image &image, const std::vector<uint32_t> &st, size_t ld_words,
                     std::vector<uint32_t> &ld) {
  if (plan.image_bytes != image.bytes.size() || plan.image_bytes % 16) {
    std::printf("    bad plan: image of %zu bytes, plan says %u\n", image.bytes.size(), plan.image_bytes);
    return false;
  }
  uint32_t *diag_host = nullptr, *diag_dev = nullptr;
  PROBE_CHECK(cudaHostAlloc(reinterpret_cast<void **>(&diag_host), 4 * sizeof(uint32_t), cudaHostAllocMapped));
  std::memset(diag_host, 0, 4 * sizeof(uint32_t));
  PROBE_CHECK(cudaHostGetDevicePointer(reinterpret_cast<void **>(&diag_dev), diag_host, 0));
  g_diag = diag_host;
  uint4 *d_image = nullptr;
  uint32_t *d_st = nullptr, *d_ld = nullptr;
  PROBE_CHECK(cudaMalloc(&d_image, std::max<size_t>(image.bytes.size(), 16)));
  PROBE_CHECK(cudaMalloc(&d_st, std::max<size_t>(st.size(), 1) * 4));
  PROBE_CHECK(cudaMalloc(&d_ld, std::max<size_t>(ld_words, 1) * 4));
  if (!image.bytes.empty())
    PROBE_CHECK(cudaMemcpy(d_image, image.bytes.data(), image.bytes.size(), cudaMemcpyHostToDevice));
  if (!st.empty()) PROBE_CHECK(cudaMemcpy(d_st, st.data(), st.size() * 4, cudaMemcpyHostToDevice));
  PROBE_CHECK(cudaMemset(d_ld, 0xAB, std::max<size_t>(ld_words, 1) * 4));  // an unwritten word shows as 0xABABABAB
  const size_t smem = 1024 + image.bytes.size() + 16;
  PROBE_CHECK(cudaFuncSetAttribute(reinterpret_cast<const void *>(&probe_kernel),
                                   cudaFuncAttributeMaxDynamicSharedMemorySize, int(smem)));
  Plan p = plan;
  const uint4 *a0 = d_image;
  const uint32_t *a1 = d_st;
  uint32_t *a2 = d_ld;
  volatile uint32_t *a3 = diag_dev;
  void *args[] = {&p, &a0, &a1, &a2, &a3};
  cudaError_t launch = cudaLaunchKernel(reinterpret_cast<const void *>(&probe_kernel), dim3(1), dim3(128), args, smem,
                                        nullptr);
  cudaError_t done = launch == cudaSuccess ? cudaDeviceSynchronize() : launch;
  if (done != cudaSuccess) {
    const volatile uint32_t *d = diag_host;
    std::printf("    kernel failed: %s; last stage reached: %s%s; tensor-memory address 0x%08x\n",
                cudaGetErrorString(done), stage_name(d[0]), d[1] ? "; an mbarrier wait timed out" : "", d[2]);
    return false;
  }
  ld.assign(ld_words, 0);
  PROBE_CHECK(cudaMemcpy(ld.data(), d_ld, ld_words * 4, cudaMemcpyDeviceToHost));
  cudaFree(d_image);
  cudaFree(d_st);
  cudaFree(d_ld);
  cudaFreeHost(diag_host);
  return true;
}

// ---- Host: cases, each in its own process --------------------------------------------------------------------------
//
// A case runs in a forked child, so a fault that poisons the CUDA context (an illegal instruction, a trap) ends only
// that case, and an alarm bounds it. The parent never touches CUDA. A case body returns kPass or kFail; a CUDA error is
// kError. Timeouts: the kernel's bounded mbarrier wait traps (kError); anything else that hangs (a launch, a copy)
// meets the alarm, whose handler prints the stage the kernel reached and exits with kTimeout.

enum Outcome { kPass = 0, kFail = 1, kError = 2, kTimeout = 3, kCrash = 4 };

inline void on_alarm(int) {
  char line[160];
  const volatile uint32_t *d = g_diag;
  const int n = d ? std::snprintf(line, sizeof line, "    alarm: case hung; last kernel stage reached: %s%s\n",
                                  stage_name(d[0]), d[1] ? "; an mbarrier wait timed out" : "")
                  : std::snprintf(line, sizeof line, "    alarm: case hung before any kernel launch\n");
  if (n > 0) (void)!write(1, line, size_t(n));
  _exit(kTimeout);
}

inline const char *outcome_name(int o) {
  static const char *names[] = {"PASS", "FAIL", "ERROR", "TIMEOUT", "CRASH"};
  return o >= 0 && o <= kCrash ? names[o] : "CRASH";
}

template <class Body> int run_case(const char *probe, const std::string &name, Body body) {
  std::printf("== %s %s\n", probe, name.c_str());
  std::fflush(stdout);
  const pid_t pid = fork();
  if (pid < 0) {
    std::perror("fork");
    return kError;
  }
  if (pid == 0) {
    setvbuf(stdout, nullptr, _IOLBF, 0);  // a killed child keeps what it printed
    signal(SIGALRM, on_alarm);
    alarm(60);
    const int r = body();
    std::fflush(stdout);
    _exit(r);
  }
  int status = 0;
  while (waitpid(pid, &status, 0) < 0) {
    if (errno != EINTR) {
      std::perror("waitpid");
      return kCrash;
    }
  }
  int outcome = kCrash;
  if (WIFEXITED(status) && WEXITSTATUS(status) <= kTimeout) outcome = WEXITSTATUS(status);
  else if (WIFSIGNALED(status) && WTERMSIG(status) == SIGALRM) outcome = kTimeout;
  std::printf("%-7s %s %s\n", outcome_name(outcome), probe, name.c_str());
  std::fflush(stdout);
  return outcome;
}

// Compares D (the f32 words of a load region) with an expected matrix, by value (so −0 equals +0). Prints the first
// few mismatches, with `explain` describing each if given. Returns the number of mismatches.
template <class Explain>
size_t compare_d(const std::vector<uint32_t> &got, size_t offset, uint32_t ncols, uint32_t col0, const Matrix &want,
                 Explain explain) {
  size_t bad = 0;
  for (uint32_t r = 0; r < want.rows; ++r)
    for (uint32_t c = 0; c < want.cols; ++c) {
      const uint32_t word = got[offset + size_t(r) * ncols + col0 + c];
      if (f32_value(word) == want.at(r, c)) continue;
      if (bad < 8) {
        std::printf("    D[%u][%u] = %g (0x%08x), want %g", r, c, f32_value(word), word, want.at(r, c));
        explain(r, c, f32_value(word));
        std::printf("\n");
      }
      ++bad;
    }
  if (bad) std::printf("    %zu of %u elements differ\n", bad, want.rows * want.cols);
  return bad;
}

inline void no_explanation(uint32_t, uint32_t, float) {}

// D = A·Bᵀ for A (rows × K) and Bt (N × K), in double; exact for the probes' values, which are all multiples of 1/4.
inline Matrix product_abt(const Matrix &a, const Matrix &bt) {
  Matrix d(a.rows, bt.rows);
  for (uint32_t i = 0; i < a.rows; ++i)
    for (uint32_t n = 0; n < bt.rows; ++n) {
      double s = 0;
      for (uint32_t k = 0; k < a.cols; ++k) s += double(a.at(i, k)) * double(bt.at(n, k));
      d.at(i, n) = float(s);
    }
  return d;
}

inline Matrix transpose(const Matrix &m) {
  Matrix t(m.cols, m.rows);
  for (uint32_t r = 0; r < m.rows; ++r)
    for (uint32_t c = 0; c < m.cols; ++c) t.at(c, r) = m.at(r, c);
  return t;
}

// A permutation of 0..127 that moves every index across 8-row groups and 64-element halves: σ(n) = (37n + 11) mod 128.
inline uint32_t sigma(uint32_t n) { return (37 * n + 11) % 128; }

// A 128 × 128 A whose row i holds 1..128 rotated by i: every value exact in bf16, distinct within a row, so a D
// element that is some A[i][k] names the k it came from (`code_k`).
inline Matrix code_matrix() {
  Matrix a(128, 128);
  for (uint32_t i = 0; i < 128; ++i)
    for (uint32_t k = 0; k < 128; ++k) a.at(i, k) = float((k + i) % 128 + 1);
  return a;
}

// The k with code_matrix()[i][k] == v, or −1.
inline int code_k(uint32_t i, float v) {
  if (v < 1 || v > 128 || v != float(int(v))) return -1;
  return int((uint32_t(v) - 1 + 128 - i % 128) % 128);
}

// The K-major MMA steps of TinyGEMM over a K-major operand with `rows` rows at image byte `base`: step s starts at box
// s / 4, plus 32 bytes per step within it.
inline uint32_t kmajor_step(uint32_t base, uint32_t rows, uint32_t s) { return base + (s / 4) * rows * 128 + (s % 4) * 32; }

}  // namespace probe
