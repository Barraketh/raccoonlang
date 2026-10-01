// Runs the persistent pair GEMM (encoding/examples/gemm_pair.rac) against a CPU reference and checks that its launcher
// refuses what the kernel cannot handle; with `time`, times it. Needs an sm_100a GPU. `run_gemm_pair.sh` builds and runs
// it:
//
//   gpu/gen.sh gpu/encoding/examples/gemm_pair.rac > gemm_pair.cu
//   nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a -o gemm_pair_test gemm_pair.cu \
//     gpu/encoding/harness/gemm_pair_test.cu -lcuda
//   ./gemm_pair_test                      correctness and refusals
//   ./gemm_pair_test time [runs [n …]]    the median of `runs` timed runs (100) at each n³ (8192³ and 4096³)
//
// The kernel computes 256×256 tiles of C, one pair of CTAs per two SMs looping over the tiles its cluster index gives
// it, each CTA 128 rows of a tile, stored by TMA. So the sizes cover a tile whose second CTA's rows lie partly or wholly
// past M, whose second half of B lies partly or wholly past N (the loads' clipping), whose 32-column chunks lie partly
// or wholly past N (the stores' clipping), tails of K, fewer tiles than pairs, and several tiles per pair, so that the
// stage ring and the accumulator ring wrap across tiles.
//
// Inputs are small multiples of 1/4, so every product and partial sum is exact in f32 whatever the order of
// accumulation: the result must equal the reference exactly. C starts as NaN, so an element the kernel never writes
// shows up as a mismatch, and it sits between two guard bands of sentinels that no write may touch. Every size runs
// three times, since a race need not show on one run.
#include <cuda_bf16.h>
#include <cuda_runtime.h>
#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>

extern "C" cudaError_t gemm_pair_launch(const __nv_bfloat16 *A, const __nv_bfloat16 *B, float *C, unsigned M, unsigned N,
                                        unsigned K, cudaStream_t stream);

#define CHECK(call)                                                                                                  \
  do {                                                                                                               \
    cudaError_t status_ = (call);                                                                                    \
    if (status_ != cudaSuccess) {                                                                                    \
      std::fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, cudaGetErrorString(status_));                          \
      std::exit(2);                                                                                                  \
    }                                                                                                                \
  } while (0)

// The pairs the launcher starts on this device: one per two SMs.
static unsigned devicePairs() {
  int device = 0, sms = 0;
  CHECK(cudaGetDevice(&device));
  CHECK(cudaDeviceGetAttribute(&sms, cudaDevAttrMultiProcessorCount, device));
  return unsigned(sms) / 2;
}

struct Problem {
  unsigned m, n, k;
  std::vector<float> a, b;  // A is M×K and B is N×K, K contiguous; values exactly representable in bf16
  // Sentinel floats before C, and after it: as many again and 256 rows of C, so a store of a row past M would land in
  // the guard.
  static constexpr size_t guard = 4096;
  size_t after() const { return guard + size_t(256) * n; }
  size_t total() const { return guard + size_t(m) * n + after(); }
  __nv_bfloat16 *dA = nullptr, *dB = nullptr;
  float *dAlloc = nullptr, *dC = nullptr;

  Problem(unsigned m, unsigned n, unsigned k, uint32_t seed) : m(m), n(n), k(k), a(size_t(m) * k), b(size_t(n) * k) {
    auto next = [&seed]() {
      seed = seed * 1664525u + 1013904223u;
      return float(int((seed >> 16) % 17) - 8) / 4.0f;
    };
    for (float &x : a) x = next();
    for (float &x : b) x = next();
    CHECK(cudaMalloc(&dA, std::max<size_t>(a.size(), 1) * sizeof(__nv_bfloat16)));
    CHECK(cudaMalloc(&dB, std::max<size_t>(b.size(), 1) * sizeof(__nv_bfloat16)));
    CHECK(cudaMalloc(&dAlloc, total() * sizeof(float)));
    dC = dAlloc + guard;
    upload(dA, a);
    upload(dB, b);
  }
  ~Problem() {
    cudaFree(dA);
    cudaFree(dB);
    cudaFree(dAlloc);
  }

  static void upload(__nv_bfloat16 *dst, const std::vector<float> &src) {
    std::vector<__nv_bfloat16> host(src.size());
    for (size_t i = 0; i < src.size(); ++i) host[i] = __float2bfloat16(src[i]);
    CHECK(cudaMemcpy(dst, host.data(), host.size() * sizeof(__nv_bfloat16), cudaMemcpyHostToDevice));
  }

  cudaError_t run() { return gemm_pair_launch(dA, dB, dC, m, n, k, nullptr); }

  unsigned tiles() const { return ((m + 255) / 256) * ((n + 255) / 256); }

  double reference(unsigned i, unsigned j) const {
    double want = 0;
    for (unsigned p = 0; p < k; ++p) want += double(a[size_t(i) * k + p]) * double(b[size_t(j) * k + p]);
    return want;
  }

  // Runs once from a NaN-filled C inside sentinel guard bands, and returns C and its guards.
  std::vector<float> runFromNaN() {
    CHECK(cudaMemset(dAlloc, 0x7f, total() * sizeof(float)));  // sentinel 0x7f7f7f7f, a finite float
    CHECK(cudaMemset(dC, 0xff, size_t(m) * n * sizeof(float)));
    CHECK(run());
    CHECK(cudaDeviceSynchronize());
    std::vector<float> all(total());
    CHECK(cudaMemcpy(all.data(), dAlloc, total() * sizeof(float), cudaMemcpyDeviceToHost));
    return all;
  }

  // The guard elements that changed.
  size_t guardsWritten(const std::vector<float> &all) const {
    size_t bad = 0;
    unsigned sentinel;
    for (size_t i = 0; i < all.size(); ++i) {
      if (i >= guard && i < guard + size_t(m) * n) continue;
      std::memcpy(&sentinel, &all[i], sizeof(sentinel));
      if (sentinel != 0x7f7f7f7fu) {
        if (bad < 5) std::printf("    guard element %td written\n", ptrdiff_t(i) - ptrdiff_t(guard));
        ++bad;
      }
    }
    return bad;
  }

  bool wrong(const float *c, unsigned i, unsigned j, size_t bad) const {
    const double want = reference(i, j);
    const float got = c[size_t(i) * n + j];
    if (double(got) == want) return false;
    if (bad < 5) std::printf("    C[%u][%u] = %g, want %g\n", i, j, got, want);
    return true;
  }

  // Runs once and returns the number of elements that differ from the reference, and of guard values that changed.
  size_t mismatches() {
    const std::vector<float> all = runFromNaN();
    const float *c = all.data() + guard;
    size_t bad = guardsWritten(all);
    for (unsigned i = 0; i < m; ++i)
      for (unsigned j = 0; j < n; ++j) bad += wrong(c, i, j, bad);
    return bad;
  }

  // As `mismatches`, for a problem too large for a whole reference: every element must be written (no NaN left), and
  // `samples` elements, among them each tile's corners, must equal the reference.
  size_t sampledMismatches(unsigned samples) {
    const std::vector<float> all = runFromNaN();
    const float *c = all.data() + guard;
    size_t bad = guardsWritten(all);
    for (size_t i = 0; i < size_t(m) * n; ++i)
      if (c[i] != c[i]) {
        if (bad < 5) std::printf("    C[%zu][%zu] not written\n", i / n, i % n);
        ++bad;
      }
    for (unsigned i = 0; i < m; i += 256)
      for (unsigned j = 0; j < n; j += 256) {
        const unsigned rows[] = {i, std::min(i + 127, m - 1), std::min(i + 128, m - 1), std::min(i + 255, m - 1)};
        const unsigned cols[] = {j, std::min(j + 31, n - 1), std::min(j + 128, n - 1), std::min(j + 255, n - 1)};
        for (unsigned r : rows)
          for (unsigned s : cols) bad += wrong(c, r, s, bad);
      }
    uint32_t seed = 12345;
    for (unsigned t = 0; t < samples; ++t) {
      seed = seed * 1664525u + 1013904223u;
      const unsigned i = seed % m;
      seed = seed * 1664525u + 1013904223u;
      bad += wrong(c, i, seed % n, bad);
    }
    return bad;
  }
};

static int correctness() {
  int failures = 0;
  const unsigned pairs = devicePairs();
  std::printf("%u pairs\n", pairs);

  // One tile, and several; K of one slice, of more slices than the ring's six stages, and with a tail; M with the
  // second CTA's rows partly (129, 200, 300) or wholly (100) past M; N with the second half of B partly (136, 200, 1000)
  // or wholly (8, 100) past N, and chunks of 32 columns partly past N (8, 100, 136, 1000); more tiles than pairs, so
  // that a pair visits several tiles and the accumulator ring wraps across them (4096: three or four tiles a pair on a
  // B200's 74 pairs), with the stage ring wrapping inside a tile as well (2560 × 2048, K = 520: 80 tiles of nine
  // stages each), and a last band of fewer rows than the others (2304: nine tile rows, bands of eight).
  const unsigned sizes[][3] = {{256, 256, 64},    {512, 512, 512},   {256, 256, 1032},   {200, 256, 72},
                               {300, 200, 64},    {100, 256, 128},   {129, 136, 8},      {256, 8, 64},
                               {256, 100, 520},   {1, 8, 8},         {1000, 1000, 1000}, {2048, 1536, 200},
                               {2304, 4352, 192}, {4096, 4096, 64},  {2560, 2048, 520}};
  for (auto &s : sizes) {
    Problem p(s[0], s[1], s[2], s[0] * 7919u + s[1] * 104729u + s[2]);
    size_t bad = 0;
    for (int rep = 0; rep < 3; ++rep) bad += p.mismatches();
    std::printf("%s M=%u N=%u K=%u (%u tiles)%s\n", bad ? "FAIL" : "ok  ", s[0], s[1], s[2], p.tiles(),
                bad ? (" (" + std::to_string(bad) + " wrong)").c_str() : "");
    failures += bad != 0;
  }

  // What the launcher must refuse rather than launch: a row of C that is not a multiple of 16 bytes (TMA stores), a row
  // of A or B that is not (TMA strides), and an empty extent, the last two refused by the encoding of the maps.
  const unsigned refused[][3] = {{256, 130, 64}, {256, 256, 10}, {256, 256, 0}, {0, 256, 64}};
  for (auto &s : refused) {
    Problem p(s[0], s[1], s[2], 1);
    cudaError_t status = p.run();
    std::printf("%s M=%u N=%u K=%u refused: %s\n", status != cudaSuccess ? "ok  " : "FAIL", s[0], s[1], s[2],
                cudaGetErrorString(status));
    failures += status == cudaSuccess;
  }
  // And extents whose element index into C does not fit 32 bits, or whose rows TMA's signed coordinates cannot reach:
  // refused by the launcher's own checks, before it reads any array. Each breaks one check alone (N = 0 passes every
  // check but M's; the map encoding, which would refuse it too, comes after them).
  const unsigned huge[][3] = {{65536, 65536, 64}, {2147483648u, 0, 64}, {256, 256, 2147483648u}};
  for (auto &s : huge) {
    cudaError_t status = gemm_pair_launch(nullptr, nullptr, nullptr, s[0], s[1], s[2], nullptr);
    std::printf("%s M=%u N=%u K=%u refused: %s\n", status != cudaSuccess ? "ok  " : "FAIL", s[0], s[1], s[2],
                cudaGetErrorString(status));
    failures += status == cudaSuccess;
  }
  std::printf("%s\n", failures ? "FAILED" : "all passed");
  return failures ? 1 : 0;
}

// Times `runs` launches of an n³ GEMM, each between its own pair of events, after 20 untimed ones, and prints the
// median, the fastest and the mean, as TFLOP/s at 2·n³. The result is checked first, by `sampledMismatches`.
static int timing(unsigned n, int runs) {
  Problem p(n, n, n, 42);
  const size_t bad = p.sampledMismatches(4096);
  if (bad) {
    std::printf("FAIL M=N=K=%u (%zu wrong): not timed\n", n, bad);
    return 1;
  }
  for (int i = 0; i < 20; ++i) CHECK(p.run());
  CHECK(cudaDeviceSynchronize());
  std::vector<cudaEvent_t> events(2 * size_t(runs));
  for (cudaEvent_t &e : events) CHECK(cudaEventCreate(&e));
  for (int i = 0; i < runs; ++i) {
    CHECK(cudaEventRecord(events[2 * i]));
    CHECK(p.run());
    CHECK(cudaEventRecord(events[2 * i + 1]));
  }
  CHECK(cudaEventSynchronize(events.back()));
  std::vector<float> ms(runs);
  for (int i = 0; i < runs; ++i) CHECK(cudaEventElapsedTime(&ms[i], events[2 * i], events[2 * i + 1]));
  for (cudaEvent_t &e : events) cudaEventDestroy(e);
  double mean = 0;
  for (float t : ms) mean += t;
  mean /= runs;
  std::sort(ms.begin(), ms.end());
  const double median = runs % 2 ? ms[runs / 2] : (ms[runs / 2 - 1] + ms[runs / 2]) / 2.0;
  const double flop = 2.0 * n * n * double(n);
  auto tflops = [flop](double t) { return flop / (t * 1e-3) / 1e12; };
  std::printf("time M=N=K=%u: median %.4f ms (%.1f TFLOP/s), fastest %.4f ms (%.1f), mean %.4f ms (%.1f), %d runs, %u tiles\n",
              n, median, tflops(median), double(ms[0]), tflops(ms[0]), mean, tflops(mean), runs, p.tiles());
  return 0;
}

int main(int argc, char **argv) {
  if (argc > 1 && std::string(argv[1]) == "time") {
    const int runs = argc > 2 ? std::max(1, std::atoi(argv[2])) : 100;
    std::vector<unsigned> sizes;
    for (int i = 3; i < argc; ++i) sizes.push_back(unsigned(std::atoi(argv[i])));
    if (sizes.empty()) sizes = {8192, 4096};
    std::printf("%u pairs\n", devicePairs());
    int failed = 0;
    for (unsigned n : sizes) failed |= timing(n, runs);
    return failed;
  }
  return correctness();
}
