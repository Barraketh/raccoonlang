// Runs a generated tensor-core GEMM against a CPU reference, checks that its launcher refuses what the kernel cannot
// handle, and times it. Needs an sm_100a GPU. For TinyGEMM:
//
//   gpu/gen.sh gpu/examples/tinygemm.rac > tinygemm.cu
//   nvcc -std=c++17 -O2 -arch=sm_100a -o tinygemm_test tinygemm.cu gpu/harness/gemm_test.cu -lcuda
//   ./tinygemm_test
//
// For another kernel, name its launcher: `-DGEMM_LAUNCH=persistent_gemm_launch` for examples/persistent_gemm.rac.
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

#ifndef GEMM_LAUNCH
#define GEMM_LAUNCH tinygemm_launch
#endif

extern "C" cudaError_t GEMM_LAUNCH(const __nv_bfloat16 *A, const __nv_bfloat16 *B, float *C, unsigned M, unsigned N,
                                   unsigned K, cudaStream_t stream);

#define CHECK(call)                                                                                                  \
  do {                                                                                                               \
    cudaError_t status_ = (call);                                                                                    \
    if (status_ != cudaSuccess) {                                                                                    \
      std::fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, cudaGetErrorString(status_));                          \
      std::exit(2);                                                                                                  \
    }                                                                                                                \
  } while (0)

struct Problem {
  unsigned m, n, k;
  std::vector<float> a, b;  // A is M×K and B is N×K, K contiguous; values exactly representable in bf16
  static constexpr size_t guard = 4096;  // sentinel floats on each side of C
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
    CHECK(cudaMalloc(&dAlloc, (size_t(m) * n + 2 * guard) * sizeof(float)));
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

  cudaError_t run() { return GEMM_LAUNCH(dA, dB, dC, m, n, k, nullptr); }

  // Runs once from a NaN-filled C inside sentinel guard bands, and returns the number of elements that differ from the
  // reference or guard values that changed.
  size_t mismatches() {
    const size_t total = size_t(m) * n + 2 * guard;
    CHECK(cudaMemset(dAlloc, 0x7f, total * sizeof(float)));  // sentinel 0x7f7f7f7f, a finite float
    CHECK(cudaMemset(dC, 0xff, size_t(m) * n * sizeof(float)));
    CHECK(run());
    CHECK(cudaDeviceSynchronize());
    std::vector<float> all(total);
    CHECK(cudaMemcpy(all.data(), dAlloc, total * sizeof(float), cudaMemcpyDeviceToHost));
    const float *c = all.data() + guard;
    size_t bad = 0;
    unsigned sentinel;
    for (size_t i = 0; i < total; ++i) {
      if (i >= guard && i < guard + size_t(m) * n) continue;
      std::memcpy(&sentinel, &all[i], sizeof(sentinel));
      if (sentinel != 0x7f7f7f7fu) {
        if (bad < 5) std::printf("    guard element %td written\n", ptrdiff_t(i) - ptrdiff_t(guard));
        ++bad;
      }
    }
    for (unsigned i = 0; i < m; ++i)
      for (unsigned j = 0; j < n; ++j) {
        double want = 0;
        for (unsigned p = 0; p < k; ++p) want += double(a[size_t(i) * k + p]) * double(b[size_t(j) * k + p]);
        float got = c[size_t(i) * n + j];
        if (!(double(got) == want)) {
          if (bad < 5) std::printf("    C[%u][%u] = %g, want %g\n", i, j, got, want);
          ++bad;
        }
      }
    return bad;
  }
};

int main() {
  int failures = 0;

  // Whole tiles, several K steps (more than the ring's stages), partial tiles in every dimension, tiny ones, and, for
  // a persistent kernel, several tiles per CTA (4096×4096 is 1024 tiles, about 7 per CTA on 148 SMs), so tile loops
  // run again and accumulator buffers are reused.
  const unsigned sizes[][3] = {{128, 128, 64},     {256, 256, 256},  {384, 256, 1024},  {200, 136, 72},
                               {128, 128, 8},      {1, 8, 8},        {129, 257, 520},   {1000, 1000, 1000},
                               {2048, 2048, 200},  {1920, 2688, 72}, {4096, 4096, 72}};
  for (auto &s : sizes) {
    Problem p(s[0], s[1], s[2], s[0] * 7919u + s[1] * 104729u + s[2]);
    size_t bad = 0;
    for (int rep = 0; rep < 3; ++rep) bad += p.mismatches();
    std::printf("%s M=%u N=%u K=%u%s\n", bad ? "FAIL" : "ok  ", s[0], s[1], s[2],
                bad ? (" (" + std::to_string(bad) + " wrong)").c_str() : "");
    failures += bad != 0;
  }

  // What the launcher must refuse rather than launch: a row of A or B that is not a multiple of 16 bytes (TMA
  // strides), and an empty K extent.
  const unsigned refused[][3] = {{128, 128, 10}, {128, 128, 0}};
  for (auto &s : refused) {
    Problem p(s[0], s[1], s[2], 1);
    cudaError_t status = p.run();
    std::printf("%s M=%u N=%u K=%u refused: %s\n", status != cudaSuccess ? "ok  " : "FAIL", s[0], s[1], s[2],
                cudaGetErrorString(status));
    failures += status == cudaSuccess;
  }

  // Throughput on a large square problem.
  {
    const unsigned n = 8192;
    Problem p(n, n, n, 42);
    CHECK(p.run());
    CHECK(cudaDeviceSynchronize());
    cudaEvent_t start, stop;
    CHECK(cudaEventCreate(&start));
    CHECK(cudaEventCreate(&stop));
    const int reps = 20;
    CHECK(cudaEventRecord(start));
    for (int i = 0; i < reps; ++i) CHECK(p.run());
    CHECK(cudaEventRecord(stop));
    CHECK(cudaEventSynchronize(stop));
    float ms = 0;
    CHECK(cudaEventElapsedTime(&ms, start, stop));
    double tflops = 2.0 * n * n * double(n) * reps / (ms * 1e-3) / 1e12;
    std::printf("perf M=N=K=%u: %.3f ms per GEMM, %.1f TFLOP/s\n", n, ms / reps, tflops);
    cudaEventDestroy(start);
    cudaEventDestroy(stop);
  }

  std::printf(failures ? "%d check(s) failed\n" : "all checks passed\n", failures);
  return failures ? 1 : 0;
}
