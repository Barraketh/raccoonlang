// Runs the generated A1 attention kernel against a CPU reference, checks that its launcher refuses what the kernel
// cannot handle, and times it (gpu/ATTENTION.md §1.3, §6). Needs an sm_100a GPU:
//
//   gpu/gen.sh gpu/encoding/examples/attention.rac > attention.cu
//   nvcc -std=c++17 -O2 -Xcompiler -pthread -gencode arch=compute_100a,code=sm_100a -o attention_test attention.cu \
//     gpu/encoding/harness/attention_test.cu -lcuda
//   ./attention_test
//
// The reference is computed in double precision from the same bf16 inputs, `s`, LSE and O exactly as §1.2's first
// block writes them with `scale_log2` as passed, and rounded to f32 before comparing. Every size runs four input sets,
// each three times, since a race need not show on one run:
//   T1  random: Q in [-1, 1] (every fourth row of a head in [-8, 8], a peaked row), K and V in [-1, 1]; every element
//       |O - O_ref| <= 2^-7 · max|V| (V of the head), every row |LSE - LSE_ref| <= 2^-8 + 2^-20 · |LSE_ref|.
//   T2  exact canaries, V in multiples of 1/4 and every `seq` a power of two: K = 0 (uniform attention, O the column
//       mean of V), and one-hot (Q row i is 2048 · e_(i mod 128), K row j is e_(j mod 128), so O is the mean of the V
//       rows j = i mod 128); O exactly equal to the reference, LSE within 2^-20 relative.
//   T3  the rescale canary: `scale_log2` = 1, integer scores whose row maximum grows by 1 per key block, V in [0, 1];
//       every element |O - O_ref| <= 2^-15 · max|V|.
//   T4  on every run: no NaN or Inf in O or LSE (both start as NaN, so an element never written shows up), the guard
//       bands of sentinels around O and LSE untouched, and the three runs' O and LSE equal bit for bit.
// Throughput is printed, not judged: TFLOP/s at 4 · BH · seq² · 128 FLOPs, with the host's load average, since the
// time of a launch includes the launcher's host work (three tensor-map encodings), which dominates at small sizes.
#include <cuda_bf16.h>
#include <cuda_runtime.h>
#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <thread>
#include <vector>

extern "C" cudaError_t attention_launch(const __nv_bfloat16 *Q, const __nv_bfloat16 *K, const __nv_bfloat16 *V,
                                        float *O, float *LSE, unsigned BH, unsigned seq, float scale_log2,
                                        unsigned rows, unsigned dim, cudaStream_t stream);

#define CHECK(call)                                                                                                  \
  do {                                                                                                               \
    cudaError_t status_ = (call);                                                                                    \
    if (status_ != cudaSuccess) {                                                                                    \
      std::fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, cudaGetErrorString(status_));                          \
      std::exit(2);                                                                                                  \
    }                                                                                                                \
  } while (0)

static const unsigned dim = 128;

// x rounded to the nearest bf16, ties to even, as a float (x finite).
static float bf16(float x) {
  uint32_t u;
  std::memcpy(&u, &x, sizeof(u));
  u = (u + 0x7fffu + ((u >> 16) & 1u)) & 0xffff0000u;
  std::memcpy(&x, &u, sizeof(x));
  return x;
}

static uint32_t bits(float x) {
  uint32_t u;
  std::memcpy(&u, &x, sizeof(u));
  return u;
}

// Runs f(i) for i in [0, n) on every hardware thread.
template <class F> static void parallelFor(size_t n, F f) {
  const size_t workers = std::max(1u, std::thread::hardware_concurrency());
  std::vector<std::thread> pool;
  for (size_t w = 0; w < workers; ++w)
    pool.emplace_back([&f, n, w, workers]() {
      for (size_t i = w; i < n; i += workers) f(i);
    });
  for (std::thread &t : pool) t.join();
}

enum class Inputs { random, uniform, oneHot, rescale };

static const char *nameOf(Inputs kind) {
  switch (kind) {
  case Inputs::random: return "T1 random";
  case Inputs::uniform: return "T2 uniform (K = 0)";
  case Inputs::oneHot: return "T2 one-hot";
  case Inputs::rescale: return "T3 rescale";
  }
  return "?";
}

struct Problem {
  unsigned bh, seq;
  Inputs kind;
  float scaleLog2;
  std::vector<float> q, k, v;     // [BH·seq, 128], values exactly representable in bf16
  std::vector<float> oRef, lseRef;  // the reference, rounded to f32
  std::vector<float> maxV;          // max|V| per head
  // Sentinel floats on each side of O (128 rows, so a store a whole tile out of place lands in a guard) and of LSE.
  static constexpr size_t guardO = size_t(128) * dim, guardL = 1024;
  __nv_bfloat16 *dQ = nullptr, *dK = nullptr, *dV = nullptr;
  float *dOAlloc = nullptr, *dO = nullptr, *dLAlloc = nullptr, *dL = nullptr;
  std::vector<float> firstO, firstL;  // the first run's results, which the later runs must equal bit for bit

  size_t rows() const { return size_t(bh) * seq; }
  size_t totalO() const { return guardO + rows() * dim + guardO; }
  size_t totalL() const { return guardL + rows() + guardL; }

  Problem(unsigned bh, unsigned seq, Inputs kind, uint32_t seed)
      : bh(bh), seq(seq), kind(kind), q(rows() * dim), k(rows() * dim), v(rows() * dim), oRef(rows() * dim),
        lseRef(rows()), maxV(bh) {
    auto next = [&seed]() {
      seed = seed * 1664525u + 1013904223u;
      return float(seed >> 8) / float(1u << 24);  // in [0, 1)
    };
    auto in = [&next](float lo, float hi) { return bf16(lo + (hi - lo) * next()); };
    auto quarter = [&next]() { return float(int(next() * 9.0f) - 4) / 4.0f; };  // a multiple of 1/4 in [-1, 1]
    scaleLog2 = kind == Inputs::rescale ? 1.0f : float(std::log2(std::exp(1.0)) / std::sqrt(double(dim)));
    for (size_t r = 0; r < rows(); ++r) {
      const unsigned i = unsigned(r % seq);  // the row within its head
      for (unsigned d = 0; d < dim; ++d) {
        const size_t at = r * dim + d;
        switch (kind) {
        case Inputs::random:
          q[at] = i % 4 == 3 ? in(-8, 8) : in(-1, 1);
          k[at] = in(-1, 1);
          v[at] = in(-1, 1);
          break;
        case Inputs::uniform:
          q[at] = in(-1, 1);
          k[at] = 0;
          v[at] = quarter();
          break;
        case Inputs::oneHot:
          q[at] = d == i % 128 ? 2048.0f : 0.0f;
          k[at] = d == i % 128 ? 1.0f : 0.0f;
          v[at] = quarter();
          break;
        case Inputs::rescale: {
          // Score of query row i against key j: b - (j mod 4) - [i odd] · ((j mod 128) / 4 mod 3), for key block b
          // = j / 128. The block's first key scores b, every other at most b, so the row maximum is b in block b.
          q[at] = d == 0 || (d == 1 && i % 2 == 1) ? 1.0f : 0.0f;
          k[at] = d == 0 ? float(int(i / 128) - int(i % 4)) : d == 1 ? -float(i % 128 / 4 % 3) : 0.0f;
          v[at] = in(0, 1);
          break;
        }
        }
      }
    }
    for (unsigned h = 0; h < bh; ++h)
      for (size_t at = size_t(h) * seq * dim; at < size_t(h + 1) * seq * dim; ++at)
        maxV[h] = std::max(maxV[h], std::fabs(v[at]));
    reference();
    CHECK(cudaMalloc(&dQ, q.size() * sizeof(__nv_bfloat16)));
    CHECK(cudaMalloc(&dK, k.size() * sizeof(__nv_bfloat16)));
    CHECK(cudaMalloc(&dV, v.size() * sizeof(__nv_bfloat16)));
    CHECK(cudaMalloc(&dOAlloc, totalO() * sizeof(float)));
    CHECK(cudaMalloc(&dLAlloc, totalL() * sizeof(float)));
    dO = dOAlloc + guardO;
    dL = dLAlloc + guardL;
    upload(dQ, q);
    upload(dK, k);
    upload(dV, v);
  }
  ~Problem() {
    cudaFree(dQ);
    cudaFree(dK);
    cudaFree(dV);
    cudaFree(dOAlloc);
    cudaFree(dLAlloc);
  }

  static void upload(__nv_bfloat16 *dst, const std::vector<float> &src) {
    std::vector<__nv_bfloat16> host(src.size());
    for (size_t i = 0; i < src.size(); ++i) host[i] = __float2bfloat16(src[i]);
    CHECK(cudaMemcpy(dst, host.data(), host.size() * sizeof(__nv_bfloat16), cudaMemcpyHostToDevice));
  }

  // §1.2's first block, in double, per query row: t = c · Q·Kᵀ in log2 units, m its maximum, l = Σ 2^(t − m),
  // O = Σ 2^(t − m) · V / l, LSE = (m + log2 l) · ln 2.
  void reference() {
    parallelFor(rows(), [this](size_t r) {
      const size_t head = r / seq * seq;
      std::vector<double> t(seq);
      double m = -INFINITY;
      for (unsigned j = 0; j < seq; ++j) {
        double dot = 0;
        for (unsigned d = 0; d < dim; ++d) dot += double(q[r * dim + d]) * double(k[(head + j) * dim + d]);
        t[j] = double(scaleLog2) * dot;
        m = std::max(m, t[j]);
      }
      double l = 0;
      std::vector<double> o(dim, 0.0);
      for (unsigned j = 0; j < seq; ++j) {
        const double p = std::exp2(t[j] - m);
        l += p;
        for (unsigned d = 0; d < dim; ++d) o[d] += p * double(v[(head + j) * dim + d]);
      }
      for (unsigned d = 0; d < dim; ++d) oRef[r * dim + d] = float(o[d] / l);
      lseRef[r] = float((m + std::log2(l)) * std::log(2.0));
    });
  }

  cudaError_t launch() {
    return attention_launch(dQ, dK, dV, dO, dL, bh, seq, scaleLog2, unsigned(rows()), dim, nullptr);
  }

  // Runs once from NaN-filled O and LSE inside sentinel guard bands, and returns the number of failed checks: elements
  // outside their bound, NaN or Inf, guard values that changed, and elements that differ from the first run.
  size_t failures(int rep) {
    const size_t totalO = this->totalO(), totalL = this->totalL();
    CHECK(cudaMemset(dOAlloc, 0x7f, totalO * sizeof(float)));  // sentinel 0x7f7f7f7f, a finite float
    CHECK(cudaMemset(dLAlloc, 0x7f, totalL * sizeof(float)));
    CHECK(cudaMemset(dO, 0xff, rows() * dim * sizeof(float)));  // NaN
    CHECK(cudaMemset(dL, 0xff, rows() * sizeof(float)));
    CHECK(launch());
    CHECK(cudaDeviceSynchronize());
    std::vector<float> allO(totalO), allL(totalL);
    CHECK(cudaMemcpy(allO.data(), dOAlloc, totalO * sizeof(float), cudaMemcpyDeviceToHost));
    CHECK(cudaMemcpy(allL.data(), dLAlloc, totalL * sizeof(float), cudaMemcpyDeviceToHost));
    size_t bad = 0;
    auto report = [&bad](const std::string &what) {
      if (bad < 5) std::printf("    %s\n", what.c_str());
      ++bad;
    };
    auto guards = [&report](const std::vector<float> &all, size_t guard, const char *what) {
      for (size_t i = 0; i < all.size(); ++i)
        if ((i < guard || i >= all.size() - guard) && bits(all[i]) != 0x7f7f7f7fu)
          report(std::string("guard of ") + what + " written at " + std::to_string(ptrdiff_t(i) - ptrdiff_t(guard)));
    };
    guards(allO, guardO, "O");
    guards(allL, guardL, "LSE");
    const float *o = allO.data() + guardO, *lse = allL.data() + guardL;
    const bool exact = kind == Inputs::uniform || kind == Inputs::oneHot;
    double worstO = 0, worstL = 0;  // the largest error as a fraction of its bound (for exact O, the largest error)
    for (size_t r = 0; r < rows(); ++r) {
      const unsigned h = unsigned(r / seq), i = unsigned(r % seq);
      const double boundO = kind == Inputs::random ? std::ldexp(maxV[h], -7) : std::ldexp(maxV[h], -15);
      for (unsigned d = 0; d < dim; ++d) {
        const float got = o[r * dim + d], want = oRef[r * dim + d];
        const double err = std::fabs(double(got) - double(want));
        if (!std::isfinite(got)) {
          report("O[" + std::to_string(h) + "][" + std::to_string(i) + "][" + std::to_string(d) + "] = " +
                 std::to_string(got));
          continue;
        }
        if (exact ? !(got == want) : !(err <= boundO))
          report("O[" + std::to_string(h) + "][" + std::to_string(i) + "][" + std::to_string(d) + "] = " +
                 std::to_string(got) + ", want " + std::to_string(want));
        worstO = std::max(worstO, exact ? err : err / boundO);
      }
      const float got = lse[r], want = lseRef[r];
      const double err = std::fabs(double(got) - double(want));
      if (!std::isfinite(got)) {
        report("LSE[" + std::to_string(h) + "][" + std::to_string(i) + "] = " + std::to_string(got));
        continue;
      }
      if (kind == Inputs::rescale) continue;  // T3 bounds O only
      const double boundL = exact ? std::ldexp(std::fabs(double(want)), -20)
                                  : std::ldexp(1.0, -8) + std::ldexp(std::fabs(double(want)), -20);
      if (!(err <= boundL))
        report("LSE[" + std::to_string(h) + "][" + std::to_string(i) + "] = " + std::to_string(got) + ", want " +
               std::to_string(want));
      worstL = std::max(worstL, err / boundL);
    }
    std::vector<float> runO(o, o + rows() * dim), runL(lse, lse + rows());
    if (rep == 0) {
      firstO = runO;
      firstL = runL;
    } else {
      if (std::memcmp(runO.data(), firstO.data(), runO.size() * sizeof(float)) != 0) report("O differs from run 0");
      if (std::memcmp(runL.data(), firstL.data(), runL.size() * sizeof(float)) != 0) report("LSE differs from run 0");
    }
    if (rep == 0) {
      if (exact)
        std::printf("    largest O error %g; largest LSE error %.3g of its bound\n", worstO, worstL);
      else if (kind == Inputs::rescale)
        std::printf("    largest O error %.3g of its bound\n", worstO);
      else
        std::printf("    largest O error %.3g, LSE error %.3g of its bound\n", worstO, worstL);
    }
    return bad;
  }

  // The time of one launch, averaged over `reps` after a warm-up.
  float milliseconds(int reps) {
    CHECK(launch());
    CHECK(cudaDeviceSynchronize());
    cudaEvent_t start, stop;
    CHECK(cudaEventCreate(&start));
    CHECK(cudaEventCreate(&stop));
    CHECK(cudaEventRecord(start));
    for (int i = 0; i < reps; ++i) CHECK(launch());
    CHECK(cudaEventRecord(stop));
    CHECK(cudaEventSynchronize(stop));
    float ms = 0;
    CHECK(cudaEventElapsedTime(&ms, start, stop));
    cudaEventDestroy(start);
    cudaEventDestroy(stop);
    return ms / reps;
  }
};

int main() {
  int failures = 0;

  // Every `seq` is a power of two (T2's exactness needs it), at most 4096 (T3's bound); one and several key blocks,
  // and several heads, so a row or a key taken from the wrong head shows.
  const unsigned seqs[] = {128, 256, 1024, 4096};
  const unsigned heads[] = {1, 3, 16};
  const Inputs kinds[] = {Inputs::random, Inputs::uniform, Inputs::oneHot, Inputs::rescale};
  for (unsigned seq : seqs)
    for (unsigned bh : heads) {
      for (Inputs kind : kinds) {
        std::printf("%s, BH=%u seq=%u\n", nameOf(kind), bh, seq);
        Problem p(bh, seq, kind, seq * 7919u + bh * 104729u + unsigned(kind));
        size_t bad = 0;
        for (int rep = 0; rep < 3; ++rep) bad += p.failures(rep);
        std::printf("%s %s, BH=%u seq=%u%s\n", bad ? "FAIL" : "ok  ", nameOf(kind), bh, seq,
                    bad ? (" (" + std::to_string(bad) + " wrong)").c_str() : "");
        failures += bad != 0;
        if (kind == Inputs::random) {
          const float ms = p.milliseconds(10);
          const double flops = 4.0 * bh * double(seq) * seq * dim;
          double load = -1;
          getloadavg(&load, 1);
          std::printf("perf BH=%u seq=%u: %.3f ms, %.1f TFLOP/s (host load average %.2f)\n", bh, seq, ms,
                      flops / (ms * 1e-3) / 1e12, load);
        }
      }
    }

  // What the launcher must refuse rather than launch, each breaking one of its conditions: seq = 0, seq not a
  // multiple of 128, BH = 0, BH > 65535 (the grid's y), BH·seq·128 ≥ 2^31, rows ≠ BH·seq, and dim ≠ 128. Every call
  // gets the same small, valid buffers; a refused call must return cudaErrorInvalidValue and leave O and LSE as they
  // were. A call that is wrongly launched runs out of bounds: its failure is reported before the next CHECK ends the
  // run on the context's sticky error.
  {
    struct Refused {
      unsigned bh, seq, rows, dim;
      const char *why;
    };
    const Refused refused[] = {
        {1, 0, 0, 128, "seq = 0"},
        {1, 200, 200, 128, "seq = 200"},
        {0, 128, 0, 128, "BH = 0"},
        {65536, 128, 65536u * 128u, 128, "BH = 65536"},
        {16384, 1024, 16384u * 1024u, 128, "BH·seq·128 = 2^31"},
        {1, 128, 256, 128, "rows = 2·BH·seq"},
        {1, 128, 128, 64, "dim = 64"},
    };
    Problem p(1, 256, Inputs::random, 1);
    const size_t totalO = p.totalO(), totalL = p.totalL();
    for (const Refused &r : refused) {
      CHECK(cudaMemset(p.dOAlloc, 0x7f, totalO * sizeof(float)));
      CHECK(cudaMemset(p.dLAlloc, 0x7f, totalL * sizeof(float)));
      const cudaError_t status =
          attention_launch(p.dQ, p.dK, p.dV, p.dO, p.dL, r.bh, r.seq, p.scaleLog2, r.rows, r.dim, nullptr);
      std::vector<float> allO(totalO), allL(totalL);
      const bool copied =
          cudaDeviceSynchronize() == cudaSuccess &&
          cudaMemcpy(allO.data(), p.dOAlloc, totalO * sizeof(float), cudaMemcpyDeviceToHost) == cudaSuccess &&
          cudaMemcpy(allL.data(), p.dLAlloc, totalL * sizeof(float), cudaMemcpyDeviceToHost) == cudaSuccess;
      auto sentinel = [](float x) { return bits(x) == 0x7f7f7f7fu; };
      const bool untouched = copied && std::all_of(allO.begin(), allO.end(), sentinel) &&
                             std::all_of(allL.begin(), allL.end(), sentinel);
      const bool ok = status == cudaErrorInvalidValue && untouched;
      std::printf("%s %s refused: %s%s\n", ok ? "ok  " : "FAIL", r.why, cudaGetErrorString(status),
                  !copied ? ", and the device failed" : untouched ? "" : ", but O or LSE was written");
      failures += !ok;
    }
  }

  std::printf(failures ? "%d check(s) failed\n" : "all checks passed\n", failures);
  return failures ? 1 : 0;
}
