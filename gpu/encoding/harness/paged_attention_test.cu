// Runs a generated paged-attention kernel (gpu/encoding/PAGED.md, P1) against a CPU reference that gathers K and V
// through the block table, checks that it stays safe on a table of out-of-range pages, checks that its launcher refuses
// what the kernel cannot handle, and times it. Needs an sm_100a GPU:
//
//   gpu/gen.sh gpu/encoding/examples/paged_attention.rac > paged_attention.cu
//   nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a -o paged_attention_test paged_attention.cu \
//     gpu/encoding/harness/paged_attention_test.cu -lcuda
//   ./paged_attention_test
//
// The kernel's head count is a generation-time constant; the harness assumes the example's 8 (`-DHEADS=…` otherwise).
//
// The checks are gpu/ATTENTION.md §1.3's, over a paged cache whose pages are shuffled across the sequences: T1 (random
// inputs, against the reference within the stated bounds), T2 (the uniform and one-hot canaries, exact), T3 (the
// rescale canary) and T4 (no NaN or Inf, guard bands around O and LSE untouched, three runs bit for bit equal). Pages
// that no sequence uses hold NaN, so a load from a wrong page shows. O starts as NaN, so a row the kernel never writes
// shows too.
#include <cuda_bf16.h>
#include <cuda_runtime.h>
#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <functional>
#include <string>
#include <vector>

#ifndef PAGED_LAUNCH
#define PAGED_LAUNCH paged_attention_launch
#endif
#ifndef HEADS
#define HEADS 8
#endif

extern "C" cudaError_t PAGED_LAUNCH(const __nv_bfloat16 *Q, const __nv_bfloat16 *K, const __nv_bfloat16 *V, float *O,
                                    float *LSE, const unsigned *block_table, unsigned B, unsigned seq,
                                    unsigned max_pages, unsigned pages, unsigned rows_q, unsigned rows_kv, unsigned dim,
                                    float scale_log2, cudaStream_t stream);

#define CHECK(call)                                                                                                  \
  do {                                                                                                               \
    cudaError_t status_ = (call);                                                                                    \
    if (status_ != cudaSuccess) {                                                                                    \
      std::fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, cudaGetErrorString(status_));                          \
      std::exit(2);                                                                                                  \
    }                                                                                                                \
  } while (0)

static const unsigned H = HEADS;
static const unsigned D = 128;  // the head dimension, and the keys of a page

// `x` rounded to the nearest bf16, ties to even (finite `x` only).
static float bf16(float x) {
  uint32_t u;
  std::memcpy(&u, &x, sizeof(u));
  u += 0x7fffu + ((u >> 16) & 1u);
  u &= 0xffff0000u;
  std::memcpy(&x, &u, sizeof(x));
  return x;
}

// A deterministic stream of numbers.
struct Random {
  uint32_t state;
  uint32_t next() {
    state = state * 1664525u + 1013904223u;
    return state >> 8;
  }
  // Uniform in [lo, hi], rounded to bf16.
  float uniform(float lo, float hi) { return bf16(lo + (hi - lo) * float(next() % 65536u) / 65535.0f); }
  // A multiple of 1/4 in [-2, 2].
  float quarter() { return float(int(next() % 17u) - 8) / 4.0f; }
};

// Logical inputs: element `d` of query row `i`, or of key row `key`, of sequence `b`, head `h`.
using Element = std::function<float(unsigned b, unsigned h, unsigned row, unsigned d)>;

struct Problem {
  unsigned b, seq, maxPages, pages;
  float scaleLog2;
  std::vector<float> q, k, v;  // Q as [B·H·seq, 128]; K and V as the cache, [pages·H·128, 128]
  std::vector<unsigned> table;  // [B, maxPages]
  // Sentinel floats on both sides of O and of LSE.
  static constexpr size_t guard = 4096;
  __nv_bfloat16 *dQ = nullptr, *dK = nullptr, *dV = nullptr;
  unsigned *dTable = nullptr;
  float *dOAlloc = nullptr, *dLAlloc = nullptr, *dO = nullptr, *dLse = nullptr;

  size_t queryRows() const { return size_t(b) * H * seq; }
  size_t cacheRows() const { return size_t(pages) * H * D; }
  // The cache row holding element `key` of sequence `s`, head `h`, through the table.
  size_t cacheRow(unsigned s, unsigned h, unsigned key) const {
    return (size_t(table[size_t(s) * maxPages + key / D]) * H + h) * D + key % D;
  }

  // A problem whose sequences' pages are a shuffle of the cache's, with `spare` pages no sequence uses (NaN) and
  // `extra` columns of the table past the last block (an entry no load reads).
  Problem(unsigned b, unsigned seq, unsigned spare, unsigned extra, float scaleLog2, uint32_t seed, const Element &fq,
          const Element &fk, const Element &fv)
      : b(b), seq(seq), maxPages(seq / D + extra), pages(b * (seq / D) + spare), scaleLog2(scaleLog2),
        q(queryRows() * D), k(cacheRows() * D, NAN), v(cacheRows() * D, NAN), table(size_t(b) * maxPages, 0xdeadbeefu) {
    Random r{seed};
    std::vector<unsigned> perm(pages);
    for (unsigned p = 0; p < pages; ++p) perm[p] = p;
    for (unsigned p = pages; p > 1; --p) std::swap(perm[p - 1], perm[r.next() % p]);
    const unsigned blocks = seq / D;
    for (unsigned s = 0; s < b; ++s)
      for (unsigned j = 0; j < blocks; ++j) table[size_t(s) * maxPages + j] = perm[s * blocks + j];
    for (unsigned s = 0; s < b; ++s)
      for (unsigned h = 0; h < H; ++h)
        for (unsigned i = 0; i < seq; ++i)
          for (unsigned d = 0; d < D; ++d) {
            q[((size_t(s) * H + h) * seq + i) * D + d] = fq(s, h, i, d);
            k[cacheRow(s, h, i) * D + d] = fk(s, h, i, d);
            v[cacheRow(s, h, i) * D + d] = fv(s, h, i, d);
          }
    CHECK(cudaMalloc(&dQ, q.size() * sizeof(__nv_bfloat16)));
    CHECK(cudaMalloc(&dK, k.size() * sizeof(__nv_bfloat16)));
    CHECK(cudaMalloc(&dV, v.size() * sizeof(__nv_bfloat16)));
    CHECK(cudaMalloc(&dTable, table.size() * sizeof(unsigned)));
    CHECK(cudaMalloc(&dOAlloc, (2 * guard + queryRows() * D) * sizeof(float)));
    CHECK(cudaMalloc(&dLAlloc, (2 * guard + queryRows()) * sizeof(float)));
    dO = dOAlloc + guard;
    dLse = dLAlloc + guard;
    upload(dQ, q);
    upload(dK, k);
    upload(dV, v);
    uploadTable();
  }
  ~Problem() {
    cudaFree(dQ);
    cudaFree(dK);
    cudaFree(dV);
    cudaFree(dTable);
    cudaFree(dOAlloc);
    cudaFree(dLAlloc);
  }

  static void upload(__nv_bfloat16 *dst, const std::vector<float> &src) {
    std::vector<__nv_bfloat16> host(src.size());
    for (size_t i = 0; i < src.size(); ++i) host[i] = __float2bfloat16(src[i]);
    CHECK(cudaMemcpy(dst, host.data(), host.size() * sizeof(__nv_bfloat16), cudaMemcpyHostToDevice));
  }
  void uploadTable() {
    CHECK(cudaMemcpy(dTable, table.data(), table.size() * sizeof(unsigned), cudaMemcpyHostToDevice));
  }

  cudaError_t run() {
    return PAGED_LAUNCH(dQ, dK, dV, dO, dLse, dTable, b, seq, maxPages, pages, unsigned(queryRows()),
                        unsigned(cacheRows()), D, scaleLog2, nullptr);
  }

  // One run from NaN-filled O and LSE inside sentinel guard bands: O and LSE, and the number of guard elements written.
  struct Out {
    std::vector<float> o, lse;
    size_t guardsWritten = 0;
  };
  static size_t guardsWritten(const std::vector<float> &all, size_t inside) {
    size_t bad = 0;
    for (size_t i = 0; i < all.size(); ++i) {
      if (i >= guard && i < guard + inside) continue;
      uint32_t bits;
      std::memcpy(&bits, &all[i], sizeof(bits));
      bad += bits != 0x7f7f7f7fu;
    }
    return bad;
  }
  Out once() {
    const size_t oTotal = 2 * guard + queryRows() * D, lTotal = 2 * guard + queryRows();
    CHECK(cudaMemset(dOAlloc, 0x7f, oTotal * sizeof(float)));  // sentinel 0x7f7f7f7f, a finite float
    CHECK(cudaMemset(dLAlloc, 0x7f, lTotal * sizeof(float)));
    CHECK(cudaMemset(dO, 0xff, queryRows() * D * sizeof(float)));  // NaN
    CHECK(cudaMemset(dLse, 0xff, queryRows() * sizeof(float)));
    CHECK(run());
    CHECK(cudaDeviceSynchronize());
    std::vector<float> oAll(oTotal), lAll(lTotal);
    CHECK(cudaMemcpy(oAll.data(), dOAlloc, oTotal * sizeof(float), cudaMemcpyDeviceToHost));
    CHECK(cudaMemcpy(lAll.data(), dLAlloc, lTotal * sizeof(float), cudaMemcpyDeviceToHost));
    Out out;
    out.o.assign(oAll.begin() + guard, oAll.begin() + guard + queryRows() * D);
    out.lse.assign(lAll.begin() + guard, lAll.begin() + guard + queryRows());
    out.guardsWritten = guardsWritten(oAll, queryRows() * D) + guardsWritten(lAll, queryRows());
    return out;
  }

  // T4: three runs, each finite with its guards untouched, all three bit for bit equal. Returns the first run, and
  // adds the number of violations to `bad`.
  Out hygienic(size_t &bad) {
    Out first = once();
    for (int rep = 0; rep < 3; ++rep) {
      Out again = rep == 0 ? first : once();
      bad += again.guardsWritten;
      for (float x : again.o) bad += !std::isfinite(x);
      for (float x : again.lse) bad += !std::isfinite(x);
      bad += std::memcmp(again.o.data(), first.o.data(), first.o.size() * sizeof(float)) != 0;
      bad += std::memcmp(again.lse.data(), first.lse.data(), first.lse.size() * sizeof(float)) != 0;
    }
    if (bad) std::printf("    T4: %zu violation(s)\n", bad);
    return first;
  }

  // The reference in double for query row `i` of sequence `s`, head `h` (ATTENTION.md §1.2), from the cache through
  // the table: its LSE, and its O into `o`.
  double reference(unsigned s, unsigned h, unsigned i, double *o) const {
    const double scale = double(scaleLog2) * std::log(2.0);
    const float *qi = &q[((size_t(s) * H + h) * seq + i) * D];
    std::vector<double> sc(seq);
    double mx = -INFINITY;
    for (unsigned key = 0; key < seq; ++key) {
      const float *kj = &k[cacheRow(s, h, key) * D];
      double dot = 0;
      for (unsigned d = 0; d < D; ++d) dot += double(qi[d]) * double(kj[d]);
      sc[key] = scale * dot;
      mx = std::max(mx, sc[key]);
    }
    double sum = 0;
    for (unsigned key = 0; key < seq; ++key) sum += std::exp(sc[key] - mx);
    const double lse = mx + std::log(sum);
    for (unsigned d = 0; d < D; ++d) o[d] = 0;
    for (unsigned key = 0; key < seq; ++key) {
      const double p = std::exp(sc[key] - lse);
      const float *vj = &v[cacheRow(s, h, key) * D];
      for (unsigned d = 0; d < D; ++d) o[d] += p * double(vj[d]);
    }
    return lse;
  }

  // The largest |V| over the sequences' pages.
  double maxV() const {
    double m = 0;
    for (unsigned s = 0; s < b; ++s)
      for (unsigned h = 0; h < H; ++h)
        for (unsigned key = 0; key < seq; ++key)
          for (unsigned d = 0; d < D; ++d) m = std::max(m, std::fabs(double(v[cacheRow(s, h, key) * D + d])));
    return m;
  }

  // Compares `out` with the reference: |O − O_ref| ≤ oBound (or O equal to the f32-rounded reference when `exact`),
  // and |LSE − LSE_ref| ≤ lseAbs + lseRel·|LSE_ref|. Returns the number of elements outside.
  size_t compare(const Out &out, bool exact, double oBound, double lseAbs, double lseRel) const {
    size_t bad = 0;
    std::vector<double> o(D);
    for (unsigned s = 0; s < b; ++s)
      for (unsigned h = 0; h < H; ++h)
        for (unsigned i = 0; i < seq; ++i) {
          const size_t row = (size_t(s) * H + h) * seq + i;
          const double lse = reference(s, h, i, o.data());
          if (!(std::fabs(double(out.lse[row]) - lse) <= lseAbs + lseRel * std::fabs(lse))) {
            if (bad < 5) std::printf("    LSE[b=%u h=%u i=%u] = %.9g, want %.9g\n", s, h, i, out.lse[row], lse);
            ++bad;
          }
          for (unsigned d = 0; d < D; ++d) {
            const float got = out.o[row * D + d];
            const bool ok = exact ? got == float(o[d]) : std::fabs(double(got) - o[d]) <= oBound;
            if (!ok) {
              if (bad < 5) std::printf("    O[b=%u h=%u i=%u][%u] = %.9g, want %.9g\n", s, h, i, d, got, o[d]);
              ++bad;
            }
          }
        }
    return bad;
  }
};

static const float log2e = 1.4426950408889634f;
static const float scaleLog2 = log2e / std::sqrt(128.0f);  // scale · log2(e), scale = 1/√128

static int report(const char *what, unsigned b, unsigned seq, size_t bad) {
  std::printf("%s %s B=%u seq=%u%s\n", bad ? "FAIL" : "ok  ", what, b, seq,
              bad ? (" (" + std::to_string(bad) + " wrong)").c_str() : "");
  return bad != 0;
}

// T1: random bf16 inputs, Q in [−1, 1] with every 16th row peaked in [−8, 8], K and V in [−1, 1].
static int t1(unsigned b, unsigned seq, unsigned spare, unsigned extra) {
  Random r{b * 7919u + seq};
  auto fq = [&r](unsigned, unsigned, unsigned i, unsigned) { return i % 16 == 0 ? r.uniform(-8, 8) : r.uniform(-1, 1); };
  auto fkv = [&r](unsigned, unsigned, unsigned, unsigned) { return r.uniform(-1, 1); };
  Problem p(b, seq, spare, extra, scaleLog2, seq * 31u + b, fq, fkv, fkv);
  size_t bad = 0;
  Problem::Out out = p.hygienic(bad);
  bad += p.compare(out, false, std::ldexp(1.0, -7) * p.maxV(), std::ldexp(1.0, -8), std::ldexp(1.0, -20));
  return report("T1", b, seq, bad);
}

// T2, uniform: K = 0, so every score is 0 and O is the column mean of V, exact for multiples of 1/4 and `seq` a power
// of two.
static int t2Uniform(unsigned b, unsigned seq) {
  Random r{seq + 17u};
  auto fq = [&r](unsigned, unsigned, unsigned, unsigned) { return r.uniform(-1, 1); };
  auto fk = [](unsigned, unsigned, unsigned, unsigned) { return 0.0f; };
  auto fv = [&r](unsigned, unsigned, unsigned, unsigned) { return r.quarter(); };
  Problem p(b, seq, 3, 1, scaleLog2, seq * 37u + b, fq, fk, fv);
  size_t bad = 0;
  Problem::Out out = p.hygienic(bad);
  bad += p.compare(out, true, 0, 0, std::ldexp(1.0, -20));
  return report("T2 uniform", b, seq, bad);
}

// T2, one-hot: Q row i is 2048·e_{i mod 128} and K row j is e_{j mod 128}, so P is an identity per block and O the mean
// of the matched V rows, exactly.
static int t2OneHot(unsigned b, unsigned seq) {
  Random r{seq + 29u};
  auto fq = [](unsigned, unsigned, unsigned i, unsigned d) { return d == i % D ? 2048.0f : 0.0f; };
  auto fk = [](unsigned, unsigned, unsigned j, unsigned d) { return d == j % D ? 1.0f : 0.0f; };
  auto fv = [&r](unsigned, unsigned, unsigned, unsigned) { return r.quarter(); };
  Problem p(b, seq, 2, 0, scaleLog2, seq * 41u + b, fq, fk, fv);
  size_t bad = 0;
  Problem::Out out = p.hygienic(bad);
  bad += p.compare(out, true, 0, 0, std::ldexp(1.0, -20));
  return report("T2 one-hot", b, seq, bad);
}

// T3: `scale_log2` = 1 and integer scores (Q row e_0, K's first column an integer) whose row maximum grows by 1 per
// key block, V in [0, 1].
static int t3(unsigned b, unsigned seq) {
  Random r{seq + 43u};
  auto fq = [](unsigned, unsigned, unsigned, unsigned d) { return d == 0 ? 1.0f : 0.0f; };
  auto fk = [](unsigned, unsigned h, unsigned j, unsigned d) {
    return d == 0 ? float(int(j / D) - int((j * 7 + h) % 4)) : 0.0f;
  };
  auto fv = [&r](unsigned, unsigned, unsigned, unsigned) { return float(r.next() % 9u) / 8.0f; };
  Problem p(b, seq, 1, 2, 1.0f, seq * 43u + b, fq, fk, fv);
  size_t bad = 0;
  Problem::Out out = p.hygienic(bad);
  bad += p.compare(out, false, std::ldexp(1.0, -15) * p.maxV(), std::ldexp(1.0, -8), std::ldexp(1.0, -20));
  return report("T3", b, seq, bad);
}

// A table of pages outside the cache. Sequence 0's entries all address rows outside it: past its end, or negative as
// TMA's signed coordinates (the page row wraps modulo 2^32), so its K and V read as zeros, every score is 0, and O must
// be exactly 0 and LSE ln(seq). The other sequences mix valid pages with ones past the end, ones whose row wraps
// negative and ones whose row wraps back into the cache: their results are garbage, which must only be finite. In every
// case nothing may fault, and nothing outside O and LSE may be written.
static int outOfRange(unsigned b, unsigned seq) {
  Random r{seq + 47u};
  auto fq = [&r](unsigned, unsigned, unsigned, unsigned) { return r.uniform(-1, 1); };
  auto fkv = [&r](unsigned, unsigned, unsigned, unsigned) { return r.uniform(-1, 1); };
  // No spare pages: a wild entry that lands on a valid page must find finite data there.
  Problem p(b, seq, 0, 3, scaleLog2, seq * 53u + b, fq, fkv, fkv);
  const unsigned negative = (1u << 31) / (H * D);  // its row is about 2^31: negative as a signed coordinate
  const unsigned outside[] = {p.pages, p.pages + 5, 0xffffffffu, negative, 0xdeadbeefu};
  const unsigned wild[] = {p.pages, 0xffffffffu, negative, 2 * negative, 0x7fffffffu, 0x80000000u, 1u, 0u};
  for (unsigned s = 0; s < b; ++s)
    for (unsigned j = 0; j < p.maxPages; ++j) {
      unsigned &entry = p.table[size_t(s) * p.maxPages + j];
      if (s == 0) entry = outside[r.next() % 5];
      else if (r.next() % 2) entry = wild[r.next() % 8];
    }
  p.uploadTable();
  size_t bad = 0;
  Problem::Out out = p.hygienic(bad);
  const double lse = std::log(double(seq));
  for (unsigned h = 0; h < H; ++h)
    for (unsigned i = 0; i < seq; ++i) {
      const size_t row = size_t(h) * seq + i;
      bad += !(std::fabs(double(out.lse[row]) - lse) <= std::ldexp(1.0, -20) * lse);
      for (unsigned d = 0; d < D; ++d) bad += out.o[row * D + d] != 0.0f;
    }
  return report("out-of-range table", b, seq, bad);
}

int main() {
  int failures = 0;

  // Several sequences, sequences of one block, tables wider than needed, and spare pages.
  failures += t1(2, 256, 3, 2);
  failures += t1(3, 384, 1, 0);
  failures += t1(1, 1024, 4, 1);
  failures += t1(5, 128, 2, 3);
  failures += t2Uniform(2, 256);
  failures += t2Uniform(1, 512);
  failures += t2OneHot(2, 512);
  failures += t2OneHot(3, 128);
  failures += t3(1, 1024);
  failures += t3(2, 512);
  failures += outOfRange(3, 512);

  // What the launcher must refuse rather than launch, one requirement broken each: {B, seq, max_pages, pages, rows_q,
  // rows_kv, dim}, with the refusal reported before any memory is touched (the arrays are a small valid problem's).
  {
    auto zero = [](unsigned, unsigned, unsigned, unsigned) { return 0.0f; };
    Problem p(1, 128, 0, 0, scaleLog2, 1, zero, zero, zero);
    const unsigned kv = H * D;  // rows_kv of one page
    const unsigned bigB = 65536 / H;
    const unsigned bigSeq = ((1u << 31) / (H * D) + D - 1) / D * D;
    const unsigned bigPages = (1u << 31) / (H * D);
    struct Case {
      const char *what;
      unsigned b, seq, maxPages, pages, rowsQ, rowsKv, dim;
    } refused[] = {
        {"seq = 0", 1, 0, 1, 1, 0, kv, 128},
        {"seq not a multiple of 128", 1, 200, 2, 1, H * 200, kv, 128},
        {"B = 0", 0, 128, 1, 1, 0, kv, 128},
        {"B·H > 65535", bigB, 128, 1, 1, bigB * H * 128, kv, 128},
        {"B·H·seq·128 ≥ 2^31", 1, bigSeq, bigSeq / D, 1, H * bigSeq, kv, 128},
        {"rows_q ≠ B·H·seq", 1, 128, 1, 1, H * 128 + 128, kv, 128},
        {"pages·H·128 ≥ 2^31", 1, 128, 1, bigPages, H * 128, bigPages * kv, 128},
        {"rows_kv ≠ pages·H·128", 1, 128, 1, 2, H * 128, kv, 128},
        {"dim ≠ 128", 1, 128, 1, 1, H * 128, kv, 64},
        {"max_pages < seq/128", 1, 256, 1, 2, H * 256, 2 * kv, 128},
        {"B·max_pages ≥ 2^31", 1, 128, 1u << 31, 1, H * 128, kv, 128},
    };
    for (const Case &c : refused) {
      cudaError_t status = PAGED_LAUNCH(p.dQ, p.dK, p.dV, p.dO, p.dLse, p.dTable, c.b, c.seq, c.maxPages, c.pages, c.rowsQ,
                                        c.rowsKv, c.dim, scaleLog2, nullptr);
      std::printf("%s refused %s: %s\n", status != cudaSuccess ? "ok  " : "FAIL", c.what, cudaGetErrorString(status));
      failures += status == cudaSuccess;
    }
  }

  // Throughput on a long prefill.
  {
    const unsigned b = 4, seq = 4096;
    auto fq = [](unsigned, unsigned, unsigned i, unsigned d) { return float(int((i * 3 + d) % 17) - 8) / 64.0f; };
    Problem p(b, seq, 0, 0, scaleLog2, 42, fq, fq, fq);
    CHECK(p.run());
    CHECK(cudaDeviceSynchronize());
    cudaEvent_t start, stop;
    CHECK(cudaEventCreate(&start));
    CHECK(cudaEventCreate(&stop));
    const int reps = 10;
    CHECK(cudaEventRecord(start));
    for (int i = 0; i < reps; ++i) CHECK(p.run());
    CHECK(cudaEventRecord(stop));
    CHECK(cudaEventSynchronize(stop));
    float ms = 0;
    CHECK(cudaEventElapsedTime(&ms, start, stop));
    const double tflops = 4.0 * b * H * double(seq) * seq * D * reps / (ms * 1e-3) / 1e12;
    std::printf("perf B=%u H=%u seq=%u: %.3f ms per launch, %.1f TFLOP/s\n", b, H, seq, ms / reps, tflops);
    cudaEventDestroy(start);
    cudaEventDestroy(stop);
  }

  std::printf(failures ? "%d check(s) failed\n" : "all checks passed\n", failures);
  return failures ? 1 : 0;
}
