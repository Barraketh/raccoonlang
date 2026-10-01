// Runs the generated paged-attention kernels (gpu/encoding/PAGED.md, with ATTENTION.md's A2 masks and tails) against a
// CPU reference that gathers K and V through the block table, checks that they stay safe on a table of out-of-range
// pages, checks that their launchers refuse what the kernels cannot handle, and times them. Needs an sm_100a GPU:
//
//   gpu/gen.sh gpu/encoding/examples/paged_attention.rac > paged_attention.cu
//   nvcc -std=c++17 -O2 -Xcompiler -pthread -gencode arch=compute_100a,code=sm_100a -o paged_attention_test \
//     paged_attention.cu gpu/encoding/harness/paged_attention_test.cu -lcuda
//   ./paged_attention_test
//
// The example generates two kernels: `paged_attention`, non-causal with O in f32, and `paged_attention_causal`, causal
// within each sequence (query i sees keys j ≤ i) with O in bf16; both run every check. Their head count is a
// generation-time constant; the harness assumes the example's 8 (`-DHEADS=…` otherwise).
//
// The cache is `[pages·128, H·128]`: page `p` holds positions 128p to 128p + 127 of every head (encoding/P2.md §1).
// The checks are gpu/ATTENTION.md §1.3's, over a paged cache whose pages are shuffled across the sequences: T1 (random
// inputs, against the reference within the stated bounds), T2 (the uniform and one-hot canaries: exact for the
// non-causal kernel at `seq` a power of two, else within 2^-21 · max|V|), T3 (the rescale canary) and T4 (no NaN or
// Inf, guard bands around O and LSE untouched, three runs bit for bit equal); with bf16 output every bound on O gains
// bf16's rounding of the result, 2^-8 · (|O_ref| + the bound). Pages that no sequence uses hold NaN, so a load from a wrong page
// shows. A sequence's last page is partly used when 128 does not divide `seq`: its unused rows hold large finite
// values (±2^60) in K and V, so a key the mask lets through shows, while a masked one (p = 0) contributes exactly 0.
// O starts as NaN, so a row the kernel never writes shows too.
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
#include <thread>
#include <vector>

#ifndef HEADS
#define HEADS 8
#endif

extern "C" cudaError_t paged_attention_launch(const __nv_bfloat16 *Q, const __nv_bfloat16 *K, const __nv_bfloat16 *V,
                                              float *O, float *LSE, const unsigned *block_table, unsigned B,
                                              unsigned seq, unsigned max_pages, unsigned pages, unsigned rows_q,
                                              unsigned rows_kv, unsigned cols_kv, unsigned dim, float scale_log2,
                                              cudaStream_t stream);
extern "C" cudaError_t paged_attention_causal_launch(const __nv_bfloat16 *Q, const __nv_bfloat16 *K,
                                                     const __nv_bfloat16 *V, __nv_bfloat16 *O, float *LSE,
                                                     const unsigned *block_table, unsigned B, unsigned seq,
                                                     unsigned max_pages, unsigned pages, unsigned rows_q,
                                                     unsigned rows_kv, unsigned cols_kv, unsigned dim, float scale_log2,
                                                     cudaStream_t stream);

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

// The float a bf16 element's two bytes at `p` hold.
static float fromBf16(const unsigned char *p) {
  uint16_t h;
  std::memcpy(&h, p, sizeof(h));
  const uint32_t u = uint32_t(h) << 16;
  float x;
  std::memcpy(&x, &u, sizeof(x));
  return x;
}

static bool powerOfTwo(unsigned n) { return n != 0 && (n & (n - 1)) == 0; }

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

// A generated kernel: causal or not, and the element type of its O (f32, or bf16 when `bf16Out`).
struct Kernel {
  const char *name;
  bool causal, bf16Out;
};

static const Kernel kernels[] = {{"paged_attention", false, false}, {"paged_attention_causal", true, true}};

// One launch of `kernel` on device arrays; O is an f32 or a bf16 array, as the kernel writes.
static cudaError_t launch(const Kernel &kernel, const __nv_bfloat16 *q, const __nv_bfloat16 *k, const __nv_bfloat16 *v,
                          void *o, float *lse, const unsigned *table, unsigned b, unsigned seq, unsigned maxPages,
                          unsigned pages, unsigned rowsQ, unsigned rowsKv, unsigned colsKv, unsigned d,
                          float scaleLog2) {
  if (kernel.bf16Out)
    return paged_attention_causal_launch(q, k, v, static_cast<__nv_bfloat16 *>(o), lse, table, b, seq, maxPages, pages,
                                         rowsQ, rowsKv, colsKv, d, scaleLog2, nullptr);
  return paged_attention_launch(q, k, v, static_cast<float *>(o), lse, table, b, seq, maxPages, pages, rowsQ, rowsKv,
                                colsKv, d, scaleLog2, nullptr);
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
  const Kernel &kernel;
  unsigned b, seq, blocks, maxPages, pages;
  float scaleLog2;
  std::vector<float> q, k, v;  // Q as [B·H·seq, 128]; K and V as the cache, [pages·128, H·128]
  std::vector<unsigned> table;  // [B, maxPages]
  // Sentinel bytes (0x7f) on both sides of O, and sentinel floats on both sides of LSE: 128 rows of f32 O, so that the
  // rows of a last query tile past `seq`, stored by mistake past the last head, land in the guard.
  static constexpr size_t guard = size_t(128) * D * sizeof(float);
  __nv_bfloat16 *dQ = nullptr, *dK = nullptr, *dV = nullptr;
  unsigned *dTable = nullptr;
  unsigned char *dOAlloc = nullptr, *dO = nullptr;
  float *dLAlloc = nullptr, *dLse = nullptr;

  size_t queryRows() const { return size_t(b) * H * seq; }
  size_t cacheRows() const { return size_t(pages) * D; }
  size_t elementBytes() const { return kernel.bf16Out ? 2 : 4; }
  size_t bytesO() const { return queryRows() * D * elementBytes(); }
  // Where the cache holds key `key` of sequence `s`, head `h`, through the table: its first element, in row
  // `128p + key % 128` of page `p`, columns `128h` on.
  size_t cacheAt(unsigned s, unsigned h, unsigned key) const {
    return (size_t(table[size_t(s) * maxPages + key / D]) * D + key % D) * H * D + size_t(h) * D;
  }
  // The keys query row i of a sequence sees: j < seq, and j ≤ i when causal.
  unsigned keys(unsigned i) const { return kernel.causal ? i + 1 : seq; }

  // A problem whose sequences' pages are a shuffle of the cache's, with `spare` pages no sequence uses (NaN) and
  // `extra` columns of the table past the last block (an entry no load reads). The rows of a last page past `seq`
  // hold ±2^60.
  Problem(const Kernel &kernel, unsigned b, unsigned seq, unsigned spare, unsigned extra, float scaleLog2, uint32_t seed,
          const Element &fq, const Element &fk, const Element &fv)
      : kernel(kernel), b(b), seq(seq), blocks((seq + D - 1) / D), maxPages(blocks + extra), pages(b * blocks + spare),
        scaleLog2(scaleLog2), q(queryRows() * D), k(cacheRows() * H * D, NAN), v(cacheRows() * H * D, NAN),
        table(size_t(b) * maxPages, 0xdeadbeefu) {
    Random r{seed};
    std::vector<unsigned> perm(pages);
    for (unsigned p = 0; p < pages; ++p) perm[p] = p;
    for (unsigned p = pages; p > 1; --p) std::swap(perm[p - 1], perm[r.next() % p]);
    for (unsigned s = 0; s < b; ++s)
      for (unsigned j = 0; j < blocks; ++j) table[size_t(s) * maxPages + j] = perm[s * blocks + j];
    for (unsigned s = 0; s < b; ++s)
      for (unsigned h = 0; h < H; ++h) {
        for (unsigned i = 0; i < seq; ++i)
          for (unsigned d = 0; d < D; ++d) {
            q[((size_t(s) * H + h) * seq + i) * D + d] = fq(s, h, i, d);
            k[cacheAt(s, h, i) + d] = fk(s, h, i, d);
            v[cacheAt(s, h, i) + d] = fv(s, h, i, d);
          }
        for (unsigned i = seq; i < blocks * D; ++i)
          for (unsigned d = 0; d < D; ++d) {
            const float big = (r.next() % 2 ? 1.0f : -1.0f) * std::ldexp(1.0f, 60);
            k[cacheAt(s, h, i) + d] = big;
            v[cacheAt(s, h, i) + d] = -big;
          }
      }
    CHECK(cudaMalloc(&dQ, q.size() * sizeof(__nv_bfloat16)));
    CHECK(cudaMalloc(&dK, k.size() * sizeof(__nv_bfloat16)));
    CHECK(cudaMalloc(&dV, v.size() * sizeof(__nv_bfloat16)));
    CHECK(cudaMalloc(&dTable, table.size() * sizeof(unsigned)));
    CHECK(cudaMalloc(&dOAlloc, 2 * guard + bytesO()));
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
    return launch(kernel, dQ, dK, dV, dO, dLse, dTable, b, seq, maxPages, pages, unsigned(queryRows()),
                  unsigned(cacheRows()), H * D, D, scaleLog2);
  }

  // One run from NaN-filled O and LSE inside sentinel guard bands: O (as floats) and LSE, and the number of guard bytes
  // written.
  struct Out {
    std::vector<float> o, lse;
    size_t guardsWritten = 0;
  };
  Out once() {
    const size_t oTotal = 2 * guard + bytesO(), lTotal = (2 * guard + queryRows()) * sizeof(float);
    CHECK(cudaMemset(dOAlloc, 0x7f, oTotal));  // sentinel bytes: 0x7f7f7f7f and 0x7f7f are finite
    CHECK(cudaMemset(dLAlloc, 0x7f, lTotal));
    CHECK(cudaMemset(dO, 0xff, bytesO()));  // NaN, in f32 and in bf16
    CHECK(cudaMemset(dLse, 0xff, queryRows() * sizeof(float)));
    CHECK(run());
    CHECK(cudaDeviceSynchronize());
    std::vector<unsigned char> oAll(oTotal), lAll(lTotal);
    CHECK(cudaMemcpy(oAll.data(), dOAlloc, oTotal, cudaMemcpyDeviceToHost));
    CHECK(cudaMemcpy(lAll.data(), dLAlloc, lTotal, cudaMemcpyDeviceToHost));
    Out out;
    out.o.resize(queryRows() * D);
    for (size_t i = 0; i < out.o.size(); ++i) {
      const unsigned char *at = oAll.data() + guard + i * elementBytes();
      if (kernel.bf16Out) out.o[i] = fromBf16(at);
      else std::memcpy(&out.o[i], at, sizeof(float));
    }
    out.lse.resize(queryRows());
    std::memcpy(out.lse.data(), lAll.data() + guard * sizeof(float), queryRows() * sizeof(float));
    for (size_t i = 0; i < oTotal; ++i) out.guardsWritten += (i < guard || i >= guard + bytesO()) && oAll[i] != 0x7f;
    for (size_t i = 0; i < lTotal; ++i)
      out.guardsWritten += (i < guard * sizeof(float) || i >= (guard + queryRows()) * sizeof(float)) && lAll[i] != 0x7f;
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

  // The reference in double for query row `i` of sequence `s`, head `h`, as §1.2's first block writes it, from the
  // cache through the table, over the keys the row sees: t = c · Q·Kᵀ in log2 units, m its maximum,
  // l = Σ 2^(t − m), O = Σ 2^(t − m) · V / l into `o`, and LSE = (m + log2 l) · ln 2, returned. (Dividing by l,
  // rather than weighting by 2^(t − LSE), keeps a canary's mean exact: its p are exactly 1.)
  double reference(unsigned s, unsigned h, unsigned i, double *o) const {
    const float *qi = &q[((size_t(s) * H + h) * seq + i) * D];
    const unsigned n = keys(i);
    std::vector<double> t(n);
    double m = -INFINITY;
    for (unsigned key = 0; key < n; ++key) {
      const float *kj = &k[cacheAt(s, h, key)];
      double dot = 0;
      for (unsigned d = 0; d < D; ++d) dot += double(qi[d]) * double(kj[d]);
      t[key] = double(scaleLog2) * dot;
      m = std::max(m, t[key]);
    }
    double l = 0;
    for (unsigned d = 0; d < D; ++d) o[d] = 0;
    for (unsigned key = 0; key < n; ++key) {
      const double p = std::exp2(t[key] - m);
      l += p;
      const float *vj = &v[cacheAt(s, h, key)];
      for (unsigned d = 0; d < D; ++d) o[d] += p * double(vj[d]);
    }
    for (unsigned d = 0; d < D; ++d) o[d] /= l;
    return (m + std::log2(l)) * std::log(2.0);
  }

  // The largest |V| over the sequences' keys.
  double maxV() const {
    double m = 0;
    for (unsigned s = 0; s < b; ++s)
      for (unsigned h = 0; h < H; ++h)
        for (unsigned key = 0; key < seq; ++key)
          for (unsigned d = 0; d < D; ++d) m = std::max(m, std::fabs(double(v[cacheAt(s, h, key) + d])));
    return m;
  }

  // Compares `out` with the reference: |O − O_ref| ≤ oBound, plus 2^-8·(|O_ref| + oBound) for bf16 output (or O
  // equal to the f32-rounded reference when `exact`), and |LSE − LSE_ref| ≤ lseAbs + lseRel·|LSE_ref|. Returns the
  // number of elements outside.
  size_t compare(const Out &out, bool exact, double oBound, double lseAbs, double lseRel) const {
    std::vector<double> oRef(queryRows() * D), lseRef(queryRows());
    parallelFor(queryRows(), [&](size_t row) {
      const unsigned i = unsigned(row % seq), h = unsigned(row / seq % H), s = unsigned(row / seq / H);
      lseRef[row] = reference(s, h, i, &oRef[row * D]);
    });
    size_t bad = 0;
    for (size_t row = 0; row < queryRows(); ++row) {
      const unsigned i = unsigned(row % seq), h = unsigned(row / seq % H), s = unsigned(row / seq / H);
      const double lse = lseRef[row];
      if (!(std::fabs(double(out.lse[row]) - lse) <= lseAbs + lseRel * std::fabs(lse))) {
        if (bad < 5) std::printf("    LSE[b=%u h=%u i=%u] = %.9g, want %.9g\n", s, h, i, out.lse[row], lse);
        ++bad;
      }
      for (unsigned d = 0; d < D; ++d) {
        const float got = out.o[row * D + d];
        const double want = oRef[row * D + d];
        const double bound = kernel.bf16Out ? oBound + std::ldexp(oBound + std::fabs(want), -8) : oBound;
        const bool ok = exact ? got == float(want) : std::fabs(double(got) - want) <= bound;
        if (!ok) {
          if (bad < 5) std::printf("    O[b=%u h=%u i=%u][%u] = %.9g, want %.9g\n", s, h, i, d, got, want);
          ++bad;
        }
      }
    }
    return bad;
  }
};

static const float log2e = 1.4426950408889634f;
static const float scaleLog2 = log2e / std::sqrt(128.0f);  // scale · log2(e), scale = 1/√128

static int report(const Kernel &kernel, const char *what, unsigned b, unsigned seq, size_t bad) {
  std::printf("%s %s %s B=%u seq=%u%s\n", bad ? "FAIL" : "ok  ", kernel.name, what, b, seq,
              bad ? (" (" + std::to_string(bad) + " wrong)").c_str() : "");
  return bad != 0;
}

// T1: random bf16 inputs, Q in [−1, 1] with every 16th row peaked in [−8, 8], K and V in [−1, 1].
static int t1(const Kernel &kernel, unsigned b, unsigned seq, unsigned spare, unsigned extra) {
  Random r{b * 7919u + seq};
  auto fq = [&r](unsigned, unsigned, unsigned i, unsigned) { return i % 16 == 0 ? r.uniform(-8, 8) : r.uniform(-1, 1); };
  auto fkv = [&r](unsigned, unsigned, unsigned, unsigned) { return r.uniform(-1, 1); };
  Problem p(kernel, b, seq, spare, extra, scaleLog2, seq * 31u + b, fq, fkv, fkv);
  size_t bad = 0;
  Problem::Out out = p.hygienic(bad);
  bad += p.compare(out, false, std::ldexp(1.0, -7) * p.maxV(), std::ldexp(1.0, -8), std::ldexp(1.0, -20));
  return report(kernel, "T1", b, seq, bad);
}

// The canaries' bounds: exact O for the non-causal f32 kernel at `seq` a power of two, where every intermediate is;
// otherwise a row's count of keys need not be a power of two, and its 1/l is rounded.
static size_t canaryCompare(const Problem &p, const Problem::Out &out) {
  const bool exact = !p.kernel.causal && !p.kernel.bf16Out && powerOfTwo(p.seq);
  return p.compare(out, exact, std::ldexp(1.0, -21) * p.maxV(), std::ldexp(1.0, -22), std::ldexp(1.0, -20));
}

// T2, uniform: K = 0, so every score a row sees is 0 and O is the mean of the V rows it sees.
static int t2Uniform(const Kernel &kernel, unsigned b, unsigned seq) {
  Random r{seq + 17u};
  auto fq = [&r](unsigned, unsigned, unsigned, unsigned) { return r.uniform(-1, 1); };
  auto fk = [](unsigned, unsigned, unsigned, unsigned) { return 0.0f; };
  auto fv = [&r](unsigned, unsigned, unsigned, unsigned) { return r.quarter(); };
  Problem p(kernel, b, seq, 3, 1, scaleLog2, seq * 37u + b, fq, fk, fv);
  size_t bad = 0;
  Problem::Out out = p.hygienic(bad);
  bad += canaryCompare(p, out);
  return report(kernel, "T2 uniform", b, seq, bad);
}

// T2, one-hot: Q row i is 2048·e_{i mod 128} and K row j is e_{j mod 128}, so P is an identity per block and O the mean
// of the matched V rows a row sees.
static int t2OneHot(const Kernel &kernel, unsigned b, unsigned seq) {
  Random r{seq + 29u};
  auto fq = [](unsigned, unsigned, unsigned i, unsigned d) { return d == i % D ? 2048.0f : 0.0f; };
  auto fk = [](unsigned, unsigned, unsigned j, unsigned d) { return d == j % D ? 1.0f : 0.0f; };
  auto fv = [&r](unsigned, unsigned, unsigned, unsigned) { return r.quarter(); };
  Problem p(kernel, b, seq, 2, 0, scaleLog2, seq * 41u + b, fq, fk, fv);
  size_t bad = 0;
  Problem::Out out = p.hygienic(bad);
  bad += canaryCompare(p, out);
  return report(kernel, "T2 one-hot", b, seq, bad);
}

// T3: `scale_log2` = 1 and integer scores (Q row e_0, K's first column an integer) whose row maximum grows by 1 per
// key block, V in [0, 1].
static int t3(const Kernel &kernel, unsigned b, unsigned seq) {
  Random r{seq + 43u};
  auto fq = [](unsigned, unsigned, unsigned, unsigned d) { return d == 0 ? 1.0f : 0.0f; };
  auto fk = [](unsigned, unsigned h, unsigned j, unsigned d) {
    return d == 0 ? float(int(j / D) - (j % D == 0 ? 0 : int((j * 7 + h) % 4))) : 0.0f;
  };
  auto fv = [&r](unsigned, unsigned, unsigned, unsigned) { return float(r.next() % 9u) / 8.0f; };
  Problem p(kernel, b, seq, 1, 2, 1.0f, seq * 43u + b, fq, fk, fv);
  size_t bad = 0;
  Problem::Out out = p.hygienic(bad);
  bad += p.compare(out, false, std::ldexp(1.0, -15) * p.maxV(), std::ldexp(1.0, -8), std::ldexp(1.0, -20));
  return report(kernel, "T3", b, seq, bad);
}

// A table of pages outside the cache. Sequence 0's entries all address rows outside it: past its end, or negative as
// TMA's signed coordinates (the page row wraps modulo 2^32), so its K and V read as zeros, every score it sees is 0,
// and O must be exactly 0 and LSE ln(n) for a row that sees n keys. The other sequences mix valid pages with ones
// past the end, ones whose row wraps negative and ones whose row wraps back into the cache: their results are garbage,
// which must only be finite. In every case nothing may fault, and nothing outside O and LSE may be written.
static int outOfRange(const Kernel &kernel, unsigned b, unsigned seq) {
  Random r{seq + 47u};
  auto fq = [&r](unsigned, unsigned, unsigned, unsigned) { return r.uniform(-1, 1); };
  auto fkv = [&r](unsigned, unsigned, unsigned, unsigned) { return r.uniform(-1, 1); };
  // No spare pages: a wild entry that lands on a valid page must find finite data there.
  Problem p(kernel, b, seq, 0, 3, scaleLog2, seq * 53u + b, fq, fkv, fkv);
  const unsigned negative = ((1u << 31) + D - 1) / D;  // its row is just past 2^31: negative as signed
  const unsigned outside[] = {p.pages, p.pages + 5, 0xffffffffu, negative};
  const unsigned wild[] = {p.pages, 0xffffffffu, negative, 2 * negative, 0xdeadbeefu, 0x80000000u, 1u, 0u};
  for (unsigned s = 0; s < b; ++s)
    for (unsigned j = 0; j < p.maxPages; ++j) {
      unsigned &entry = p.table[size_t(s) * p.maxPages + j];
      if (s == 0) entry = outside[r.next() % 4];
      else if (r.next() % 2) entry = wild[r.next() % 8];
    }
  p.uploadTable();
  size_t bad = 0;
  Problem::Out out = p.hygienic(bad);
  for (unsigned h = 0; h < H; ++h)
    for (unsigned i = 0; i < seq; ++i) {
      const size_t row = size_t(h) * seq + i;
      const double lse = std::log(double(p.keys(i)));
      bad += !(std::fabs(double(out.lse[row]) - lse) <= std::ldexp(1.0, -22) + std::ldexp(1.0, -20) * lse);
      for (unsigned d = 0; d < D; ++d) bad += out.o[row * D + d] != 0.0f;
    }
  return report(kernel, "out-of-range table", b, seq, bad);
}

int main() {
  int failures = 0;

  for (const Kernel &kernel : kernels) {
    // Several sequences, sequences of one block, tables wider than needed, and spare pages; A2's tails: one key, one
    // short of a block, one past it, a long sequence with a partial last page, and a long one.
    failures += t1(kernel, 2, 256, 3, 2);
    failures += t1(kernel, 3, 384, 1, 0);
    failures += t1(kernel, 1, 1024, 4, 1);
    failures += t1(kernel, 5, 128, 2, 3);
    failures += t1(kernel, 3, 1, 1, 1);
    failures += t1(kernel, 2, 127, 2, 0);
    failures += t1(kernel, 3, 129, 1, 1);
    failures += t1(kernel, 2, 1000, 2, 1);
    failures += t1(kernel, 1, 4096, 0, 0);
    failures += t2Uniform(kernel, 2, 256);
    failures += t2Uniform(kernel, 1, 512);
    failures += t2Uniform(kernel, 3, 129);
    failures += t2Uniform(kernel, 2, 1000);
    failures += t2OneHot(kernel, 2, 512);
    failures += t2OneHot(kernel, 3, 128);
    failures += t2OneHot(kernel, 2, 127);
    failures += t2OneHot(kernel, 1, 1000);
    failures += t3(kernel, 1, 1024);
    failures += t3(kernel, 2, 512);
    failures += t3(kernel, 2, 1000);
    failures += outOfRange(kernel, 3, 512);
    failures += outOfRange(kernel, 2, 200);

    // What the launcher must refuse rather than launch, one requirement broken each: {B, seq, max_pages, pages,
    // rows_q, rows_kv, cols_kv, dim}, with the refusal reported before any memory is touched (the arrays are a small
    // valid problem's). (A `seq` that 128 does not divide is accepted since A2; the checks above run it.)
    {
      auto zero = [](unsigned, unsigned, unsigned, unsigned) { return 0.0f; };
      Problem p(kernel, 1, 128, 0, 0, scaleLog2, 1, zero, zero, zero);
      const unsigned kv = D, cols = H * D;  // rows_kv of one page, and cols_kv
      const unsigned bigB = 65535 / H + 1;
      const unsigned bigSeq = (((1u << 31) + H * D - 1) / (H * D) + D - 1) / D * D;
      const unsigned bigPages = ((1u << 31) + D - 1) / D;
      struct Case {
        const char *what;
        unsigned b, seq, maxPages, pages, rowsQ, rowsKv, colsKv, dim;
      } refused[] = {
          {"seq = 0", 1, 0, 1, 1, 0, kv, cols, 128},
          {"B = 0", 0, 128, 1, 1, 0, kv, cols, 128},
          {"B·H > 65535", bigB, 128, 1, 1, bigB * H * 128, kv, cols, 128},
          {"B·H·seq·128 ≥ 2^31", 1, bigSeq, bigSeq / D, 1, H * bigSeq, kv, cols, 128},
          {"rows_q ≠ B·H·seq", 1, 128, 1, 1, H * 128 + 128, kv, cols, 128},
          {"pages·128 ≥ 2^31", 1, 128, 1, bigPages, H * 128, bigPages * kv, cols, 128},
          {"rows_kv ≠ pages·128", 1, 128, 1, 2, H * 128, kv, cols, 128},
          {"cols_kv ≠ H·128", 1, 128, 1, 1, H * 128, kv, cols + D, 128},
          {"dim ≠ 128", 1, 128, 1, 1, H * 128, kv, cols, 64},
          {"max_pages < seq/128", 1, 256, 1, 2, H * 256, 2 * kv, cols, 128},
          {"max_pages < ceil(seq/128)", 1, 200, 1, 2, H * 200, 2 * kv, cols, 128},
          {"B·max_pages ≥ 2^31", 1, 128, 1u << 31, 1, H * 128, kv, cols, 128},
      };
      for (const Case &c : refused) {
        cudaError_t status = launch(kernel, p.dQ, p.dK, p.dV, p.dO, p.dLse, p.dTable, c.b, c.seq, c.maxPages, c.pages,
                                    c.rowsQ, c.rowsKv, c.colsKv, c.dim, scaleLog2);
        std::printf("%s %s refused %s: %s\n", status != cudaSuccess ? "ok  " : "FAIL", kernel.name, c.what,
                    cudaGetErrorString(status));
        failures += status == cudaSuccess;
      }
    }

    // Throughput on a long prefill.
    {
      const unsigned b = 4, seq = 4096;
      auto fq = [](unsigned, unsigned, unsigned i, unsigned d) { return float(int((i * 3 + d) % 17) - 8) / 64.0f; };
      Problem p(kernel, b, seq, 0, 0, scaleLog2, 42, fq, fq, fq);
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
      const double flops = (kernel.causal ? 2.0 : 4.0) * b * H * double(seq) * seq * D;
      std::printf("perf %s B=%u H=%u seq=%u: %.3f ms per launch, %.1f TFLOP/s\n", kernel.name, b, H, seq, ms / reps,
                  flops * reps / (ms * 1e-3) / 1e12);
      cudaEventDestroy(start);
      cudaEventDestroy(stop);
    }
  }

  std::printf(failures ? "%d check(s) failed\n" : "all checks passed\n", failures);
  return failures ? 1 : 0;
}
