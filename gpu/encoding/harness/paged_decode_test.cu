// Runs the generated kernels of paged decode (gpu/encoding/P2.md): the append (examples/paged_append.rac), the split
// attention for G = 1, 4 and 8 query heads per KV head (examples/paged_decode.rac) and the combine
// (examples/paged_combine.rac), in that order, against a CPU reference that reads the cache back after the append and
// gathers it through the block table. Checks that the append writes exactly the rows its claims hold, that colliding,
// out-of-range and reused-epoch claims are refused and never written, that the partial results cover their rows once
// and stay inside their arrays, and that the launchers refuse what the kernels cannot handle. Needs an sm_100a GPU:
//
//   for f in paged_append paged_decode paged_combine; do gpu/gen.sh gpu/encoding/examples/$f.rac > $f.cu; done
//   nvcc -std=c++17 -O2 -Xcompiler -pthread -gencode arch=compute_100a,code=sm_100a -o paged_decode_test \
//     paged_append.cu paged_decode.cu paged_combine.cu gpu/encoding/harness/paged_decode_test.cu -lcuda
//   ./paged_decode_test
//
// The kernels' KV head count is a generation-time constant; the harness assumes the examples' 8 (`-DHEADS=…`
// otherwise). The cache is `[pages·128, 8·128]`: page `p` holds positions 128p to 128p + 127 of every head. Pages that no
// sequence uses hold NaN, so a load from a wrong page shows; a last page's rows past the new position hold ±2^60 in K
// and V, so a key the mask lets through shows, while a masked one contributes exactly 0. Opart, LSEpart and O start as
// NaN inside sentinel guard bands, so a row never written, or one written outside its array, shows.
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

#ifndef HEADS
#define HEADS 8
#endif

extern "C" cudaError_t paged_append_launch(__nv_bfloat16 *K, __nv_bfloat16 *V, const __nv_bfloat16 *k_new,
                                           const __nv_bfloat16 *v_new, const unsigned *lens, const unsigned *block_table,
                                           unsigned long long *owners, unsigned *appended, unsigned B,
                                           unsigned max_pages, unsigned pages, unsigned epoch, cudaStream_t stream);
#define DECODE_LAUNCH(name)                                                                                          \
  extern "C" cudaError_t name(const __nv_bfloat16 *Q, const __nv_bfloat16 *K, const __nv_bfloat16 *V, float *Opart, \
                              float *LSEpart, const unsigned *block_table, const unsigned *lens, unsigned B,         \
                              unsigned max_pages, unsigned splits, unsigned pages, unsigned rows_q, unsigned rows_kv, \
                              unsigned cols_kv, unsigned dim, float scale_log2, cudaStream_t stream)
DECODE_LAUNCH(paged_decode_g1_launch);
DECODE_LAUNCH(paged_decode_g4_launch);
DECODE_LAUNCH(paged_decode_g8_launch);
extern "C" cudaError_t paged_combine_launch(const float *Opart, const float *LSEpart, __nv_bfloat16 *O, float *LSE,
                                            unsigned rows, unsigned splits, cudaStream_t stream);

#define CHECK(call)                                                                                                  \
  do {                                                                                                               \
    cudaError_t status_ = (call);                                                                                    \
    if (status_ != cudaSuccess) {                                                                                    \
      std::fprintf(stderr, "%s:%d: %s\n", __FILE__, __LINE__, cudaGetErrorString(status_));                          \
      std::exit(2);                                                                                                  \
    }                                                                                                                \
  } while (0)

static const unsigned H = HEADS;  // KV heads
static const unsigned D = 128;    // the head dimension, and the positions of a page
static const unsigned W = H * D;  // a cache row's elements

// `x` rounded to the nearest bf16, ties to even (finite `x` only).
static float bf16(float x) {
  uint32_t u;
  std::memcpy(&u, &x, sizeof(u));
  u += 0x7fffu + ((u >> 16) & 1u);
  u &= 0xffff0000u;
  std::memcpy(&x, &u, sizeof(x));
  return x;
}

static float fromBf16(__nv_bfloat16 b) {
  uint16_t h;
  std::memcpy(&h, &b, sizeof(h));
  const uint32_t u = uint32_t(h) << 16;
  float x;
  std::memcpy(&x, &u, sizeof(x));
  return x;
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

// A deterministic stream of numbers.
struct Random {
  uint32_t state;
  uint32_t next() {
    state = state * 1664525u + 1013904223u;
    return state >> 8;
  }
  // Uniform in [lo, hi], rounded to bf16.
  float uniform(float lo, float hi) { return bf16(lo + (hi - lo) * float(next() % 65536u) / 65535.0f); }
};

template <class T> static T *deviceArray(size_t n) {
  T *p = nullptr;
  CHECK(cudaMalloc(&p, std::max<size_t>(n, 1) * sizeof(T)));
  return p;
}

static void upload(__nv_bfloat16 *dst, const std::vector<float> &src) {
  std::vector<__nv_bfloat16> host(src.size());
  for (size_t i = 0; i < src.size(); ++i) host[i] = __float2bfloat16(src[i]);
  CHECK(cudaMemcpy(dst, host.data(), host.size() * sizeof(__nv_bfloat16), cudaMemcpyHostToDevice));
}

static std::vector<float> download(const __nv_bfloat16 *src, size_t n) {
  std::vector<__nv_bfloat16> host(n);
  CHECK(cudaMemcpy(host.data(), src, n * sizeof(__nv_bfloat16), cudaMemcpyDeviceToHost));
  std::vector<float> out(n);
  for (size_t i = 0; i < n; ++i) out[i] = fromBf16(host[i]);
  return out;
}

template <class T> static void uploadVector(T *dst, const std::vector<T> &src) {
  CHECK(cudaMemcpy(dst, src.data(), src.size() * sizeof(T), cudaMemcpyHostToDevice));
}

template <class T> static std::vector<T> downloadVector(const T *src, size_t n) {
  std::vector<T> out(n);
  CHECK(cudaMemcpy(out.data(), src, n * sizeof(T), cudaMemcpyDeviceToHost));
  return out;
}

// Whether two floats have the same bits (NaN included).
static bool sameBits(float a, float b) { return std::memcmp(&a, &b, sizeof(a)) == 0; }

// The sequences, their tables and the cache, on the host and the device, with the owners of its pages.
struct Cache {
  unsigned b, maxPages, pages;
  std::vector<unsigned> lens;   // the keys of each sequence before this step
  std::vector<unsigned> table;  // [B, maxPages]
  std::vector<float> k, v;      // [pages·128, H·128], as last uploaded or read back
  std::vector<float> kNew, vNew;  // [B·H, 128]
  std::vector<unsigned> spares;   // the pages no sequence uses
  __nv_bfloat16 *dK, *dV, *dKNew, *dVNew;
  unsigned *dLens, *dTable, *dAppended;
  unsigned long long *dOwners;
  unsigned epoch = 1;

  // Sequences of `lens` keys, each with the pages its keys and its new position need, shuffled across the cache with
  // `spare` pages no sequence uses (NaN) and `extra` table columns past each sequence's last page (0xdeadbeef, a page
  // past the cache). A last page's rows from the new position on hold ±2^60.
  Cache(const std::vector<unsigned> &lens, unsigned spare, unsigned extra, uint32_t seed) : b(unsigned(lens.size())), lens(lens) {
    unsigned most = 0, total = spare;
    for (unsigned n : lens) {
      most = std::max(most, n / D + 1);
      total += n / D + 1;
    }
    maxPages = most + extra;
    pages = total;
    table.assign(size_t(b) * maxPages, 0xdeadbeefu);
    k.assign(size_t(pages) * D * W, NAN);
    v.assign(size_t(pages) * D * W, NAN);
    Random r{seed};
    std::vector<unsigned> perm(pages);
    for (unsigned p = 0; p < pages; ++p) perm[p] = p;
    for (unsigned p = pages; p > 1; --p) std::swap(perm[p - 1], perm[r.next() % p]);
    unsigned next = 0;
    for (unsigned s = 0; s < b; ++s)
      for (unsigned j = 0; j <= lens[s] / D; ++j) table[size_t(s) * maxPages + j] = perm[next++];
    spares.assign(perm.begin() + next, perm.end());
    for (unsigned s = 0; s < b; ++s)
      for (unsigned h = 0; h < H; ++h)
        for (unsigned key = 0; key < (lens[s] / D + 1) * D; ++key)
          for (unsigned d = 0; d < D; ++d) {
            const float big = (r.next() % 2 ? 1.0f : -1.0f) * std::ldexp(1.0f, 60);
            k[at(s, h, key) + d] = key < lens[s] ? r.uniform(-1, 1) : big;
            v[at(s, h, key) + d] = key < lens[s] ? r.uniform(-1, 1) : -big;
          }
    kNew.resize(size_t(b) * W);
    vNew.resize(size_t(b) * W);
    for (float &x : kNew) x = r.uniform(-1, 1);
    for (float &x : vNew) x = r.uniform(-1, 1);
    dK = deviceArray<__nv_bfloat16>(k.size());
    dV = deviceArray<__nv_bfloat16>(v.size());
    dKNew = deviceArray<__nv_bfloat16>(kNew.size());
    dVNew = deviceArray<__nv_bfloat16>(vNew.size());
    dLens = deviceArray<unsigned>(b);
    dTable = deviceArray<unsigned>(table.size());
    dAppended = deviceArray<unsigned>(size_t(b) * H);
    dOwners = deviceArray<unsigned long long>(size_t(pages) * H);
    upload(dK, k);
    upload(dV, v);
    upload(dKNew, kNew);
    upload(dVNew, vNew);
    uploadVector(dLens, lens);
    uploadVector(dTable, table);
    CHECK(cudaMemset(dOwners, 0, size_t(pages) * H * sizeof(unsigned long long)));
  }
  ~Cache() {
    cudaFree(dK);
    cudaFree(dV);
    cudaFree(dKNew);
    cudaFree(dVNew);
    cudaFree(dLens);
    cudaFree(dTable);
    cudaFree(dAppended);
    cudaFree(dOwners);
  }

  // The first element of key `key` of sequence `s`, head `h`, through the table.
  size_t at(unsigned s, unsigned h, unsigned key) const {
    return (size_t(table[size_t(s) * maxPages + key / D]) * D + key % D) * W + size_t(h) * D;
  }

  void uploadTables() {
    uploadVector(dLens, lens);
    uploadVector(dTable, table);
  }

  // Random K and V in rows 0 to `rows` − 1 of page `p`, every head.
  void randomize(unsigned p, unsigned rows, uint32_t seed) {
    Random r{seed};
    for (size_t i = size_t(p) * D * W; i < (size_t(p) * D + rows) * W; ++i) {
      k[i] = r.uniform(-1, 1);
      v[i] = r.uniform(-1, 1);
    }
    upload(dK, k);
    upload(dV, v);
  }

  // One append at the current epoch, which then increases (unless `reuse`): which (sequence, head) appended, and the
  // number of cache elements that differ from what the append may write (the new row where it appended, else the old
  // value).
  struct Appended {
    std::vector<unsigned> flags;  // [B·H]
    size_t wrongElements = 0;
  };
  Appended append(bool reuse) {
    std::vector<float> wantK = k, wantV = v;
    CHECK(paged_append_launch(dK, dV, dKNew, dVNew, dLens, dTable, dOwners, dAppended, b, maxPages, pages, epoch, nullptr));
    CHECK(cudaDeviceSynchronize());
    if (!reuse) ++epoch;
    Appended out;
    out.flags = downloadVector(dAppended, size_t(b) * H);
    k = download(dK, k.size());
    v = download(dV, v.size());
    // Each element must hold its old value, or the new row of the one (sequence, head) that appended there.
    for (unsigned s = 0; s < b; ++s)
      for (unsigned h = 0; h < H; ++h)
        if (out.flags[s * H + h] == 1)
          for (unsigned d = 0; d < D; ++d) {
            wantK[at(s, h, lens[s]) + d] = kNew[(size_t(s) * H + h) * D + d];
            wantV[at(s, h, lens[s]) + d] = vNew[(size_t(s) * H + h) * D + d];
          }
    for (size_t i = 0; i < k.size(); ++i) out.wrongElements += !sameBits(k[i], wantK[i]) + !sameBits(v[i], wantV[i]);
    return out;
  }
};

// A decode kernel: its query heads per KV head, and its launcher.
struct Kernel {
  const char *name;
  unsigned group;
  cudaError_t (*launch)(const __nv_bfloat16 *, const __nv_bfloat16 *, const __nv_bfloat16 *, float *, float *,
                        const unsigned *, const unsigned *, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned,
                        unsigned, unsigned, float, cudaStream_t);
};

static const Kernel kernels[] = {{"paged_decode_g1", 1, paged_decode_g1_launch},
                                 {"paged_decode_g4", 4, paged_decode_g4_launch},
                                 {"paged_decode_g8", 8, paged_decode_g8_launch}};

static const float log2e = 1.4426950408889634f;
static const float scaleLog2 = log2e / std::sqrt(128.0f);  // scale · log2(e), scale = 1/√128

// Sentinel floats (bytes 0x7f) on both sides of an array of `n` floats, which starts as NaN.
struct Guarded {
  static constexpr size_t guard = 4096;
  size_t n;
  float *all, *data;
  explicit Guarded(size_t n) : n(n), all(deviceArray<float>(n + 2 * guard)), data(all + guard) {}
  ~Guarded() { cudaFree(all); }
  void reset() {
    CHECK(cudaMemset(all, 0x7f, (n + 2 * guard) * sizeof(float)));
    CHECK(cudaMemset(data, 0xff, n * sizeof(float)));
  }
  // The array, and the number of guard floats written.
  std::vector<float> read(size_t &guardsWritten) const {
    std::vector<float> host = downloadVector(all, n + 2 * guard);
    for (size_t i = 0; i < host.size(); ++i) {
      uint32_t u;
      std::memcpy(&u, &host[i], sizeof(u));
      guardsWritten += (i < guard || i >= guard + n) && u != 0x7f7f7f7fu;
    }
    return std::vector<float>(host.begin() + guard, host.begin() + guard + n);
  }
};

// One decode step after an append: the partials of `kernel` over `splits` splits, then their combination, compared
// with the reference over each sequence's `lens[b] + 1` keys as the cache now holds them. Returns the number of
// violations.
static size_t decode(const Kernel &kernel, Cache &c, unsigned splits, uint32_t seed) {
  const unsigned g = kernel.group, rows = c.b * H * g;
  Random r{seed};
  std::vector<float> q(size_t(rows) * D);
  for (size_t i = 0; i < q.size(); ++i) q[i] = (i / D) % 7 == 0 ? r.uniform(-8, 8) : r.uniform(-1, 1);
  __nv_bfloat16 *dQ = deviceArray<__nv_bfloat16>(q.size());
  upload(dQ, q);
  Guarded oPart(size_t(splits) * rows * D), lsePart(size_t(splits) * rows);
  __nv_bfloat16 *dO = deviceArray<__nv_bfloat16>(size_t(rows) * D + 2 * D);
  Guarded lse(rows);
  oPart.reset();
  lsePart.reset();
  lse.reset();
  CHECK(cudaMemset(dO, 0xff, (size_t(rows) * D + 2 * D) * sizeof(__nv_bfloat16)));
  CHECK(kernel.launch(dQ, c.dK, c.dV, oPart.data, lsePart.data, c.dTable, c.dLens, c.b, c.maxPages, splits, c.pages, rows,
                      c.pages * D, W, D, scaleLog2, nullptr));
  CHECK(paged_combine_launch(oPart.data, lsePart.data, dO + D, lse.data, rows, splits, nullptr));
  CHECK(cudaDeviceSynchronize());
  size_t bad = 0;
  const std::vector<float> op = oPart.read(bad), lp = lsePart.read(bad), lseOut = lse.read(bad);
  const std::vector<float> oAll = download(dO, size_t(rows) * D + 2 * D);
  for (unsigned d = 0; d < D; ++d) bad += !std::isnan(oAll[d]) + !std::isnan(oAll[D + size_t(rows) * D + d]);
  if (bad) std::printf("    %zu guard element(s) written\n", bad);

  // Every partial row written: an empty split's as O = 0 and LSE = −∞, every other finite.
  size_t partialBad = 0;
  for (unsigned s = 0; s < splits; ++s)
    for (unsigned row = 0; row < rows; ++row) {
      const unsigned seq = row / (H * g), keys = c.lens[seq] + 1, n = (keys + D - 1) / D, per = (n + splits - 1) / splits;
      const bool empty = !(s * per < std::min(n, s * per + per));
      const size_t at = size_t(s) * rows + row;
      const float l = lp[at];
      bool ok = empty ? l == -INFINITY : std::isfinite(l);
      for (unsigned d = 0; d < D; ++d) ok = ok && (empty ? op[at * D + d] == 0.0f : std::isfinite(op[at * D + d]));
      partialBad += !ok;
    }
  if (partialBad) std::printf("    %zu partial row(s) wrong\n", partialBad);
  bad += partialBad;

  // The reference, from the cache as read back, in double: t = c·q·k in log2 units over keys 0 to lens[b], m its
  // maximum, l = Σ 2^(t − m), O = Σ 2^(t − m)·V / l and LSE = (m + log2 l)·ln 2.
  std::vector<double> oRef(size_t(rows) * D), lseRef(rows);
  double maxV = 0;
  for (unsigned s = 0; s < c.b; ++s)
    for (unsigned h = 0; h < H; ++h)
      for (unsigned key = 0; key <= c.lens[s]; ++key)
        for (unsigned d = 0; d < D; ++d) maxV = std::max(maxV, std::fabs(double(c.v[c.at(s, h, key) + d])));
  parallelFor(rows, [&](size_t row) {
    const unsigned s = unsigned(row / (H * g)), h = unsigned(row / g % H), n = c.lens[s] + 1;
    std::vector<double> t(n);
    double m = -INFINITY;
    for (unsigned key = 0; key < n; ++key) {
      double dot = 0;
      for (unsigned d = 0; d < D; ++d) dot += double(q[row * D + d]) * double(c.k[c.at(s, h, key) + d]);
      t[key] = double(scaleLog2) * dot;
      m = std::max(m, t[key]);
    }
    double l = 0;
    double *o = &oRef[row * D];
    for (unsigned key = 0; key < n; ++key) {
      const double p = std::exp2(t[key] - m);
      l += p;
      for (unsigned d = 0; d < D; ++d) o[d] += p * double(c.v[c.at(s, h, key) + d]);
    }
    for (unsigned d = 0; d < D; ++d) o[d] /= l;
    lseRef[row] = (m + std::log2(l)) * std::log(2.0);
  });
  // |O − O_ref| ≤ 2^-7·max|V| + bf16's rounding of the result, and |LSE − LSE_ref| ≤ 2^-8 + 2^-20·|LSE_ref|.
  const double oBound = std::ldexp(1.0, -7) * maxV;
  size_t wrong = 0;
  for (unsigned row = 0; row < rows; ++row) {
    if (!(std::fabs(double(lseOut[row]) - lseRef[row]) <= std::ldexp(1.0, -8) + std::ldexp(1.0, -20) * std::fabs(lseRef[row]))) {
      if (wrong < 5) std::printf("    LSE[%u] = %.9g, want %.9g\n", row, lseOut[row], lseRef[row]);
      ++wrong;
    }
    for (unsigned d = 0; d < D; ++d) {
      const double want = oRef[size_t(row) * D + d], got = oAll[D + size_t(row) * D + d];
      if (!(std::fabs(got - want) <= oBound + std::ldexp(oBound + std::fabs(want), -8))) {
        if (wrong < 5) std::printf("    O[%u][%u] = %.9g, want %.9g\n", row, d, got, want);
        ++wrong;
      }
    }
  }
  cudaFree(dQ);
  cudaFree(dO);
  return bad + wrong;
}

static int report(const std::string &what, size_t bad) {
  std::printf("%s %s%s\n", bad ? "FAIL" : "ok  ", what.c_str(), bad ? (" (" + std::to_string(bad) + " wrong)").c_str() : "");
  return bad != 0;
}

static std::string lengths(const std::vector<unsigned> &lens) {
  std::string s;
  for (unsigned n : lens) s += (s.empty() ? "" : ",") + std::to_string(n);
  return s;
}

// Every sequence appends, each new row lands where its table says and nowhere else, and every decode kernel at each
// split count matches the reference over the appended cache.
static int appendThenDecode(const std::vector<unsigned> &lens, unsigned spare, unsigned extra, uint32_t seed) {
  Cache c(lens, spare, extra, seed);
  Cache::Appended a = c.append(false);
  size_t bad = a.wrongElements;
  for (unsigned f : a.flags) bad += f != 1;
  int failures = report("append, lens " + lengths(lens), bad);
  for (const Kernel &kernel : kernels)
    for (unsigned splits : {1u, 3u, 8u})
      failures += report(std::string(kernel.name) + " splits=" + std::to_string(splits) + ", lens " + lengths(lens),
                         decode(kernel, c, splits, seed * 31u + splits + kernel.group));
  return failures;
}

// Sequences whose tables name one last page: of each group sharing a page, for each head, exactly one appends, the
// others are refused and write nothing, and decoding over the cache as it then is (a refused sequence's new key is
// whatever row the winner wrote, or the old one) matches the reference.
static int collisions(uint32_t seed) {
  // Sequences 0, 1 and 2 share the last page of sequence 0; 3 and 4 share sequence 3's; 5 has its own.
  Cache c({130, 140, 129, 7, 3, 300}, 2, 1, seed);
  auto share = [&c](unsigned s, unsigned with) {
    c.table[size_t(s) * c.maxPages + c.lens[s] / D] = c.table[size_t(with) * c.maxPages + c.lens[with] / D];
  };
  share(1, 0);
  share(2, 0);
  share(4, 3);
  c.uploadTables();
  // The shared pages' rows up to the last new position on them hold keys, finite, whichever sequence reads them.
  c.randomize(c.table[c.lens[0] / D], c.lens[1] % D + 1, seed + 2);
  c.randomize(c.table[size_t(3) * c.maxPages + c.lens[3] / D], c.lens[3] % D + 1, seed + 3);
  Cache::Appended a = c.append(false);
  size_t bad = a.wrongElements;
  const std::vector<std::vector<unsigned>> groups = {{0, 1, 2}, {3, 4}, {5}};
  for (const std::vector<unsigned> &group : groups)
    for (unsigned h = 0; h < H; ++h) {
      unsigned held = 0;
      for (unsigned s : group) held += a.flags[s * H + h] == 1, bad += a.flags[s * H + h] > 1;
      bad += held != 1;
    }
  int failures = report("append with colliding last pages", bad);
  failures += report("paged_decode_g4 splits=3 after colliding appends", decode(kernels[1], c, 3, seed + 1));
  return failures;
}

// Table entries outside the table or the cache: a position past the table's columns, an entry past the cache, and the
// largest entry are refused and write nothing; the other sequences append.
static int outOfRange(uint32_t seed) {
  Cache c({5, 200, 3, 130}, 1, 0, seed);
  c.lens[0] = c.maxPages * D;                            // its new position's block lies past the table's columns
  c.table[size_t(1) * c.maxPages + c.lens[1] / D] = c.pages;  // a page past the cache
  c.table[size_t(2) * c.maxPages + c.lens[2] / D] = 0xffffffffu;
  c.uploadTables();
  Cache::Appended a = c.append(false);
  size_t bad = a.wrongElements;
  for (unsigned s = 0; s < c.b; ++s)
    for (unsigned h = 0; h < H; ++h) bad += a.flags[s * H + h] != (s == 3 ? 1u : 0u);
  return report("append with out-of-range table entries", bad);
}

// Epochs: a launch at an epoch that a previous launch used finds that launch's claims current, so a page claimed then
// by one sequence is refused to another, while a fresh page is claimed; at a new epoch the claim succeeds.
static int epochs(uint32_t seed) {
  Cache c({10, 20}, 2, 1, seed);
  Cache::Appended first = c.append(true);  // epoch 1, kept
  size_t bad = first.wrongElements;
  for (unsigned f : first.flags) bad += f != 1;
  // Sequence 1's next position is on the page sequence 0 claimed at epoch 1, and sequence 0's on a spare page.
  const unsigned page0 = c.table[c.lens[0] / D];
  c.lens[0] += 1;
  c.lens[1] += 1;
  c.table[size_t(1) * c.maxPages + c.lens[1] / D] = page0;
  c.table[c.lens[0] / D] = c.spares[0];
  c.uploadTables();
  Cache::Appended again = c.append(false);  // epoch 1 again
  bad += again.wrongElements;
  for (unsigned h = 0; h < H; ++h) bad += again.flags[h] != 1u, bad += again.flags[H + h] != 0u;
  int failures = report("append at a reused epoch", bad);
  // At epoch 2, both claims are fresh: sequence 1 claims the page sequence 0 claimed at epoch 1, and sequence 0 its
  // spare page again.
  Cache::Appended fresh = c.append(false);
  bad = fresh.wrongElements;
  for (unsigned f : fresh.flags) bad += f != 1;
  failures += report("append at the next epoch", bad);
  return failures;
}

// What the launchers must refuse rather than launch, one requirement broken each, before any memory is touched.
static int refusals() {
  Cache c({3}, 0, 0, 1);
  int failures = 0;
  auto check = [&failures](const char *what, cudaError_t status) {
    std::printf("%s refused %s: %s\n", status != cudaSuccess ? "ok  " : "FAIL", what, cudaGetErrorString(status));
    failures += status == cudaSuccess;
  };
  const unsigned bigPages = ((1u << 31) + D - 1) / D;
  // The append: {B, max_pages, pages, epoch}.
  auto append = [&c](unsigned b, unsigned maxPages, unsigned pages, unsigned epoch) {
    return paged_append_launch(c.dK, c.dV, c.dKNew, c.dVNew, c.dLens, c.dTable, c.dOwners, c.dAppended, b, maxPages, pages,
                               epoch, nullptr);
  };
  check("append B = 0", append(0, 1, 1, 1));
  check("append epoch = 0", append(1, 1, 1, 0));
  check("append B·H·128 ≥ 2^31", append((1u << 31) / W, 1, 1, 1));
  check("append pages·128 ≥ 2^31", append(1, 1, bigPages, 1));
  check("append B·max_pages ≥ 2^31", append(1, 1u << 31, 1, 1));
  // The decode kernels: {B, max_pages, splits, pages, rows_q, rows_kv, cols_kv, dim}.
  for (const Kernel &k : kernels) {
    const unsigned g = k.group, rq = H * g;
    auto decode = [&c, &k](unsigned b, unsigned maxPages, unsigned splits, unsigned pages, unsigned rowsQ, unsigned rowsKv,
                           unsigned colsKv, unsigned dim) {
      return k.launch(nullptr, c.dK, c.dV, nullptr, nullptr, c.dTable, c.dLens, b, maxPages, splits, pages, rowsQ, rowsKv,
                      colsKv, dim, scaleLog2, nullptr);
    };
    const std::string n = k.name;
    const unsigned bigB = 65535 / H + 1, bigSplits = (1u << 31) / (rq * D) + 1;
    check((n + " B = 0").c_str(), decode(0, 1, 1, 1, 0, D, W, D));
    check((n + " B·H > 65535").c_str(), decode(bigB, 1, 1, 1, bigB * rq, D, W, D));
    check((n + " splits = 0").c_str(), decode(1, 1, 0, 1, rq, D, W, D));
    check((n + " splits·B·H·G·128 ≥ 2^31").c_str(), decode(1, 1, bigSplits, 1, rq, D, W, D));
    check((n + " rows_q ≠ B·H·G").c_str(), decode(1, 1, 1, 1, rq + 1, D, W, D));
    check((n + " dim ≠ 128").c_str(), decode(1, 1, 1, 1, rq, D, W, 64));
    check((n + " B·max_pages ≥ 2^31").c_str(), decode(1, 1u << 31, 1, 1, rq, D, W, D));
    check((n + " pages·128 ≥ 2^31").c_str(), decode(1, 1, 1, bigPages, rq, bigPages * D, W, D));
    check((n + " rows_kv ≠ pages·128").c_str(), decode(1, 1, 1, 2, rq, D, W, D));
    check((n + " cols_kv ≠ H·128").c_str(), decode(1, 1, 1, 1, rq, D, W + D, D));
  }
  // The combine: {rows, splits}.
  check("combine rows = 0", paged_combine_launch(nullptr, nullptr, nullptr, nullptr, 0, 1, nullptr));
  check("combine splits = 0", paged_combine_launch(nullptr, nullptr, nullptr, nullptr, 1, 0, nullptr));
  check("combine splits·rows·128 ≥ 2^31", paged_combine_launch(nullptr, nullptr, nullptr, nullptr, 1u << 20, 1u << 4, nullptr));
  return failures;
}

int main() {
  int failures = 0;
  // Lengths from 0 cached keys (the new one alone) to several thousand; positions at a page's first and last row; more
  // splits than blocks; spare pages and wide tables.
  failures += appendThenDecode({0, 1, 127, 128, 255}, 2, 1, 11);
  failures += appendThenDecode({1000, 3, 384}, 1, 0, 12);
  failures += appendThenDecode({4999, 2047, 129}, 0, 2, 13);
  failures += collisions(21);
  failures += outOfRange(31);
  failures += epochs(41);
  failures += refusals();
  std::printf(failures ? "%d check(s) failed\n" : "all checks passed\n", failures);
  return failures ? 1 : 0;
}
