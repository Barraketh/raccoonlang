// H1 (gpu/ATTENTION.md §4.4), assumption A23: the layout of a bf16 A operand in tensor memory.
//
// Question. With `tcgen05.mma.cta_group::1.kind::f16 [d], [a], b-desc, idesc, p`, M = 128, A bf16 and not
// transposed, is row i of A lane i, are K elements packed two per 32-bit column with the lower K index in the low 16
// bits, and does each K = 16 step read 8 columns from the given address? PTX gives the layout only as a figure.
//
// PTX ISA 9.4: §9.7.18.10.10.1 `tcgen05.mma` (the [a-tmem] form); §9.7.18.10.5.4 (Figure 217, A in tensor memory);
// §9.7.18.8.4 `tcgen05.st` and §9.7.18.2.3.1.1 (the 32x32b shape: thread t of warp w writes lane 32·(w mod 4) + t);
// §9.7.18.8.3 `tcgen05.ld`; §9.7.18.8.5 `tcgen05.wait`; §9.7.18.6.4.4 (store, then MMA from another thread);
// §9.7.18.4.1–2 (descriptors); §9.7.18.12.1 `tcgen05.commit`.
//
// Cases (each in its own process):
//   control-perm, control-int   A and B both in shared memory, K-major: TinyGEMM's proven path. Checks the probe
//                               itself; if these fail, nothing else here means anything.
//   decode                      A's tensor-memory columns hold distinct codes (one per 16-bit half, tagged with the
//                               lane); B is the identity on its first 16 columns; one K = 16 MMA reads A at column
//                               a, a second at a + 8. D then shows, for each k, the column and half the MMA read, and
//                               that lane i fed row i. Prints the map and names the layout it matches.
//   <layout>-perm, <layout>-int P (128 × 128) written in tensor memory as <layout> says, B in shared memory (K-major),
//                               eight K = 16 MMAs over the whole K; D compared with P·B. B is a permutation (and P
//                               has distinct entries per row, so a wrong element names the k it came from) or a
//                               general integer matrix. The layouts:
//     a23          two per column, lower k in the low half, 8 columns per K step (what A23 and the design assume)
//     swapped      two per column, lower k in the high half, 8 columns per step
//     unpacked-lo  one per column, in the low half (high half 0), 16 columns per step
//     unpacked-hi  one per column, in the high half, 16 columns per step
//
// Outcomes. control fails: the probe's harness is wrong; fix it first. a23 passes (and decode agrees): A23 holds, and
// `storeP` packs as §3.4 says. swapped passes instead: `storeP` must pair its `cvt.rn.bf16x2.f32` operands the other
// way round (A25 then places element 2i in the high half). An unpacked layout passes: P needs 128 columns, which the
// tensor-memory map of §2.2 does not have (P would have to overlay S, as FA4 does, or shrink). Nothing passes: P goes
// through shared memory (§2.3's fallback), and decode's map says what the hardware did read.
//
// Build and run (exit status 0 only when the controls, decode and a23 pass):
//   nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a h1_tmem_a.cu -o h1_tmem_a && ./h1_tmem_a
#include "probe.h"

using namespace probe;

namespace {

enum class Layout { A23, Swapped, UnpackedLo, UnpackedHi };

const char *layout_name(Layout l) {
  switch (l) {
    case Layout::A23: return "a23";
    case Layout::Swapped: return "swapped";
    case Layout::UnpackedLo: return "unpacked-lo";
    case Layout::UnpackedHi: return "unpacked-hi";
  }
  return "?";
}

bool packed(Layout l) { return l == Layout::A23 || l == Layout::Swapped; }

// Tensor-memory columns: D at 0 (128 columns, and a second D at 128 for decode), A from 256.
constexpr uint32_t kD = 0, kD2 = 128, kA = 256;

// The 32-bit words of P's tensor-memory image under `layout`: lane r, column c at [r·ncols + c].
std::vector<uint32_t> tmem_words(const Matrix &p, Layout layout, uint32_t &ncols) {
  ncols = packed(layout) ? p.cols / 2 : p.cols;
  std::vector<uint32_t> w(size_t(p.rows) * ncols);
  for (uint32_t r = 0; r < p.rows; ++r)
    for (uint32_t c = 0; c < ncols; ++c) {
      uint32_t lo = 0, hi = 0;
      switch (layout) {
        case Layout::A23: lo = bf16_bits(p.at(r, 2 * c)), hi = bf16_bits(p.at(r, 2 * c + 1)); break;
        case Layout::Swapped: lo = bf16_bits(p.at(r, 2 * c + 1)), hi = bf16_bits(p.at(r, 2 * c)); break;
        case Layout::UnpackedLo: lo = bf16_bits(p.at(r, c)); break;
        case Layout::UnpackedHi: hi = bf16_bits(p.at(r, c)); break;
      }
      w[size_t(r) * ncols + c] = lo | (hi << 16);
    }
  return w;
}

Plan base_plan(uint32_t image_bytes) {
  Plan plan;
  std::memset(&plan, 0, sizeof plan);
  plan.tmem_cols = 512;
  plan.image_bytes = image_bytes;
  plan.n_ld = 1;
  plan.ld[0] = Region{kD, 128, 8, 0};
  return plan;
}

// B (N × K, K-major, 128 × 128) at image byte `b_base`; step s of the eight K = 16 steps.
Mma b_step(uint32_t b_base, uint32_t s) {
  Mma m;
  std::memset(&m, 0, sizeof m);
  m.d_col = kD;
  m.b_off = kmajor_step(b_base, 128, s);
  m.b_lbo = 0;
  m.b_sbo = 1024;
  m.idesc = idesc_bf16(128, 128, false);
  m.accumulate = s > 0;
  return m;
}

// The two B matrices, stored transposed (Bt[n][k] = B[k][n]) as the K-major operand is, and the P each is used with.
struct Inputs {
  Matrix p, bt;
  bool perm;
};

Inputs inputs(bool perm) {
  if (perm) {
    Matrix bt(128, 128);
    for (uint32_t n = 0; n < 128; ++n) bt.at(n, sigma(n)) = 1.0f;  // D[i][n] = P[i][σ(n)]
    return Inputs{code_matrix(), bt, true};
  }
  Lcg g{12345};
  Matrix p(128, 128), bt(128, 128);
  for (float &x : p.v) x = g.quarter();
  for (float &x : bt.v) x = g.small_int();
  return Inputs{p, bt, false};
}

size_t check(const std::vector<uint32_t> &d, const Inputs &in) {
  const Matrix want = product_abt(in.p, in.bt);
  if (!in.perm) return compare_d(d, 0, 128, 0, want, no_explanation);
  return compare_d(d, 0, 128, 0, want, [](uint32_t i, uint32_t n, float v) {
    std::printf(" (P[%u][k] for k = %d; B selects k = %u)", i, code_k(i, v), sigma(n));
  });
}

int control(bool perm) {
  const Inputs in = inputs(perm);
  Image image(2 * 32768);
  image.put_kmajor(0, in.p);
  image.put_kmajor(32768, in.bt);
  Plan plan = base_plan(uint32_t(image.bytes.size()));
  plan.n_mma = 8;
  for (uint32_t s = 0; s < 8; ++s) {
    plan.mma[s] = b_step(32768, s);
    plan.mma[s].a_off = kmajor_step(0, 128, s);
    plan.mma[s].a_sbo = 1024;
  }
  std::vector<uint32_t> d;
  if (!run_plan(plan, image, {}, 128 * 128, d)) return kError;
  return check(d, in) ? kFail : kPass;
}

int full(Layout layout, bool perm) {
  const Inputs in = inputs(perm);
  Image image(32768);
  image.put_kmajor(0, in.bt);
  uint32_t ncols = 0;
  const std::vector<uint32_t> words = tmem_words(in.p, layout, ncols);
  Plan plan = base_plan(uint32_t(image.bytes.size()));
  plan.n_st = 1;
  plan.st[0] = Region{kA, ncols, 8, 0};
  plan.n_mma = 8;
  const uint32_t step = packed(layout) ? 8 : 16;
  for (uint32_t s = 0; s < 8; ++s) {
    plan.mma[s] = b_step(0, s);
    plan.mma[s].a_tmem = 1;
    plan.mma[s].a_col = kA + s * step;
  }
  std::vector<uint32_t> d;
  if (!run_plan(plan, image, words, 128 * 128, d)) return kError;
  return check(d, in) ? kFail : kPass;
}

// decode: 32 columns of A, lane r, column j, half h (0 low, 1 high) hold the bf16 integer 1 + 2j + h + 64·(r mod 4),
// at most 256, so exact. B's first 16 rows (N) are the identity on K; the rest zero. MMA 0 reads A at kA into D at
// kD, MMA 1 at kA + 8 into kD2. D[r][n] for n < 16 is the A element the MMA used for (row r, k = n).
constexpr uint32_t kCodeCols = 32;

struct Slot {
  int col, half, tag;  // col −1: D was 0 or not a code
};

Slot decode_value(float v) {
  if (v < 1 || v > 256 || v != float(int(v))) return Slot{-1, -1, -1};
  const int code = int(v) - 1;
  return Slot{(code % 64) / 2, code % 2, code / 64};
}

// Where each layout hypothesis says MMA `m` (0 at kA, 1 at kA + 8) reads k, as (column relative to kA, half).
Slot predicted(Layout l, uint32_t m, uint32_t k) {
  const int base = int(8 * m);
  switch (l) {
    case Layout::A23: return Slot{base + int(k / 2), int(k % 2), 0};
    case Layout::Swapped: return Slot{base + int(k / 2), 1 - int(k % 2), 0};
    case Layout::UnpackedLo: return Slot{base + int(k), 0, 0};
    case Layout::UnpackedHi: return Slot{base + int(k), 1, 0};
  }
  return Slot{-1, -1, -1};
}

int decode() {
  Matrix bt(128, 64);  // one 64-wide box of K suffices for one K = 16 step
  for (uint32_t n = 0; n < 16; ++n) bt.at(n, n) = 1.0f;
  Image image(16384);
  image.put_kmajor(0, bt);
  std::vector<uint32_t> words(128 * kCodeCols);
  for (uint32_t r = 0; r < 128; ++r)
    for (uint32_t j = 0; j < kCodeCols; ++j) {
      const uint32_t lo = bf16_bits(float(1 + 2 * j + 64 * (r % 4)));
      const uint32_t hi = bf16_bits(float(2 + 2 * j + 64 * (r % 4)));
      words[r * kCodeCols + j] = lo | (hi << 16);
    }
  Plan plan = base_plan(uint32_t(image.bytes.size()));
  plan.n_st = 1;
  plan.st[0] = Region{kA, kCodeCols, 8, 0};
  plan.n_mma = 2;
  for (uint32_t m = 0; m < 2; ++m) {
    plan.mma[m] = b_step(0, 0);
    plan.mma[m].d_col = m ? kD2 : kD;
    plan.mma[m].a_tmem = 1;
    plan.mma[m].a_col = kA + 8 * m;
    plan.mma[m].accumulate = 0;
  }
  plan.ld[0] = Region{kD, 256, 8, 0};
  std::vector<uint32_t> d;
  if (!run_plan(plan, image, words, 128 * 256, d)) return kError;

  // Lane 0's map, then whether every lane agrees with it and carries its own tag.
  size_t inconsistent = 0, nonzero_tail = 0;
  for (uint32_t m = 0; m < 2; ++m) {
    std::printf("    MMA %u (A at column %u): k -> (column - %u, half) as read by lane 0:", m, kA + 8 * m, kA);
    for (uint32_t k = 0; k < 16; ++k) {
      const Slot s = decode_value(f32_value(d[m * 128 + k]));
      if (s.col < 0) std::printf(" %u:(%g)", k, f32_value(d[m * 128 + k]));
      else std::printf(" %u:(%d,%s)", k, s.col, s.half ? "hi" : "lo");
    }
    std::printf("\n");
    for (uint32_t r = 0; r < 128; ++r) {
      for (uint32_t k = 0; k < 16; ++k) {
        const Slot s0 = decode_value(f32_value(d[m * 128 + k]));
        const Slot s = decode_value(f32_value(d[size_t(r) * 256 + m * 128 + k]));
        if (s.col != s0.col || s.half != s0.half || s.tag != int(r % 4)) {
          if (inconsistent < 4)
            std::printf("    lane %u, MMA %u, k %u: D = %g, a different slot or lane tag than lane 0's\n", r, m, k,
                        f32_value(d[size_t(r) * 256 + m * 128 + k]));
          ++inconsistent;
        }
      }
      for (uint32_t n = 16; n < 128; ++n) nonzero_tail += f32_value(d[size_t(r) * 256 + m * 128 + n]) != 0.0f;
    }
  }
  if (inconsistent) std::printf("    %zu (lane, k) pairs disagree with lane 0 or with row = lane\n", inconsistent);
  if (nonzero_tail) std::printf("    %zu elements of D past column 16 are nonzero (B is zero there)\n", nonzero_tail);
  const Layout all[] = {Layout::A23, Layout::Swapped, Layout::UnpackedLo, Layout::UnpackedHi};
  bool a23 = false, any = false;
  for (Layout l : all) {
    bool match = true;
    for (uint32_t m = 0; m < 2; ++m)
      for (uint32_t k = 0; k < 16; ++k) {
        const Slot s = decode_value(f32_value(d[m * 128 + k])), want = predicted(l, m, k);
        match = match && s.col == want.col && s.half == want.half;
      }
    if (match && !inconsistent && !nonzero_tail) {
      std::printf("    decode: the map is layout %s, row i = lane i\n", layout_name(l));
      a23 = a23 || l == Layout::A23;
      any = true;
    }
  }
  if (!any) std::printf("    decode: the map matches no layout hypothesis; read it above\n");
  return a23 ? kPass : kFail;
}

}  // namespace

int main() {
  if (!layouts_selftest()) {
    std::printf("FAIL    h1 host layout self-test\n");
    return 1;
  }
  const Layout layouts[] = {Layout::A23, Layout::Swapped, Layout::UnpackedLo, Layout::UnpackedHi};
  int controls = 0, dec = 0;
  controls |= run_case("h1", "control-perm", [] { return control(true); });
  controls |= run_case("h1", "control-int", [] { return control(false); });
  dec = run_case("h1", "decode", decode);
  std::vector<std::string> matching;
  for (Layout l : layouts) {
    const int a = run_case("h1", std::string(layout_name(l)) + "-perm", [l] { return full(l, true); });
    const int b = run_case("h1", std::string(layout_name(l)) + "-int", [l] { return full(l, false); });
    if (a == kPass && b == kPass) matching.push_back(layout_name(l));
  }
  std::printf("-- h1 summary: controls %s; decode %s; layouts that pass:", controls ? "FAILED" : "pass",
              outcome_name(dec));
  for (auto &m : matching) std::printf(" %s", m.c_str());
  if (matching.empty()) std::printf(" none");
  std::printf("\n");
  const bool a23 = !matching.empty() && matching[0] == "a23";
  if (controls) std::printf("-- h1 verdict: INCONCLUSIVE (the shared-memory control failed)\n");
  else if (a23 && dec == kPass) std::printf("-- h1 verdict: A23 HOLDS\n");
  else if (a23) std::printf("-- h1 verdict: INCONCLUSIVE (the a23 products pass, but decode is %s; see its output)\n",
                            outcome_name(dec));
  else if (!matching.empty()) std::printf("-- h1 verdict: A23 FALSE; the layout is %s\n", matching[0].c_str());
  else std::printf("-- h1 verdict: A23 FALSE and no variant matches: P through shared memory (ATTENTION.md 2.3)\n");
  return !controls && a23 && dec == kPass ? 0 : 1;
}
