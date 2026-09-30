// H3 (gpu/ATTENTION.md §4.4), assumption A27: column alignment of tensor-memory addresses.
//
// Question. May `tcgen05.mma`'s D address, its tensor-memory A address, and a `tcgen05.ld`/`tcgen05.st` address start
// at any column that is a multiple of 64 (the design uses 0, 128, 256 and 384 for S, Ô and P, and 8-column steps
// within P)? And at multiples of 32? PTX's text states the addressing (lane << 16 | column) and the allocation unit
// (32 columns), but no alignment rule for these addresses that the design found.
//
// PTX ISA 9.4: §9.7.18.1.1 (tensor-memory addressing); §9.7.18.1.2 (allocation: 32 to 512 columns, a power of two);
// §9.7.18.8.3 `tcgen05.ld`, §9.7.18.8.4 `tcgen05.st` (the .32x32b shape, .x4, .x8 and .x32); §9.7.18.8.5 `tcgen05.wait`;
// §9.7.18.10.10.1 `tcgen05.mma`; §9.7.18.6.4.4 (store, then MMA from another thread).
//
// All 512 columns are allocated, and every column not under test holds a background word naming its lane and column,
// so a write that lands in the wrong place, or a read from the wrong place, shows. Cases (each in its own process, so
// a fault raised by the hardware ends only its case, and is reported with the stage the kernel reached):
//   ldst.x32@c  for c in 0, 32, 64, 96, 128, 256, 384: one .x32 store at column c, the rest by .x8 stores at
//               multiples of 8; all 512 columns read back by .x8 loads, and [c, c + 32) again by one .x32 load at c.
//   ldst.x4@c   for c in 388, 444: the same with one .x4 store and load, at 4-column offsets inside P's columns, as
//               `storeP` writes P (ATTENTION.md §3.4); the background around it by .x4 stores.
//   mmaD@c      for c in 0, 32, 64, 96, 128, 256, 384: D = A·Bᵀ (A, B in shared memory, K-major, K = 64: TinyGEMM's
//               path) written at column c over the background; all 512 columns read back. D must occupy exactly
//               [c, c + 128).
//   mmaA@c      for c in 256 (first: the baseline), 128, 160, 192, 224, 384, 448: A (128 × 128 bf16) in tensor
//               memory at column c, packed as A23 says (two per column, lower k low, 8 columns per K = 16 step), D at
//               column 0. When the baseline fails, A23 itself is in doubt (H1 says), and the A cases are reported
//               INCONCLUSIVE rather than as alignment failures.
// Every background and marker word also carries the case's number, since tensor memory keeps an earlier case's words.
//
// Outcomes. Every case at an offset the design uses (a multiple of 64, and the .x4 offsets) passes: A27 holds as the
// design uses it. A multiple-of-32 offset failing (32, 96, 160, 224) does not affect A1, but `splitTmem` (§3.1) must
// then require multiples of 64, not 32. A case the design relies on failing: the tensor-memory map of §2.2 must move
// to the offsets that work, and the case's output (an error and the stage reached, or where the data landed) says
// what went wrong.
//
// Build and run (exit status 0 only when the baseline and every case at an offset the design uses pass):
//   nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a h3_tmem_align.cu -o h3_tmem_align && ./h3_tmem_align
#include "probe.h"

using namespace probe;

namespace {

constexpr uint32_t kCols = 512;

// The case's number, cycling through 1 to 15 so that consecutive cases differ, in bits 24–27 of every background and marker word, so a store that is silently dropped
// cannot be hidden by the identical word an earlier case left in tensor memory (which is not cleared between
// processes).
uint32_t g_salt = 0;

// The background word at lane r, column c, and the marker the tested store writes: neither a code any other case
// writes, and both name their place.
uint32_t background(uint32_t r, uint32_t c) { return 0xB0000000u | (g_salt << 24) | (r << 16) | c; }
uint32_t marker(uint32_t r, uint32_t c) { return 0xC0000000u | (g_salt << 24) | (r << 16) | c; }

// Store regions covering all 512 columns: background everywhere except [from, from + len), which holds `inner` and
// is written by instructions `inner_width` wide. The background goes in .x8 stores where its region allows, else .x4.
// Adds the regions to `plan` and their words to `words`.
template <class Inner>
void cover(Plan &plan, std::vector<uint32_t> &words, uint32_t from, uint32_t len, uint32_t inner_width, Inner inner) {
  auto add = [&](uint32_t col, uint32_t ncols, uint32_t width, auto value) {
    if (ncols == 0) return;
    plan.st[plan.n_st++] = Region{col, ncols, width, uint32_t(words.size())};
    for (uint32_t r = 0; r < 128; ++r)
      for (uint32_t j = 0; j < ncols; ++j) words.push_back(value(r, col + j));
  };
  add(0, from, from % 8 ? 4 : 8, background);
  add(from, len, inner_width, inner);
  add(from + len, kCols - from - len, (from + len) % 8 ? 4 : 8, background);
}

Plan empty_plan(uint32_t image_bytes) {
  Plan plan;
  std::memset(&plan, 0, sizeof plan);
  plan.tmem_cols = kCols;
  plan.image_bytes = image_bytes;
  plan.n_ld = 1;
  plan.ld[0] = Region{0, kCols, 8, 0};
  return plan;
}

// Checks the 512-column readback: `expect_d` (a D matrix at `d_col`, compared by value) where given, `inner` on
// [from, from + len), and the background everywhere else (compared by bits).
template <class Inner>
size_t check_columns(const std::vector<uint32_t> &got, const Matrix *d, uint32_t d_col, uint32_t from, uint32_t len,
                     Inner inner) {
  size_t bad = 0;
  if (d) bad += compare_d(got, 0, kCols, d_col, *d, no_explanation);
  for (uint32_t r = 0; r < 128; ++r)
    for (uint32_t c = 0; c < kCols; ++c) {
      if (d && c >= d_col && c < d_col + d->cols) continue;
      const uint32_t want = c >= from && c < from + len ? inner(r, c) : background(r, c);
      const uint32_t word = got[size_t(r) * kCols + c];
      if (word == want) continue;
      if (bad < 8) {
        std::printf("    lane %u column %u = 0x%08x, want 0x%08x", r, c, word, want);
        if ((word >> 28) == 0xB || (word >> 28) == 0xC)
          std::printf(" (the %s word of lane %u column %u, case %u)", (word >> 28) == 0xB ? "background" : "marker",
                      (word >> 16) & 0x7F, word & 0xFFFF, (word >> 24) & 0xF);
        std::printf("\n");
      }
      ++bad;
    }
  return bad;
}

// One store `width` columns wide (.x4 or .x32) at column c, and one load of the same width there.
int ldst(uint32_t c, uint32_t width) {
  Image image(0);
  Plan plan = empty_plan(0);
  std::vector<uint32_t> words;
  cover(plan, words, c, width, width, marker);
  plan.n_ld = 2;
  plan.ld[1] = Region{c, width, width, 128 * kCols};
  std::vector<uint32_t> got;
  if (!run_plan(plan, image, words, 128 * kCols + 128 * width, got)) return kError;
  size_t bad = check_columns(got, nullptr, 0, c, width, marker);
  for (uint32_t r = 0; r < 128; ++r)
    for (uint32_t j = 0; j < width; ++j) {
      const uint32_t word = got[128 * kCols + r * width + j];
      if (word == marker(r, c + j)) continue;
      if (bad < 8)
        std::printf("    .x%u load at %u: lane %u word %u = 0x%08x, want 0x%08x\n", width, c, r, j, word, marker(r, c + j));
      ++bad;
    }
  if (bad) std::printf("    %zu words wrong\n", bad);
  return bad ? kFail : kPass;
}

int mma_d(uint32_t c) {
  Lcg g{31 + c};
  Matrix a(128, 64), bt(128, 64);
  for (float &x : a.v) x = g.quarter();
  for (float &x : bt.v) x = g.small_int();
  Image image(2 * 16384);
  image.put_kmajor(0, a);
  image.put_kmajor(16384, bt);
  Plan plan = empty_plan(uint32_t(image.bytes.size()));
  std::vector<uint32_t> words;
  cover(plan, words, 0, 0, 8, background);
  plan.n_mma = 4;
  for (uint32_t s = 0; s < 4; ++s) {
    Mma &m = plan.mma[s];
    m.d_col = c;
    m.a_off = kmajor_step(0, 128, s);
    m.a_sbo = 1024;
    m.b_off = kmajor_step(16384, 128, s);
    m.b_sbo = 1024;
    m.idesc = idesc_bf16(128, 128, false);
    m.accumulate = s > 0;
  }
  std::vector<uint32_t> got;
  if (!run_plan(plan, image, words, 128 * kCols, got)) return kError;
  const Matrix d = product_abt(a, bt);
  const size_t bad = check_columns(got, &d, c, 0, 0, background);
  if (bad) std::printf("    %zu words wrong\n", bad);
  return bad ? kFail : kPass;
}

int mma_a(uint32_t c) {
  Lcg g{57 + c};
  Matrix p(128, 128), bt(128, 128);
  for (float &x : p.v) x = g.quarter();
  for (float &x : bt.v) x = g.small_int();
  Image image(32768);
  image.put_kmajor(0, bt);
  auto packed = [&p, c](uint32_t r, uint32_t col) {
    const uint32_t j = col - c;
    return uint32_t(bf16_bits(p.at(r, 2 * j))) | (uint32_t(bf16_bits(p.at(r, 2 * j + 1))) << 16);
  };
  Plan plan = empty_plan(uint32_t(image.bytes.size()));
  std::vector<uint32_t> words;
  cover(plan, words, c, 64, 8, packed);
  plan.n_mma = 8;
  for (uint32_t s = 0; s < 8; ++s) {
    Mma &m = plan.mma[s];
    m.d_col = 0;
    m.a_tmem = 1;
    m.a_col = c + 8 * s;
    m.b_off = kmajor_step(0, 128, s);
    m.b_sbo = 1024;
    m.idesc = idesc_bf16(128, 128, false);
    m.accumulate = s > 0;
  }
  std::vector<uint32_t> got;
  if (!run_plan(plan, image, words, 128 * kCols, got)) return kError;
  const Matrix d = product_abt(p, bt);
  const size_t bad = check_columns(got, &d, 0, c, 64, packed);
  if (bad) std::printf("    %zu words wrong\n", bad);
  return bad ? kFail : kPass;
}

}  // namespace

int main() {
  if (!layouts_selftest()) {
    std::printf("FAIL    h3 host layout self-test\n");
    return 1;
  }
  int required_failures = 0;
  std::string works, fails;
  uint32_t salt = 0;
  // Runs a case with the next salt; `required`: the design relies on it (A27), so a failure fails the probe.
  auto run = [&](const std::string &name, bool required, auto body) {
    salt = salt % 15 + 1;
    const uint32_t this_salt = salt;
    const int outcome = run_case("h3", name, [&] {
      g_salt = this_salt;
      return body();
    });
    (outcome == kPass ? works : fails) += " " + name;
    if (required && outcome != kPass) ++required_failures;
    return outcome;
  };
  const uint32_t offsets[] = {0, 32, 64, 96, 128, 256, 384};
  for (uint32_t c : offsets) run("ldst.x32@" + std::to_string(c), c % 64 == 0, [c] { return ldst(c, 32); });
  // `storeP` writes P with .x4 stores at 384 + 4c (ATTENTION.md §3.4).
  const uint32_t x4_offsets[] = {388, 444};
  for (uint32_t c : x4_offsets) run("ldst.x4@" + std::to_string(c), true, [c] { return ldst(c, 4); });
  for (uint32_t c : offsets) run("mmaD@" + std::to_string(c), c % 64 == 0, [c] { return mma_d(c); });
  // The A cases pack A as A23 says. mmaA@256 is their baseline: when it fails, A23 itself is in doubt (see H1), and
  // the other A cases say nothing about alignment, so none of them counts.
  const bool a_baseline = run("mmaA@256", false, [] { return mma_a(256); }) == kPass;
  std::string inconclusive;
  const uint32_t a_offsets[] = {128, 160, 192, 224, 384, 448};
  for (uint32_t c : a_offsets) {
    const std::string name = "mmaA@" + std::to_string(c);
    const int outcome = run(name, a_baseline && c % 64 == 0, [c] { return mma_a(c); });
    if (!a_baseline && outcome != kPass) inconclusive += " " + name;
  }
  if (!a_baseline) {
    std::printf("-- h3 the A-in-tensor-memory cases are INCONCLUSIVE: the baseline mmaA@256 failed, so A23's packing is "
                "wrong or A in tensor memory fails outright (see H1); inconclusive:%s\n",
                inconclusive.empty() ? " none" : inconclusive.c_str());
  }
  std::printf("-- h3 works:%s\n-- h3 fails:%s\n", works.empty() ? " none" : works.c_str(),
              fails.empty() ? " none" : fails.c_str());
  const char *d_and_ldst = required_failures ? "FALSE at some offset the design uses (see above)" : "HOLDS";
  if (!a_baseline) std::printf("-- h3 verdict: A27 %s for D and ld/st; UNSETTLED for A operands\n", d_and_ldst);
  else std::printf("-- h3 verdict: A27 %s\n", d_and_ldst);
  return required_failures || !a_baseline ? 1 : 0;
}
