// H2 (gpu/ATTENTION.md §4.4), assumption A24: an MN-major B operand from shared memory.
//
// Question. For the second product Ô += P·V, B's element (k, n) is V[k][n], stored with n (the head dimension)
// contiguous, as the V ring's two 64-wide boxes of 128 key rows lay it down. Does the instruction descriptor's
// "transpose B" bit (bit 16) with the shared-memory descriptor LBO = 16384 (between the two 64-element halves of N),
// SBO = 1024 (between groups of 8 rows of K) and 128-byte swizzle, the start advanced 2048 bytes per K = 16 step and
// base offset 0, read B as the canonical MN-major layout ((T,8,m),(8,k)):((1,T,LBO),(8T,SBO))?
//
// PTX ISA 9.4: §9.7.18.3.1–3 (shared-memory matrix layouts, the canonical layouts); §9.7.18.4.1 (shared-memory
// descriptor, Table 50); §9.7.18.4.2 (instruction descriptor, Table 51: bit 16 transpose B); §9.7.18.10.3 (Table 65:
// 16-bit B may be MN-major with 128-byte swizzle); §9.7.18.10.10.1 `tcgen05.mma`.
//
// A is 128 × 128 in shared memory, K-major (TinyGEMM's layout and descriptors), as Q is in the first product. Eight
// K = 16 MMAs cover K = 128, so SBO and the K step are exercised across all 16 groups of 8 rows, and N = 128 spans
// both boxes, so LBO is exercised. Cases (each in its own process), each with B a permutation (and A with distinct
// entries per row, so a wrong element names the k it came from) and B a general integer matrix:
//   control   B stored K-major (Bᵀ, TinyGEMM's path), transpose bit clear. Checks the probe itself.
//   a24       B MN-major, transpose bit set, LBO 16384, SBO 1024 (the design).
//   swapped   B MN-major, transpose bit set, LBO 1024, SBO 16384 (the roles exchanged, as PTX has them for the
//             non-swizzled MN-major layout).
//
// Outcomes. control fails: the probe is wrong. a24 passes: A24 holds; the V ring needs no transpose and `mmaPV…`
// uses these descriptors. swapped passes instead: the design's LBO and SBO are exchanged. Neither: the permutation
// cases print, for row 0, which k each column of D came from, which localizes the error (a wrong LBO scrambles the
// upper half of N, a wrong SBO or K step the key order); V could still be transposed on the way in (a K-major V needs
// another TMA layout or an in-kernel transpose).
//
// Build and run (exit status 0 only when control and a24 pass):
//   nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a h2_mn_major_b.cu -o h2_mn_major_b && ./h2_mn_major_b
#include "probe.h"

using namespace probe;

namespace {

enum class Variant { Control, A24, Swapped };

const char *variant_name(Variant v) {
  switch (v) {
    case Variant::Control: return "control";
    case Variant::A24: return "a24";
    case Variant::Swapped: return "swapped";
  }
  return "?";
}

constexpr uint32_t kB = 32768;  // image byte of B; A (128 × 128 K-major, 32768 bytes) is at 0

int run(Variant variant, bool perm) {
  Matrix a(128, 128), b(128, 128);  // b is B itself: K × N, D = A·B
  if (perm) {
    a = code_matrix();
    for (uint32_t n = 0; n < 128; ++n) b.at(sigma(n), n) = 1.0f;  // D[i][n] = A[i][σ(n)]
  } else {
    Lcg g{777};
    for (float &x : a.v) x = g.quarter();
    for (float &x : b.v) x = g.small_int();
  }
  Image image(2 * 32768);
  image.put_kmajor(0, a);
  if (variant == Variant::Control) image.put_kmajor(kB, transpose(b));
  else image.put_mnmajor(kB, b);

  Plan plan;
  std::memset(&plan, 0, sizeof plan);
  plan.tmem_cols = 128;
  plan.image_bytes = uint32_t(image.bytes.size());
  plan.n_mma = 8;
  for (uint32_t s = 0; s < 8; ++s) {
    Mma &m = plan.mma[s];
    m.d_col = 0;
    m.a_off = kmajor_step(0, 128, s);
    m.a_sbo = 1024;
    m.accumulate = s > 0;
    if (variant == Variant::Control) {
      m.b_off = kmajor_step(kB, 128, s);
      m.b_sbo = 1024;
      m.idesc = idesc_bf16(128, 128, false);
    } else {
      m.b_off = kB + 2048 * s;
      m.b_lbo = variant == Variant::A24 ? 16384 : 1024;
      m.b_sbo = variant == Variant::A24 ? 1024 : 16384;
      m.idesc = idesc_bf16(128, 128, true);
    }
  }
  plan.n_ld = 1;
  plan.ld[0] = Region{0, 128, 8, 0};
  std::vector<uint32_t> d;
  if (!run_plan(plan, image, {}, 128 * 128, d)) return kError;

  const Matrix want = product_abt(a, transpose(b));
  if (!perm) return compare_d(d, 0, 128, 0, want, no_explanation) ? kFail : kPass;
  const size_t bad = compare_d(d, 0, 128, 0, want, [](uint32_t i, uint32_t n, float v) {
    std::printf(" (A[%u][k] for k = %d; B selects k = %u)", i, code_k(i, v), sigma(n));
  });
  if (bad) {
    std::printf("    row 0, n: k read (k wanted):");
    const uint32_t ns[] = {0, 1, 7, 8, 9, 63, 64, 65, 72, 127};
    for (uint32_t n : ns) std::printf(" %u:%d(%u)", n, code_k(0, f32_value(d[n])), sigma(n));
    std::printf("\n");
  }
  return bad ? kFail : kPass;
}

}  // namespace

int main() {
  if (!layouts_selftest()) {
    std::printf("FAIL    h2 host layout self-test\n");
    return 1;
  }
  const Variant variants[] = {Variant::Control, Variant::A24, Variant::Swapped};
  bool pass[3] = {false, false, false};
  for (int i = 0; i < 3; ++i) {
    const Variant v = variants[i];
    const int p = run_case("h2", std::string(variant_name(v)) + "-perm", [v] { return run(v, true); });
    const int q = run_case("h2", std::string(variant_name(v)) + "-int", [v] { return run(v, false); });
    pass[i] = p == kPass && q == kPass;
  }
  if (!pass[0]) std::printf("-- h2 verdict: INCONCLUSIVE (the K-major control failed)\n");
  else if (pass[1]) std::printf("-- h2 verdict: A24 HOLDS\n");
  else if (pass[2]) std::printf("-- h2 verdict: A24 FALSE; LBO and SBO are exchanged (LBO 1024, SBO 16384)\n");
  else std::printf("-- h2 verdict: A24 FALSE and the swapped variant fails too; see the k maps above\n");
  return pass[0] && pass[1] ? 0 : 1;
}
