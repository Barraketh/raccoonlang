// H5 (gpu/ATTENTION.md §4.4): the tensor cores' f32 accumulation error, which T1's score term assumes (§1.3).
//
// Question. §1.3 bounds the error of the scores `Q·Kᵀ` summed in f32 over 128 products as a sequential f32 sum's:
// |S − S_exact| ≤ 127 · 2⁻²⁴ · Σ_d |q·k| (to first order). How the tensor cores round within and between K = 16 steps
// is not specified. Is the bound met, and how far inside it are they?
//
// PTX ISA 9.4: §9.7.18.10.10.1 `tcgen05.mma` (kind::f16, f32 accumulation); the rounding of the accumulation is not
// specified there. The operands' products are exact in f32 (8 + 8 significant bits).
//
// Cases (each in its own process): S = Q·Kᵀ, 128 × 128 × 128, both K-major in shared memory (TinyGEMM's path, eight
// K = 16 MMAs, the first overwriting), Q and K random bf16 over §1.3's ranges:
//   uniform  Q and K in [−1, 1]
//   peaked   Q in [−8, 8], K in [−1, 1]
// four seeds each. The reference is exact (a double sum of exact products, bf16 · bf16 having 16 significant bits,
// is exact to well below the errors measured). Printed per case: the maximum and mean of |S − ref| / Σ|q·k| in units of
// 2⁻²⁴ (the tensor cores, and for comparison a sequential f32 sum and a pairwise one on the host); the maximum and mean
// relative error |S − ref| / |ref| over elements whose |ref| ≥ 2⁻⁶ · Σ|q·k| (so cancellation does not dominate);
// the mean signed error in the same units (a truncating accumulator shows as a bias toward zero, reported as the mean
// of (S − ref)·sign(ref)).
//
// Outcomes. PASS: every element within 128 · 2⁻²⁴ · Σ|q·k|, so §1.3's score term stands. FAIL: T1's bound for O
// must be rederived with the measured constant (its margin is 2⁻⁷ − 0.0067 ≈ 0.0011 · max|V|).
//
// Build and run (exit status 0 when both cases pass):
//   nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a h5_accum_error.cu -o h5_accum_error && ./h5_accum_error
#include "probe.h"

#include <cmath>

using namespace probe;

namespace {

struct Stats {
  double max_ulps = 0, sum_ulps = 0, max_rel = 0, sum_rel = 0, sum_signed = 0;
  size_t n = 0, n_rel = 0;
  void add(double got, double ref, double mag) {
    const double e = std::fabs(got - ref) / (mag * std::ldexp(1.0, -24));
    max_ulps = std::max(max_ulps, e);
    sum_ulps += e;
    sum_signed += (got - ref) * (ref < 0 ? -1 : 1) / (mag * std::ldexp(1.0, -24));
    ++n;
    if (std::fabs(ref) >= std::ldexp(mag, -6)) {
      const double r = std::fabs(got - ref) / std::fabs(ref);
      max_rel = std::max(max_rel, r);
      sum_rel += r;
      ++n_rel;
    }
  }
  void print(const char *what) const {
    std::printf("    %-14s |err|/sum|qk|: max %7.2f, mean %6.3f (2^-24); signed mean %+7.3f; relative: max %.3g, mean %.3g "
                "(over %zu elements)\n",
                what, max_ulps, sum_ulps / double(n), sum_signed / double(n), max_rel, n_rel ? sum_rel / double(n_rel) : 0.0,
                n_rel);
  }
};

float pairwise(const float *x, uint32_t n) { return n == 1 ? x[0] : pairwise(x, n / 2) + pairwise(x + n / 2, n - n / 2); }

int run(float q_range) {
  Stats tc, seq, pair;
  for (uint32_t seed = 1; seed <= 4; ++seed) {
    Lcg g{seed * 2654435761u + uint32_t(q_range)};  // distinct seeds per range: scaling by 8 alone is exact
    Matrix q(128, 128), k(128, 128);
    for (float &x : q.v) x = g.uniform_bf16(q_range);
    for (float &x : k.v) x = g.uniform_bf16(1.0f);
    Image image(2 * 32768);
    image.put_kmajor(0, q);
    image.put_kmajor(32768, k);
    Plan plan;
    std::memset(&plan, 0, sizeof plan);
    plan.tmem_cols = 128;
    plan.image_bytes = uint32_t(image.bytes.size());
    plan.n_mma = 8;
    for (uint32_t s = 0; s < 8; ++s) {
      Mma &m = plan.mma[s];
      m.a_off = kmajor_step(0, 128, s);
      m.a_sbo = 1024;
      m.b_off = kmajor_step(32768, 128, s);
      m.b_sbo = 1024;
      m.idesc = idesc_bf16(128, 128, false);
      m.accumulate = s > 0;
    }
    plan.n_ld = 1;
    plan.ld[0] = Region{0, 128, 8, 0};
    std::vector<uint32_t> d;
    if (!run_plan(plan, image, {}, 128 * 128, d)) return kError;
    for (uint32_t i = 0; i < 128; ++i)
      for (uint32_t j = 0; j < 128; ++j) {
        double ref = 0, mag = 0;
        float s = 0, prod[128];
        for (uint32_t t = 0; t < 128; ++t) {
          prod[t] = q.at(i, t) * k.at(j, t);  // exact in f32
          ref += double(prod[t]);
          mag += std::fabs(double(prod[t]));
          s += prod[t];
        }
        if (mag == 0) continue;
        tc.add(f32_value(d[i * 128 + j]), ref, mag);
        seq.add(s, ref, mag);
        pair.add(pairwise(prod, 128), ref, mag);
      }
  }
  tc.print("tensor cores");
  seq.print("sequential f32");
  pair.print("pairwise f32");
  const bool ok = tc.max_ulps <= 128.0;
  std::printf("    bound 128 (2^-24 units): %s\n", ok ? "met" : "EXCEEDED");
  return ok ? kPass : kFail;
}

}  // namespace

int main() {
  if (!layouts_selftest()) {
    std::printf("FAIL    h5 host layout self-test\n");
    return 1;
  }
  const int a = run_case("h5", "uniform", [] { return run(1.0f); });
  const int b = run_case("h5", "peaked", [] { return run(8.0f); });
  std::printf("-- h5 verdict: %s\n", a == kPass && b == kPass ? "the 1.3 score bound HOLDS" : "see above");
  return a == kPass && b == kPass ? 0 : 1;
}
