# Checking cost, and what to port from `main-new`

**Status: 2026-10-30. Findings and proposals, none adopted.** This comes
from profiling the GPU experiment's slowest module, and from comparing
`main-new` with `main-clean` feature by feature; the two branches share no
history. The two correctness ports below are taken into the kernel
follow-ups. The rest await a decision.

## 1 Why `GpuClientFootprint` takes 11.8 s

It was measured at `78a5f3a6`, using JFR, call counters and a width sweep.

- **Where the time goes.** The module checks in 13.4–14.4 s on this machine.
  12.3 s of that is one definition, `source_and_destination_disjoint`.
  - While it is checked, the evaluator makes 19.0M proof-valued calls,
    against 1.5M data-valued ones.
  - It runs 14.1M matches on proof scrutinees.
  - 91% of the time is `Exclusive.reach_good`, which recomputes the quadratic
    `Nodup` invariant through `Nodup.perm` → `Pairwise.perm` → `Every.perm`
    along the 140-step trace. Another 8% is `Morphism.transport`.
- **How it scales.** The time grows as W^3.2 in the tile width W: 0.26 s at
  W = 8 and 12.3 s at W = 32.
- **What it is not.** `Protocol.step` is called zero times, because this
  module holds no tokens, so the earlier explanation in `KERNEL_FOLLOWUPS.md`
  §4 was wrong. Conversion, termination checking, refinement and Nat normal
  forms cost about nothing. Binding arguments and environments in the
  interpreter is 56% of the profile.
- **The root cause.** Checking evaluates call by value, and it runs every
  checked lambda, even one whose function type is a proposition. Conversion
  never inspects a proof, since proof irrelevance decides first. Only a few
  things ever need a proof's form:
  - a match on it;
  - the checker's known-constructor view;
  - the termination checker's key test;
  - the printed program result.

  Here nothing needs it. The result is a stuck proof of `False`, after about
  19M wasted proof calls.

## 2 Fixes for checking cost

1. **Suspend proof-valued calls.** Prototyped on branch
   `prototype/proof-suspension`, commit `d736c840`, not for merge.
   - **The rule.** A call to a checked lambda whose function type is a
     proposition becomes a memoized suspension. It runs only when one of the
     consumers above demands it.
   - **Two changes from `main-new`'s rule** (its `404033b1`, which is not on
     `origin/main-new`). The suspension's proposition is computed lazily, and
     a demanded proof runs eagerly inside. Both are needed: with eager
     propositions, `GpuCounterexample` takes 6.5 s instead of 1.8 s.
   - **Results:**

     | | Before | With the prototype |
     |---|---|---|
     | `GpuClientFootprint` | 13.4–14.4 s | 1.15 s, flat in W |
     | `GpuClient` | 1.83 s | 1.21 s |
     | an exponential proof, burn(26) | 31.6 s | 0.57 s |
     | the Abel–Coquand example | crashes | accepted |
     | GPU verifier | 32/32 | 32/32 |
     | test suite | — | 661/661 |

   - **For production:** the prototype marks a suspension as a `VApp` with a
     null type. Production needs a proper value form and an audit of the six
     sites that destructure `VApp`.
   - **Risk:** medium-low. A demanded proof reaches the same weak head normal
     form as before.
2. **Drop the duplicate environment instantiation in `evalApply` for
   lambdas.** It has no semantic effect, and measured −17% with eager proofs.
3. **Cheaper environment binding.** This is the case-class copy and
   `Vector :+` per local, the rebuilt wrapper, and `zip` and `foldLeft` in
   `instantiateFull`: about 55% of the eager profile. `main-new`'s prepared
   frames are the full version. Not measured.
4. **A policy question, not prototyped: keep a match from a suspended proof
   into `Prop` suspended.** Proofs that are demanded only for small
   elimination would then cost nothing. But the checker's known-constructor
   path would then require every case that is reachable by type, and fields
   would become fresh variables.

## 3 Candidates from `main-new`

These are already settled and not reassessed:
- **Already on `main-clean`:** Prop separation (`cd8e8a30`).
- **Decided ports:** structure eta, wildcard cases, match equations,
  declaration-time positivity, mutual families.
- **Skipped:** features tied to sealing, lifetimes and scopes, the old
  linearity rules, quotients, or native buffers.

| # | Candidate | Class | Evidence in `main-clean` | Recommendation | Size |
|---|---|---|---|---|---|
| 1 | Suspend proof calls (§2) | performance, robustness | missing; reproduced | adapt, as prototyped | 150–250 lines |
| 2 | Apply a stuck head (a stuck `VApp`, `NeutralThunk` or `Var`) | correctness | `g(k)(2)` for an axiom `g` gives "Cannot apply non-fn type" | port. Taken into the follow-ups as 1.3, fixed by structure eta | ~20 |
| 3 | Branch fields typed at the scrutinee's parameters (`f598d033`) | correctness | a `Vec(A, f(n))` match gives "expected A#3608, actual A#3614" | port. Ported as follow-up 1.5 | 60–120 |
| 4 | `EvaluationTooDeep` on a dedicated stack thread (`5bfa2234`) | robustness | `count(20000)` exits with a bare `StackOverflowError` | port | ~100 |
| 5 | Tail positions run in a loop (`9141fea2`) | performance, robustness | no tail loop; `count(100000)` overflows a 64 MB stack | port the loop, not the frame machine | 150–250 |
| 6 | Memoized materialization (`32b2112c`) | performance | a shared 24-level tree takes 5.7 s, against a 0.6 s control | port | 60–100 |
| 7 | Singleton view of an opaque proof (`6692800b`) | completeness | `castNat(h, x) ≡ x` is rejected for a variable `h` | adapt, only after #1 | 200–300 |
| 8 | Refinement certificates (`2a4f05ad`, `ee2f57e0`) | defence in depth | no wrong `Contradiction` found | defer | ≥1,000 |
| 9 | Function types printed in diagnostics | quality of life | "expected VPi, actual VPi" | port. Part of the follow-ups' diagnostics (ported 2026-10-30) | ~40 |
| 10 | Parser layout: comments and blank lines in blocks, `decreases` on the next line | quality of life | parse errors print parser objects | adapt. Part of the follow-ups' parser items (ported 2026-10-30) | 150–400 |
| 11 | Key-coherence assertion (`51e5a497`, `60487552`) | defence in depth | no incoherence found | optional | ~150 |
| 12–14 | Value metadata, result-type caching, interning, bytecode, evidence arguments | performance, features | tied to `main-new`'s representation | skip; re-measure after #1, #5 and #6 | large |

## 4 Proposed next steps

- **In the kernel follow-ups:** #2, #3, and the parts of #9 and #10 that the
  follow-ups list.
- **On a separate performance branch, after your decision:**
  1. #1, as a proper value form, with the prototype as reference;
     *Status: done on `perf-evaluation`, as `Value.VProofCall` (kernel.md,
     "Proof calls"). The prototype's over-approximated dependencies changed
     an occurs check, so the decisions they make conservative confirm them
     through forced values. `GpuClientFootprint` 16.1 s → 1.5 s.*
  2. #2 of §2, the environment instantiation;
     *Status: done on `perf-evaluation`: `evalApply` instantiates a function
     type only for a head that is no lambda, whose application's type needs
     it. With proofs suspended, it saves little (`GpuClient` 1.37 s → 1.31 s).*
  3. #4, #5 and #6;
     *Status of #4: done on `perf-evaluation`: the CLI runs on a `--stack`
     thread, 256 MB by default, and an overflow is `EvaluationTooDeep` at the
     declaration or the body, printing the result included.*
  4. then re-measure, and decide on #7 and on §2's policy question 4.
