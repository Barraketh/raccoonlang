# Refinement certificates

Status: **draft for review** (2026-09-30). Third of three specs, after `docs/PROP_SEPARATION.md` and
`docs/NOMINAL_FAMILIES.md`, whose principles N1–N3 it uses.

Dependent pattern matching draws two kinds of conclusion from unification:
- **Pruning.** A constructor whose equations are *apart* is unreachable, so its case is omitted. One wrong omission
  proves `False`.
- **Refinement.** A case is checked under the *links* unification made, each a definitional substitution `x := v`.
  One wrong link proves `Eq(T, x, v)` for values that differ, and so `False`.

Today both rest on the unifier being right: on its apartness rules, its classification of invertible frames, and their
interactions with quotients, proof irrelevance, universe polymorphism, packed literals and value keys. Six of the ten
soundness bugs in the project's log are in these rules. The five on the pruning side:
- Quot no-confusion;
- proof-constructor apartness;
- family-head apartness under propositional extensionality;
- the cross-family clash;
- the level-polymorphic clash.

The sixth, on the link side, is the solve/invert conflation. A seventh, large elimination from a level-polymorphic
family, is an elimination rule rather than a refinement rule; `PROP_SEPARATION` removes it.

This document takes them out of the trusted base. For every conclusion the match checker draws, it synthesizes a proof
term and type-checks it with the kernel's ordinary rules, then discards it: proofs are irrelevant, so only their
existence matters. The unifier stays as the search that proposes conclusions. When the proof cannot be built, the
conclusion is not drawn: the case is not pruned, or the link is not made. A bug in the unifier or in the synthesizer can
then only make the checker stricter.

## 1. The trusted statement

What a certificate must prove is the one part that stays trusted, so it is stated once and kept small.

Let a match have scrutinee `s : F(p̄, ī)`, and let `C` be a constructor of `F` with fresh fields `f̄` and result type
`F(p̄, j̄(f̄))`. The case for `C` may assume the **constructor hypothesis** `H_C`:

- **`F` a `Type` family:** one equation in the family's total space,
  ```text
  H_C : Eq(Σ(ī′: Idx(p̄)). F(p̄, ī′), ⟨ī, s⟩, ⟨j̄(f̄), C(p̄, f̄)⟩)
  ```
  where `Idx(p̄)` is the index telescope as nested `Sigma`s. Indices whose types are propositions are left out, since
  they are equal by proof irrelevance. With no indices, `H_C` is `Eq(F(p̄), s, C(p̄, f̄))`.
- **`F` a `Prop` family:** the index equation alone, `Eq(Idx(p̄), ī, j̄(f̄))`. The scrutinee is a proof, so its equation
  with `C(p̄, f̄)` holds by irrelevance.

`H_C` is homogeneous by construction: one equation, at one type. That is the reason for the total space. Dependent
elimination gives exactly this hypothesis (Lean's `cases` works over the same equation), so assuming it is justified by
the eliminator, and every conclusion below is justified by a proof from it.

## 2. Apartness certificates

**The rule.** Constructor `C` may be omitted when the checker exhibits a term of type

```text
(f̄: fields of C) -> H_C -> False
```

in the match's context. The case is then unreachable: in any instance, `H_C` would hold, and so `False`.

**Synthesis.** The certificate is built by a small structural procedure over `H_C`, separate from the unifier (§4). It
keeps a list of equations, each with a proof of it from `H_C`, and applies these rules:

| Rule | Equation | Step | Justified by |
|---|---|---|---|
| total space | `⟨a, b⟩ = ⟨a′, b′⟩` | `a = a′`, then `b = b′` once `a` and `a′` are convertible | `Sigma`'s injectivity; uniqueness of identity proofs for the second component |
| constructor injectivity | `D(ā) = D(b̄)`, same type | `ā = b̄` as a tuple, split by the total-space rule | `D`'s family's generated `noConfusion` (below) |
| constructor clash | `D(ā) = E(b̄)`, `D ≠ E`, same type | `False` | generated `noConfusion` |
| type-family injectivity | `G(ā) = G(b̄)`, `G` a `Type` family | `ā = b̄` | N1 |
| type clash | `G(ā) = G′(b̄)`, or two different forms | `False` | N2, N3 |
| literal | a packed `Nat` or `String` literal against a constructor or another literal | decode one layer, then the rules above | conversion (decoding is definitional) |
| solution | `x = v`, `x` a refinable local, `x ∉ v` | substitute `x := v` in the remaining equations, which transports their proofs | `Eq` elimination |
| deletion | `a = a′` convertible | drop | — |

Any other equation stops the procedure without a certificate. That covers:
- two neutral applications;
- lambdas;
- a `Prop`-family head nested in an index;
- the second component of a total space whose first components are not convertible (a heterogeneous equation);
- an opaque type.

**Generated `noConfusion`.** For each `Type` family with constructors, the declaration also generates, as ordinary
Raccoon definitions checked once at declaration:
- `F.noConfusionType : F(p̄, ī) -> F(p̄, ī′) -> Prop`, which gives the field equations (a total-space equation) for the
  same constructor and `False` for different ones;
- `F.noConfusion`, which turns an equation between two values into `F.noConfusionType` of them, by `Eq` elimination.

This is Lean's construction. It needs large elimination into `Prop`-the-sort, which every `Type` family has and no
`Prop` family has. That is the point: the conditions the apartness rules had to remember, and got wrong five times, are
now the typing rules for writing a discriminator:
- free constructors (`Quot.mk` has no `noConfusion`);
- data rather than proofs;
- values of one type;
- large elimination allowed.

The generated definitions are visible, so a user who must refute a case by hand can call them.

**What is not pruned.**
- **Failed synthesis.** A constructor whose certificate cannot be synthesized, or does not type-check, stays reachable.
  If the match has no case for it, that is `MissingCase`, and the user writes the case, refuting it with
  `F.noConfusion` if needed.
- **`UnreachableCase`.** A written case is reported unreachable only when its certificate checks.
- **The shortcut.** The constructor-form shortcut, which today marks every other constructor unreachable when the
  scrutinee is literally a constructor application, goes through the same rule. Its certificates are one constructor
  clash each.

## 3. Link certificates

**The rule.** A case may be checked under the link `x := v` when the checker exhibits a term of type

```text
(f̄: fields of C) -> H_C -> Eq(T, x, v)
```

in the match's context, where `T` is `x`'s type. Links are certified in the order they were made, each in the context
refined by the links before it.

**Why that is enough.** Given `e : Eq(T, x, v)` for a local `x`, a case body checked with `x` replaced by `v` becomes
a body for the case as written, by `Eq` elimination on `e` over `x`. That is the standard argument for the
"solution" step of dependent pattern matching. So a certified link adds nothing that `H_C` did not already give.

**Synthesis.** The same procedure as §2, stopping at the solution rule instead of a clash: the certificate for
`x := v` is the proof the procedure carries for the equation `x = v` when it reaches it. The procedure's own
solutions are the certified links. A link the unifier made but the procedure does not reach, for example one made
through a frame that is not a constructor or a `Type`-family head, is not certified.

**When a link cannot be certified,** the whole case falls back to no refinement, as a stuck unification does today.
The case is still checked, with no links. This is decision 2 below; per-link fallback is possible, but it has to drop
every later link that depends on the dropped one.

**What stays trusted.**
- **Links on levels, kinds and lifetimes.** They are not ordinary terms with an `Eq` to transport along. Their rules
  stay as `docs/kernel.md` states them: a variable alone on one side, not occurring on the other, with a solution that
  normalization forces.
- **Structure-eta expansion of a refinable variable.** Its link needs no certificate, since eta is definitional.

## 4. Where the unifier stands

`ValueEquivalence` is unchanged and still decides conversion, which is not refinement. For refinement, its verdicts
become proposals:
- **"Apart"** proposes that the procedure look for a certificate.
- **A store of links** proposes the links to certify.

Its apartness rules, invertible frames and fast paths stop being part of the trusted base. A mistake in them now costs
completeness only: an unpruned case, or a case checked without refinement.

Two designs:
- **Confirm** (proposed first). The unifier proposes and the procedure certifies. Behaviour is unchanged wherever
  certificates succeed.
- **Replace.** Refinement uses the procedure alone, and the unifier serves conversion only. This is simpler in the end,
  but refinement loses what the procedure does not do (postponement, eta, levels) unless the procedure grows it.

## 5. Measurement before enforcement

A shadow mode comes first. The checker synthesizes and type-checks every certificate, logs any failure, and enforces
nothing. It runs over the whole corpus (tests, `gpu/check.sh`, documentation) and reports:
- the number of pruned constructors and links;
- the fraction certified;
- each uncertified case with its reason;
- the added check time.

Enforcement follows only once the uncertified cases are either the unsound ones (the soundness regressions) or accepted
as a loss.

Expected coverage: the GPU proofs refine through `Eq` on data (`Nat`, `Bool`, `List(String)`) and prune on literal and
constructor clashes, all within the rules of §2. Heterogeneous index telescopes are the likely uncertified cases. The
measurement decides this.

## 6. Tests

- **Every existing soundness regression** passes with certificates enforced: Quot, proof constructors, family heads,
  cross-family clashes, level-polymorphic clashes, and solve/invert. Each is refused because no certificate exists,
  whatever the unifier says.
- **Fault injection.** A test-only switch makes the unifier call every constructor clash apart, and another makes it
  link through every head. With certificates enforced, the soundness regressions still hold, and the corpus's valid
  programs still check where their certificates exist.
- **Generated `noConfusion`** checks for every `Type` family in the corpus, and is absent for `Prop` families and
  quotients.
- **`MissingCase` fallback.** A case whose certificate cannot be built is required, and the user can close it by hand
  with `F.noConfusion`.
- **Link fallback.** A case whose link cannot be certified is checked unrefined.
- **Corpus:** `gpu/check.sh` green with byte-identical kernels, and the test suite green, except cases the measurement
  (§5) identified and this review accepted.

## 7. Steps

1. **C0, shadow mode.** The procedure, generated `noConfusion`, the shadow switch and the measurement report. No change
   to what checks.
2. **C1, apartness certificates enforced** (§2), with the constructor-form shortcut and `UnreachableCase` routed
   through them.
3. **C2, link certificates enforced** (§3).
4. **C3, documents.**
   - `docs/kernel.md`: "Refinement unification" states §1's hypothesis and the two certificate rules as the trusted
     statement.
   - "Apartness" becomes a description of the search.
   - "Nominal families" (from `NOMINAL_FAMILIES`) is cited as the principles certificates may use.

All steps are trusted-core changes: implementers at medium effort, hostile reviewers at high. C1 and C2 each end with a
fault-injection review, in which the reviewer's brief is to make a wrong proposal of the unifier's get through.

## 8. Decisions for review

1. **Confirm or replace** (§4): certify the unifier's proposals first, or build refinement on the procedure alone.
2. **Link fallback granularity** (§3): the whole case unrefined (proposed), or per link with dependent links dropped.
3. **Generated `noConfusion` visible** to users (proposed), or internal.
4. **Heterogeneous telescopes**: declined when an earlier type equation is stuck (proposed), rather than handled by a
   telescope-unification scheme such as Cockx and Devriese's "unifiers as equivalences". With N2 and N3, most such
   equations are refuted at the type equation anyway.
