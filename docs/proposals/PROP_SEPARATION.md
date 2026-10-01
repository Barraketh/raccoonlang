# Prop outside the universe hierarchy

Status: **draft for review** (2026-09-30). First of three specs for a safer kernel, with `docs/proposals/NOMINAL_FAMILIES.md`
(which builds on it) and `docs/proposals/REFINEMENT_CERTIFICATES.md` (which builds on both).

Today `Prop` is `Sort { level = Level.zero }`, the bottom of the universe hierarchy. A level variable may later be
instantiated to zero, so whether a type is a proposition is not always known when it is checked: `Option(A)` at
`A : Sort { level = u }` is data for some `u` and a proposition for `u := 0`. This document moves `Prop` out of the
hierarchy. Level variables range over data universes only, every family is declared either in `Prop` or in a `Type`,
and whether a type is a proposition is decided when the type is formed.

## 1. Why

**The third answer.** "Is this a proposition?" has three answers today: yes, no, and not until a level is chosen. Every
consumer of the answer must handle the third, and three soundness bugs came from one that treated it as "no":

| Bug | What happened |
|---|---|
| Prop-sort conflation (fixed 2026-07) | `(n: Nat) -> Prop` was classified as a proposition; predicates became proof-irrelevant; `False`. |
| Level-polymorphic clash (fixed on the unmerged branch `s1-prop-clash`) | `Sum.inl` against `Sum.inr` at `A : Sort u` counted as apart, but at `u = 0` they are equal proofs; `False`. |
| Level-polymorphic large elimination (open) | `Option.isSome` distinguishes `some` from `none` at `A : Sort u`; at `u = 0` both are the same erased proof; `False`. |

A fourth defect is a check/run incoherence rather than a proof of `False`: a level-polymorphic definition that checks
generically fails when run at a `Prop` instance, because an implicit read through a constructor field
(`telescope/Projection.scala`, the constructor-field step) meets an erased proof instead of a constructor.

**The reason for the design is gone.** `Prop` was a separate sort until commit `1635385` ("Move Prop into Sort",
2026-05-15). `Level.imax` (`5fb38da`, 2026-07-14) and blocking on levels that may collapse a type to a proposition
(`974e9f6`, 2026-07-16) followed for the Lean export, which was abandoned on 2026-09-16.

**The flexibility is unused.** An instrumented run of the whole test suite, `gpu/check.sh` (the GPU library and its
2,442 lines of proofs) and the documentation's examples logged every level instantiated to zero (§6).

## 2. Sorts

Two sort formers, both keywords:

```text
Type { level = e, kind = k, scope = S }   // data: level e, kind k, scope S; each field optional
Prop { scope = S }                        // propositions: scope S; no level, no kind
```

- `Type`'s omitted fields are `level = Level.zero`, `kind = Kind.unr`, `scope = Lifetime.empty`. So `Type` alone is
  today's `Type` (`Sort { level = Level.one }`), renumbered: **data levels start at zero**.
- `Prop` takes only `scope`. A `level` or `kind` field on `Prop` is a parse error: a proposition's proofs are always
  unrestricted.
- `Sort` is no longer a keyword. Every `Sort { level = e }` in today's sources becomes `Type { level = e′ }` (§6.2).
- Levels: `Level.zero`, `Level.one`, `Level.succ(e)`, `Level.max(e, e)` and variables. `Level.imax` is removed: it
  existed only to let a function type's level be zero when its codomain is.

Typing of sorts:

| Sort | Its type |
|---|---|
| `Prop { scope = S }` | `Type { scope = S }` |
| `Type { level = e, kind = k, scope = S }` | `Type { level = succ(e), scope = S }` |

`Prop` is a type (at level zero), so `Eq(Prop, P, Q)` and `P : Prop` binders are unchanged.

## 3. Function types

A function type's sort is decided by its codomain's sort, which is known when the type is formed:

- **Codomain in `Prop`:** the function type is in `Prop { scope = … }`, whatever its domain (impredicativity). Its
  closure kind must be `Kind.unr`. Its scope is computed as today.
- **Codomain in `Type { level = b }`:** the function type is in `Type { level = max(a, b), kind = …, scope = … }`,
  where `a` is the domain's level, or `Level.zero` when the domain is a proposition. Kind and scope are computed as
  today.

There is no conditional level: the "imax fold" over binder groups (`Interpreter.piClassifierFromChecked`), the cache
of classifications that cannot flip (`stablePiPropClassification`) and the per-instance `VPi.isPropValued` become one
Boolean fixed at formation.

## 4. Families

A family is declared in `Prop { … }` or in `Type { … }`. Its parameters and indices may be of any type.

- **Fields of a `Type` family** at level `ℓ`: a field whose type is at level `m` needs `m ≤ ℓ`, as today. A field whose
  type is a proposition fits any `Type` family (today this held because `0 ≤ ℓ`; now it is stated).
- **Fields of a `Prop` family:** any type, as today (impredicativity).
- **Elimination from a `Prop` family into a `Type` motive** is allowed only when the family satisfies the subsingleton
  rule (`MatchChecker.allowLargeElimination`). The test `Sorts.isProposition(scrutineeType)` is now exact, so the open
  large-elimination bug has no route left: there is no family whose instances may or may not be propositions.
- **Structure eta** is eligible for `Type` structs only, decided at declaration; the per-instance filter
  (`StructEta.eligibleInstance`) becomes a flag.
- **Evidence eligibility** (PROOF_BY_EVALUATION §1.9, "declared in `Prop` itself, not a level that may become zero")
  becomes "declared in `Prop`".
- **Linear kinds.** `Type { kind = lin }` is allowed at every level. The `LinearProp` rule ("a linear kind needs a level
  that is never zero") has nothing left to refuse, and `Pair`'s `succ` levels, there only to satisfy it, go.

A value is a proof exactly when its type is in `Prop`, which is known when its type is formed.

## 5. What goes and what stays

A survey of the implementation (2026-09-30, ~12.7k lines of kernel) classified every site that exists because `Prop`
is `Sort 0` or because a level may be zero:

| | Lines | What |
|---|---|---|
| **Removed** | ~120 | `Level.imax` and its normalization, keys, printing and `leq` bounds; `Level.isNeverZero`; `LinearProp`; `typeCollapseDeps` (a stuck match waiting on its type's levels); the destructuring case "checked outside `Prop` but evaluated where a level puts it in `Prop`"; the `s1-prop-clash` guard, which `ProofEquation` makes redundant once every proof's type is known to be a proposition |
| **Decided at formation or declaration** | ~210 | the `Prop` tag on sorts; function types' `Prop`-ness; a family's `mayBeProp`, field sources and proof-recovery plan; eta eligibility; sort syntax |
| **Unchanged** | ~780 | proof irrelevance, canonical proofs, erasure, reconstruction, discharge, the elimination restriction, apartness, the rest of the level algebra |

The level algebra (~290 lines) loses ~85. What is gained is not mostly lines: every consumer of "is this a
proposition" gets a two-valued answer that no later substitution changes, so re-canonicalizing a proof because a level
became zero, and the check/run gap of §1, cannot arise. (Re-canonicalizing a proof whose *proposition* sharpens, such
as `Eq.refl` reconstructed once its sides resolve, stays.)

New in the kernel (~60–100 lines): the `Prop` sort value (a scope only; keys and printing mix in the tag; `Prop` against
`Type` is stuck in unification, never linked), the `Prop` sort term in parser and elaborator, the function-type rule
of §3, the field rule of §4, and implicit projection of a level from a sort failing cleanly on `Prop`, which has none.

## 6. The corpus

### 6.1 What relied on a zero level

An instrumented build (hooks at every checked application and every sort built from a level term; not committed; the
patch is in the measuring worktree `.claude/worktrees/agent-acef0d2e3a5954d20/.probe/`) ran the test suite (866/867
passing; the one failure is the probe file tripping ArchitectureTests), `gpu/check.sh` (63/63) and 25 checkable doc
snippets.

| Where | Uses of a level-polymorphic definition at a proposition | Rewrite |
|---|---|---|
| GPU proofs | 36 × `False.elim` into a proposition; 3 × `Eq.subst` with a motive into `Prop` | the `Prop` variants of §6.3; one line each |
| Preludes (each copy) | `Eq.mp` (via `Eq.subst` at a `Prop` motive); `False.decEq`, `falseDecidableEq`, `True.decEq`, `trueDecidableEq`, `propSubsingleton` (unused, and vacuous under definitional proof irrelevance) | `Eq.mp` as a direct match; delete the rest (~17 lines) |
| Ordinary tests | 3 (`EvidenceFieldTests`, `PreludeTests`, `TailEvaluationTests`) | 1–3 lines each |
| Universe tests | 20 tests that exist to exercise `Prop` instances, plus ~10 Scala-level `imax` tests | rewrite or delete (§8) |

Nothing in ordinary code needs one definition at both a proposition and a data type. `Pair`'s many zero-level uses are
data (its components are at `succ(u)`), and no `Option`, `List`, `Sum`, `Sigma`, `Subtype`, `Quot` or `Inhabited` is ever
given a proposition outside the universe tests. `Eq` is used at a proof type 6 times in the preludes (the vacuous
instances above) and never in the GPU library; `Eq(Prop, P, Q)` (level one, not zero) is unaffected.

### 6.2 Mechanical changes

- Sorts are rewritten as follows. A level variable keeps its name; its meaning shifts, since it now ranges over data
  levels only.

  | Today | After |
  |---|---|
  | `Sort { level = u }` | `Type { level = u }`, never a proposition |
  | `Sort { level = max(one, u) }` | `Type { level = u }` |
  | `Sort { level = succ(u) }` (`Pair`) | `Type { level = u }` |
  | `Type` (level one) | `Type` (level zero) |
  | `Sort { level = succ(one) }` | `Type { level = one }` |
  | `Prop` | `Prop` |
- 67 such lines per prelude copy (`src/main/resources/Init/Prelude.rac`, `gpu/Prelude.rac`), 3 lines of
  `prelude-inventory.txt`, ~80 level binders across 23 test suites, ~20 lines of documentation.

### 6.3 The prelude

- Families that could be propositions (`Option`, `List`, `Sum`, `Prod`, `Sigma`, `Subtype`, `Inhabited`, `Quot`) move
  to `Type { level = u }`.
- Families that were steered away from `Prop` (`BEq`, `DecidableEq`, `LE`, `LT` at `max(one, u)`; `Pair` at `succ`)
  become plain `Type { level = u }`.
- `Prop` families with a type parameter (`Eq`, `Exists`, `Nonempty`, `Subsingleton`) take `A : Type { level = u }`.
  Equality of proofs is no longer stated; it was vacuous. Proof irrelevance is observed through predicates:
  `def irrel (P: Prop)(Q: P -> Prop)(h1: P)(h2: P)(q: Q(h1)): Q(h2) := q`.
- Eliminators whose target ranged over `Sort v` (`False.elim`, `absurd`, `Empty.elim`, `Eq.subst`, `congrArg`,
  `Bool.cond`, `Decidable.ite`, `Option.elim`, `Sum.elim`, `List.foldr`/`foldl`, `Quot.lift`) target `Type { level = v }`.
  Where the corpus uses a `Prop` target (only `False.elim` and `Eq.subst`), the prelude adds a `Prop` variant:
  `False.elimP {C: Prop}(h: False): C` and `Eq.substP`. Others get one when a use appears; each is a one-line `match`,
  since `match` accepts a motive of either sort.

## 7. What is not done: sort-polymorphic binders

A binder ranging over `{Prop} ∪ {Type { level = u }}` would let one definition serve both. It is not added: a function
type whose codomain is at a sort variable has a conditional sort, which is `imax` again under another name, and its
proposition-ness is unknown until instantiation, which is the third answer this document removes. The corpus has no use
that needs it (§6.1). Agda also keeps `Prop` separate and duplicates; Coq's recent sort polymorphism needs elimination
constraints to stay sound.

## 8. Tests and diagnostics

- The three bugs of §1 become ill-typed programs: `Option(True)`, `Sum(True, True)` and `Eq(Sum(A, A), …)` at a
  proposition no longer typecheck. Their regression tests assert that.
- The check/run gap of §1: the definition is refused or the call is ill-typed, as appropriate; a test pins it.
- Proof-irrelevance tests are restated with predicates (§6.3).
- New: `Prop : Type`; a `Prop`-valued function type is in `Prop` whatever its domain, and its closure kind is `unr`; a
  proposition domain adds no level; a proposition field fits a `Type` family; large elimination from a `Prop` family is
  refused unless the subsingleton rule holds, and allowed for every `Type` family; `Type { kind = lin }` at level zero;
  `kind` or `level` on `Prop`, and `Sort`, are parse errors.
- `LinearProp` is deleted; the `imax` tests (`UniverseTests`) are deleted; `ProofCollapseTests`' level-collapse cases are
  deleted or become rejections.
- `gpu/check.sh` stays green with the four generated kernels byte-identical.

## 9. Documents

`docs/kernel.md`: "Universes and function types" (the sort rules, the removed `imax` fold, `LinearProp`),
"Definitional equality", "Apartness", "Linearity", "Inductives and matching" (universe bounds), "Proofs and
elimination", "Evidence arguments", "Structure eta and projections", "Termination", "Maintained invariants".
`docs/language.md`: "Universes", "Destructuring", "Bundled prelude". `docs/implemented/PAIRS_AND_PRELUDE.md` §2.3 (a `Prod` of a
proof and a value becomes `Subtype` or a `Type` struct with a proof field), `docs/implemented/PROOF_BY_EVALUATION.md` §1.9,
`docs/implemented/LEMUR_ON_RACCOON.md` §2.3, §2.4 and §8.

## 10. Steps

1. **P1, the switch** (one step, since the preludes must change with the kernel): the `Prop` sort value and syntax, the
   function-type and field rules, `imax` removed, both preludes and the GPU library retyped, tests and documents. The
   machinery of §5 that becomes dead may stay in place, inert.
2. **P2, removal**: delete the dead machinery of §5, which the test suite then checks is dead, and the
   `s1-prop-clash` guard if it was merged.

Both are trusted-core changes: implementers at medium effort, hostile reviewers at high.

## 11. Decisions for review

1. **Naming of `Prop` variants** of eliminators: `False.elimP`, `Eq.substP` (suffix `P`), or other names.
2. **`Sort` removed** as a keyword, rather than kept as a synonym for `Type`.
3. **Data levels renumbered** to start at zero (`Type` is `Type { level = zero }`), rather than keeping today's numbers.
4. **The `s1-prop-clash` fix** (commit `ef799a0`, reviewed): merge now as a stopgap, leaving the large-elimination bug
   open until P1, or leave both open until P1.
