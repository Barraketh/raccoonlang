# Raccoon Language Overview
_Context and guiding principles for implementing Raccoon (Surface + Core)_

Raccoon is a **small dependently typed language / proof assistant kernel** designed to be:
- **Predictable**: minimal “ambient magic” and local, explicit effects.
- **Auditable**: every nontrivial elaboration step is visible in the resulting core term.
- **Fast to typecheck**: conversion and elaboration are engineered for tight inner loops.
- **RL-friendly**: stable semantics and bounded, explicit search sites support AlphaZero-style exploration.

This document provides background and design rationale for Codex while implementing the language.

---

## 1) Goals

### 1.1 Primary goals
1. **Kernel simplicity**
   - Small trusted base (RaccoonCore).
   - Decidable, predictable conversion checking.
2. **Fast, stable typechecking**
   - Conversion cost should be stable (avoid blowups from uncontrolled unfolding/search).
   - Strong caching opportunities (WHNF, conversion, inferred head types).
3. **Auditability / reproducibility**
   - Surface syntax desugars deterministically to core.
   - No implicit parameter insertion in the kernel.
4. **Search-friendly tooling**
   - Tactics/search live **outside** the kernel (untrusted).
   - Any search is explicit and bounded (if enabled).
5. **Practical dependent programming**
   - Inductive families + explicit motives for dependent matching.
   - Equality + transport for controlled rewriting.
   - Use-time proof irrelevance via *irrelevant binders*.

### 1.2 Non-goals (at least initially)
- Maximal ergonomics comparable to Lean + mathlib.
- Aggressive automation in the trusted kernel.
- Large metatheory features early (quotients with computation, complex coercions).
- Large amount of definitional computation in types beyond a small trusted core.

---

## 2) Architecture: Surface vs Core

Raccoon is explicitly split into two layers:

### 2.1 RaccoonSurface (user language)
- Friendly syntax: multi-arg binders, pattern matches, equation-style definitions.
- **No implicit parameters** in the surface syntax (still explicit).
- Dependent pattern matches must include an explicit `returning ...` clause (motive).
 - Transparency: declarations are opaque by default; an optional `inline` modifier on definitions allows δ-unfolding. `theorem/axiom` are always opaque.
 - Surface universes are inferred deterministically; the core uses explicit levels.
- Optional conveniences (may be added later):
  - `implicit[T]` elaboration-time resolution site (typeclass-like dictionary search).
  - holes `?h` and a tactic language `by { ... }` as untrusted tooling.

**RaccoonSurface must desugar deterministically** into RaccoonCore. The kernel never sees holes or `implicit[...]`.

### 2.2 RaccoonCore (kernel language)
- Tiny AST: `Type`, `Pi`, `Lam`, `App`, `Let`, `Match`, plus global constants/inductives.
- Explicit **relevance** on binders: `Rel` vs `Irr`.
- Definitional equality is WHNF-based with:
  - β/ζ/ι reductions
  - restricted δ (Inline-only; opaque-by-default)
  - irrelevance-aware spine comparison (irrelevant args ignored by conversion)

The **trusted boundary** is: RaccoonCore programs must be fully explicit and hole-free.

---

## 3) Design philosophy: “Make power explicit”

Lean/Coq/Agda gain ergonomics by inserting and solving metavariables implicitly:
- implicit parameters (type arguments, instances)
- coercions
- motive inference
- proof search/tactics

This is powerful, but it introduces:
- context-sensitive meaning (`f x` elaborates differently depending on expected type)
- unpredictable performance (failed attempts can be expensive)
- larger semantic surface area (harder to audit)

Raccoon prefers:
- explicit binders and explicit motives
- explicit sites where search may occur (optional `implicit[T]`)
- a small, predictable conversion procedure

This makes Raccoon a better substrate for program synthesis / RL search:
- fewer “mystery degrees of freedom” in the elaborator
- stable typechecking cost per node

---

## 4) Core language design decisions (and rationale)

### 4.1 Pure language (initially)
- No effects in the core calculus.
- Makes definitional equality and η principles semantically safe.
- Effects can be added later via monads/encodings or a separate compilation layer.

### 4.2 Non-cumulative universes
- Universes do **not** implicitly coerce upward (`Type u` is not a `Type (u+1)`).
- Keeps conversion/subtyping simpler and more explicit.
- Avoids cumulativity interactions that complicate η/normalization strategies.
- Universe polymorphism is explicit in the core (via `Level` expressions like `max`), with surface universe inference to synthesize them.
- Implementation note: maintain a simple normalized level form (flatten `max`, track `succ` offsets) and compare structurally.

### 4.3 Explicit dependent matching with explicit motive
- `match scrut as w returning R w with ...`
- Motive inference is intentionally avoided to reduce elaborator complexity.
- When indices don’t match definitionally, users write `transport` / rewriting explicitly.
- The elaborator can still do **index refinement** (a small, deterministic unification on indices) to:
  - determine reachable constructors
  - avoid binding forced constructor args in cases
  - keep patterns concise without global metavariables
  - accept zero-case matches when no constructors are reachable

### 4.4 δ-reduction: opaque-by-default
- Uncontrolled unfolding is a major source of conversion slowdowns.
- Raccoon uses a strict policy: **δ unfolds Inline-only** (or another small whitelist).
- Users can still express unfolding by:
  - marking defs `inline` (small computational defs)
  - using explicit rewrite lemmas (recommended for proofs)
  - Note: `theorem` and `axiom` are always opaque in the surface; the kernel only honors the explicit `Inline`/`Opaque` transparency on constants.

### 4.5 Use-time proof irrelevance via irrelevant binders
Instead of a special `Prop` sort:
- Any term can be used as a proof, but when an argument is marked **irrelevant**:
  - it is **typechecked** but **cannot be inspected** (no pattern match / computation dependence)
  - conversion **ignores** irrelevant arguments in application spines
  - compilation/evaluation can erase irrelevant args

This gives proof irrelevance “where you say it matters,” and keeps conversion fast by avoiding proof-term comparison.

### 4.6 Conversion strategy: WHNF + spine comparison
- Conversion is structured and cacheable:
  - reduce to WHNF
  - compare constructors/Π structurally
  - compare neutral heads + spines, skipping Irr arguments based on the function type
- Optional typed η can be added later as a comparison rule (not required initially).

---

## 5) What the elaborator *is allowed* to do (and what it should not do)

### 5.1 Allowed (deterministic)
- Desugar surface syntax to core AST.
- Perform index refinement on match scrutinee indices (first-order, WHNF-aware).
- Reject programs that require ambiguous inference (e.g., missing motives).

### 5.2 Optional features (explicit sites only)
- `implicit[T]` may run dictionary resolution / instance search, but only at explicit sites.
  - Must be deterministic (or at least explainable) and bounded by depth/budget.
  - Must produce a concrete RaccoonCore term, or fail with a trace.
- Holes/tactics:
  - allowed in Surface, but must be eliminated before kernel check.
  - tactics produce RaccoonCore terms; kernel remains the final authority.

### 5.3 Not allowed (by design)
- Global implicit parameter insertion at arbitrary applications.
- Hidden coercion insertion.
- Hidden motive inference in dependent matches.
- Unbounded unfolding/search during typechecking.

---

## 6) Implementation guidance for Codex

### 6.1 Suggested milestone plan
1. **RaccoonCore parser** (for internal testing).
2. **Kernel typechecker**:
   - inference/checking
   - WHNF reducer (β/ζ/ι + δ-inline)
   - conversion (spine-based, irrelevance-aware)
3. **Inductive declarations + constructors**
   - enough to express `Nat`, `Vec`, `Eq`.
4. **Surface parser**
   - parse binders, matches, data decls, defs
5. **Surface desugaring**
   - multi-arg → nested Π/λ
   - match → core Match with explicit motive
   - index refinement to simplify patterns/cases
6. (Optional) `implicit[T]` resolution
7. (Optional) holes/tactics tooling

### 6.2 Must-have performance engineering (early)
For RL-friendly speed, implement these early:
- de Bruijn indices + efficient substitution (or closures)
- hash-consing / sharing of terms
- WHNF cache
- conversion cache keyed by (t,u,transparency)
- cache inferred types of neutral heads
- memoize index unification results where possible

### 6.3 Error reporting (important for auditability)
Because Raccoon avoids implicit inference, the errors should be direct:
- motive mismatch / missing motive
- unreachable/missing match cases
- index unification failure details (show the two indices that failed to unify)
- conversion failures with a small “WHNF diff”

---

## 7) Tiny worked example (surface → core intuition)

Surface:

```text
def head (A : Type 0) (n : Nat) (v : Vec A (succ n)) : A :=
  match v as w returning A with {
  | cons a xs => a
  }
```

Elaborator notes:
- scrutinee type `Vec A (succ n)` makes constructor `nil` unreachable
- index arg of `cons` is forced (`n`), so pattern binds only `a xs`

Core (schematic):

```text
Lam(Rel, A, Lam(Rel, n, Lam(Rel, v,
  Match(v, Vec A (succ n), w,
    Lam(Rel, w, A),
    { Case(cons, [a:A, xs:Vec A n], a) }
  ))))
```

---

## 8) Future extension points (intentionally postponed)

These can be added later without destabilizing the kernel:
- More universe features / constraints
- Stronger automation: `simp`-like rewriting, best-first proof search
- Richer libraries for algebra/hierarchy (possibly via explicit dictionaries + `implicit[T]`)
- Quotients or other extensional features (likely as axioms or with limited computation)
- Effects / IO (kept separate from kernel conversion)

---

## 9) Summary

Raccoon is a proof assistant core optimized for:
- **small trusted kernel**
- **fast and predictable typechecking**
- **explicit, auditable elaboration**
- **search-friendly program/proof generation**

The core is intentionally spartan; ergonomics are provided by deterministic desugaring and (optional) untrusted tooling.
