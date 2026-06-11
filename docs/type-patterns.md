# Type Patterns: Specification

This document is the normative description of type patterns: their syntax, scoping, declaration-time
checking, freshening, and the matching performed at application sites. The implementation lives mainly in
`telescope/TypePatternOps.scala` (value level) and `Elaborator.scala` (name level); this document is written
so that each implementation step can be audited against a rule here.

Notation: `Γ`, `Δ` are value environments (`Env`). `α`, `β`, `s` are unification variables (`Var`) with
globally unique ids. `deps(v)` is `v.synDeps` (every var id reachable from a value, including through its
type); `deps(Γ)` is `Γ.allDeps`. "Type" below means a `Sort`-classified value.

## 1. Grammar

After parsing, a pattern is one of:

```
Q ::= T                                  rigid type term, no captures        [Type]
    | h(P1, ..., Pn)                     pattern application, n >= 1         [App]
    | $x of Q                            constrained capture                 [CC]
    | (y1: Q1) -> ... -> (yk: Qk) -> Q0  pattern Pi, k >= 1                  [Pi]

P ::= Q | $x                             argument position also allows       [Capture]
                                         bare captures
```

- `h` is a reference (global or local) to a type-valued function. Pattern application is not restricted to
  inductive heads.
- Top-level position (a binder annotation `(b: Q)`, a CC constraint) requires a `Q`; a bare `$x` is only
  legal as an argument of an [App].
- Pi binders use the same parenthesized binder syntax as terms, including instance binders `[y: Q]`. Erased
  binders are not part of pattern Pis.
- **Normalization**: a syntactic pattern containing no captures is not a pattern; it parses as a rigid type
  term `T`. In particular an arrow type is a [Pi] pattern only if a capture occurs somewhere inside it.
- **Flattening**: `(y1: Q1) -> ((y2: Q2) -> Q0)` and `(y1: Q1) -> (y2: Q2) -> Q0` denote the same 2-ary
  [Pi]. Pattern Pis flatten maximally, exactly like term-level Pis, and match only Pi values of the same
  arity (the kernel does not identify `Π(a)(b). R` with `Π(a). Π(b). R`).

Definitions used throughout:

- `captures(Q)` — the ordered binding telescope of `Q`:
  - `captures(T) = []`, `captures($x) = [x]`, `captures($x of Q) = captures(Q) ++ [x]`,
  - `captures(h(Ps)) = concat(captures(Pi))`,
  - `captures((y: Q1) -> Q0) = captures(Q1) ++ captures(Q0)` — Pi binders `y` are *not* captures.
- `compile(Q)` — erasure to an ordinary type term: captures become local references, [App] becomes
  application, [Pi] becomes a Pi term whose binder annotations are the compiled domains.

## 2. Scoping (elaboration)

For a telescope `(b1: Q1)...(bn: Qn) : T_out := body`, processed left to right:

- **S1 (introduction order)**: binder `(bi: Qi)` introduces, in order, the locals `captures(Qi)` and then
  `bi`. All of them are in scope for: the remainder of `Qi` (as plain references `x`), every later `Qj`,
  `T_out`, and `body`.
- **S2 (linearity)**: each capture name has exactly one binding occurrence (`$x`) per scope. A second `$x`,
  or a binder named `x`, is `AlreadyDefined`. Subsequent uses are ordinary references `x`.
- **S3 (Pi hoisting)**: in a [Pi] pattern, *all* captures occurring anywhere inside it (including under
  nested [Pi]s) are bound at the outermost [Pi] node of that pattern, before the Pi's own binders, in
  first-occurrence order. Consequences:
  - captures scope over the entire Pi pattern, so forward references work (a domain may reference a capture
    whose binding occurrence is in the codomain);
  - captures outlive the Pi: they are ordinary telescope locals of the *enclosing* binder, visible to later
    binders, the codomain, and the body.
- **S4 (binder/capture separation)**: a Pi binder name may not collide with any capture name of the same
  pattern (`AlreadyDefined`). Pi binder names scope only over the remaining domains and the codomain of
  their own pattern; they never escape it.
- **S5 (constraint scoping)**: because captures are bound *outside* the Pi binders (S3), the constraint of a
  hoisted capture is scoped at the hoist point: it may reference earlier captures (in hoist order) and
  anything in the enclosing scope, but **must not reference the Pi's binders** `y1..yk` at any nesting
  depth. This is a syntactic check and must be rejected during elaboration.
  (Rigid domain types, by contrast, may freely reference earlier Pi binders — dependent arrows like
  `(n: Nat) -> (v: Vec(Nat, n)) -> $B of Type` are fine; only capture *constraints* are restricted.)

## 3. Declaration rule

Judgment: `Γ ⊢ (b: Q) ok ⇝ (Γ', B)` — in value env `Γ`, the binder pattern is well-formed, producing the
capture-extended env `Γ'` and a checked binder `B` recording `(b, Q, compile(Q), captures(Q))`.

The rule has two phases.

**D1 (capture initialization).** Extend `Γ` with a fresh variable `α_x` for each `x ∈ captures(Q)`, in
order. The type of `α_x` is determined by the position of its binding occurrence:

- **CC**: in `$x of Q'`, first open `Q'` (rule O below, reusing already-introduced captures), require the
  result `V'` to be a type, and set `α_x : V'`.
- **App argument**: a bare `$x` as the i-th argument of `h(P1...Pn)` gets the *opened expected type* of
  `h`'s i-th binder: check `h`'s value to have an n-ary Pi type, walk its telescope binding each argument
  pattern in order (capture arguments bind as the opened expected value; other argument patterns are checked
  against the opened binder type), and set `α_x : Ui` where `Ui` is the opened i-th domain.
- **No other position** can type a bare capture: error `PatternCaptureNeedsExpectedType`.

If a capture is re-encountered with a constraint (possible across shared structure), the existing `α_x` is
reused and checked against the new constraint instead of rebinding.

> **D1-Pi restriction (current)**: inside a [Pi] pattern, initialization handles CC captures but *not* bare
> App-argument captures: `(_: Vec($A, $n)) -> Nat` is rejected with `PatternCaptureNeedsExpectedType`, and
> the constrained forms `(_: Vec($A of Type, $n of Nat)) -> Nat` or `(_: $V of Vec($A, $n)) -> Nat` must be
> used instead. The general App-argument rule above is well-defined there too, so this restriction may be
> lifted later; until then the error should suggest the workaround.

**D2 (pattern checking).** Under `Γ' = Γ, ᾱ`:

- [Type]: `T` checks as a type term.
- [App]: arity matches `h`'s Pi; each non-capture argument pattern checks (recursively) and its value is
  type-checked against the corresponding opened domain.
- [CC]: the constraint checked in D1; nothing further.
- [Pi]: every domain `(yi: Qi)` is itself checked as a binder pattern over the *same* (already initialized)
  capture set, then freshened (rule F); the codomain `Q0` is checked under the freshened binders; the Pi's
  classifier is computed exactly like a term-level Pi (`Prop` if the codomain is `Prop`-valued, else
  `Sort(max(domain levels, codomain level))`).
- Finally `eval(compile(Q), Γ')` must be a type.

D1 running to completion before D2 is what makes S3's forward references work: by the time any domain is
checked, every capture of the whole pattern is already in the environment.

## 4. Opening and freshening

**O (open)**: `open(Γ, Q) = (V, Γ', D)`:

- `Γ'` extends `Γ` with *fresh* variables `α_x` for `captures(Q)` not already present, typed exactly as in
  D1 (CC constraints are re-evaluated; App-argument captures are typed from freshly opened head telescopes;
  for [Pi], initialization walks the whole pattern first).
- `V = eval(compile(Q), Γ')`.
- `D = (⋃_x deps(Γ'(α_x))) \ deps(Γ)` — the ids created by this opening, i.e. the capture variables plus any
  transitively reachable fresh structure. These are the only ids a subsequent match may solve.

**F (freshen)**: `freshen(Γ, b: Q) = Γ', b := fresh β : V` where `(V, Γ', _) = open(Γ, Q)`. Used wherever a
binder must be entered without an argument: codomain checking, body checking, Pi equality, instance search,
inductive checks.

Invariants:

- **O-fresh**: every opening creates brand-new ids; two openings of the same pattern are α-equivalent but
  share nothing.
- **O-once**: at a binding site the pattern is opened exactly once, and the same `(V, Γ', D)` is used both
  to solve captures and to bind the binder. Solving against a second opening of the same pattern is a bug.

## 5. Matching at applications

Checking `f(a1, ..., an)` with `f : Π(b1: Q1)...(bn: Qn). T` processes binders left to right in the callee
env `Δ` (the Pi's closure env), with each argument value `v` supplied by the caller.

**M (bind)**: `bind(Δ, (b: Q), v) = Δ'`:

1. If `captures(Q) = []`: check `type(v) ≤ eval(compile(Q), Δ)` (definitional equality with cumulativity;
   the evaluation-only path may skip the check), and `Δ' = Δ, b := v`.
2. Otherwise:
   - **M1 (open)**: `(V, Δ1, D) = open(Δ, Q)`.
   - **M2 (solve)**: `σ = pmatch(Q, V, type(v), ∅ allowing D)` — pattern unification (section 6), starting
     from an *empty* equality store whose refinable set is exactly `D` (plus ids created transiently inside
     `pmatch` itself).
   - **M3 (constraints)**: for each `$x of Q'` in pattern order: let `C = σ(type-assigned-to-α_x)`; try to
     *unify* `C` with `σ(α_x).tpe` (this may solve further capture variables, e.g. `$u` in `Sort($u)`);
     if unification fails, require `σ(α_x).tpe ≤ C` (cumulativity / proof irrelevance), else fail.
   - **M4 (validation)**: for every capture `x`:
     - **V-solved**: `σ(α_x) ≠ α_x` — the argument's type must determine every capture; otherwise
       `PatternCaptureNeedsExpectedType`.
     - **V-closed**: `deps(σ(α_x)) ⊆ deps(Δ) ∪ deps(type(v))` — a capture's solution must be a value over
       variables that exist outside the match. It must not mention *any* id created during M1–M3:
       shared Pi-binder variables (`s̄` of section 6, at any depth — spine, domains, or inside constraint
       unification), transient flex variables opened on the actual side (the argument type's own pattern
       captures), or unsolved sibling captures. Otherwise `PatternCaptureEscapesScope`.
       Given V-solved and monotonic variable ids, this is equivalent to: no id allocated after solving began
       survives in a solution — which is how the implementation checks it (a fresh-id watermark taken at the
       start of M2).
   - **M5 (bind)**: `Δ' = σ(Δ1), b := ascribe(v, σ(V))`. The checking path additionally verifies
     `type(v) ≤ σ(V)`.

Invariants:

- **M-local**: solving starts from an empty store and may refine only `D` (and `pmatch`-internal
  transients). Ambient variables of `Δ` or of the caller are never refined by a type-pattern match.
- **M-ascribe**: the binder is bound at the *solved expected type* `σ(V)`, not at `type(v)`. Later binders,
  the codomain, and the caller therefore compute with the pattern's view of the argument. This is also what
  makes the coarse Pi equality of section 7 sound: a function accepted at a more specific pattern type is
  subsequently *used* at that more specific type.
- **M-eager**: there is no constraint postponement. A pattern that the argument's type does not fully
  determine is an error at this binder, not later.

## 6. Pattern unification

`pmatch(Q, expected, actual, σ)` unifies the opened expected type with the actual argument type, directed by
the pattern:

- **U-default**: if `Q` is not a [Pi], `pmatch = unify(expected, actual, σ)` — ordinary value unification
  (definitional equality modulo the refinable set, normalizers, Miller pattern applications, level
  equations). Captures solve here because `expected` literally contains the `α_x`.
- **U-Pi**: if `Q = (y1: Q1) ... (yk: Qk) -> Q0`, then `expected` is a `VPi` (by construction), and the two
  Pi values relate by the *generic* Pi unification rule:
  1. `actual` must be a `VPi` with exactly `k` binders, with pointwise equal instance flags; otherwise the
     match fails.
  2. For `i = 1..k`:
     - open the expected binder (compiled, so capture-free: it references the already-created `ᾱ`) and the
       actual binder (which may itself be a pattern binder; its captures open as fresh transient flex
       variables, added to the refinable set);
     - `σ ← unify(expected domain_i, actual domain_i, σ)` — domains unify *invariantly*;
     - create one fresh **shared variable** `s_i : σ(domain_i)` and bind both sides' binders to it
       (registering instance keys for instance binders). `s_i` is transient: it must not appear in any
       capture solution (V-closed).
  3. `σ ← unify(σ(expected codomain at s̄), σ(actual codomain at s̄), σ)` — nested arrows (in codomains *and*
     domains) relate by the same rule, so captures anywhere under binders solve through step 2/3, and every
     shared variable introduced at any depth is transient and excluded by V-closed.

  There is no pattern-directed dispatch in the solver: `compile(Q)` already placed the `ᾱ` inside rigid
  structure, and ordinary unification of the opened pattern against the actual type solves them. V-closed is
  the single rule that keeps binder-crossing sound.

There is no contravariant subtyping anywhere in a match: domains and codomains unify; cumulativity is
admitted only at the final `≤` checks (M3 constraint fit, M5 argument check).

## 7. Pattern types and definitional equality

Two Pi values are definitionally equal iff they have the same binder count, pointwise equal instance flags,
*related* binder patterns, and defEq codomains under shared fresh variables. Two binder patterns are related
iff their openings unify **with both sides' capture variables refinable**.

This is deliberately coarse: it treats captures up to α-equivalence (`Vec($A, $n) -> ...` equals
`Vec($B, $m) -> ...`), and it lets one side's rigid structure solve the other side's captures. The
asymmetries this could introduce are neutralized by M-ascribe (values are used at the solved expected type)
and by V-solved (capture-exporting positions reject arguments whose types leave captures undetermined).

## 8. Soundness conditions (summary)

1. **Locality** (M-local): a match refines only variables it created.
2. **Freshness** (O-fresh, O-once): one opening per binding event; openings share nothing.
3. **Determination** (V-solved): every capture is solved by the argument type.
4. **Closedness** (V-closed): every capture solution — and hence everything the body computes with — is a
   value over the pre-existing environment plus the argument's type. No variable created during matching
   (shared Pi binders at any depth, actual-side transients, unsolved siblings) may leak.
5. **Constraint fit** (M3): solved captures satisfy their declared constraints up to cumulativity.
6. **Ascription** (M-ascribe): binders are bound at solved expected types.
7. **Scope separation** (S3–S5): hoisted captures and their constraints live strictly outside the Pi's own
   binders.

## Appendix: implementation mapping

| Spec | Implementation |
|---|---|
| `captures(Q)` | `TypePatternOps.collectCaptures`, `Elaborator.typePatternCaptureNames` |
| `compile(Q)` | `TypePatternOps.compileType` |
| S1–S4 | `Elaborator.elabPattern` / `elabBinder` (`fixedCaptures` implements S3 hoisting) |
| D1/D2 | `TypePatternOps.toVBinder` (`initializePiCaptures` + `checkPattern`) |
| O / F | `TypePatternOps.openPattern` / `openBinderPattern` / `freshenBinder` |
| M | `TypePatternOps.bindValue` / `bindValueAndCheck` / `solveOpenedCaptures` |
| M2 (incl. U-Pi) | `ValueEquivalence.unify` / `tryUnifyPis` / `tryRelatePiBinders` |
| M3 | `TypePatternOps.solveTypePatternConstraints` |
| M4 | V-solved and watermark V-closed loops in `solveOpenedCaptures` |
| §7 | `ValueEquivalence.tryRelatePiBinders` / `defEqPi` / `tryUnifyPis` |

## Appendix: known divergences (2026-06-11)

1. **S5 is not checked at elaboration.** `(n: Nat) -> $B of Eq(n, n)` elaborates (the constraint resolves
   `n` into the Pi binder scope) and then crashes at declaration checking with a raw `n#1 not found`.
2. **D1-Pi restriction** (documented above): bare App-argument captures under a Pi are rejected; the error
   does not suggest the constrained-capture workaround.
3. **Pretty-printing does not round-trip**: pattern Pis print elided anonymous binders (`Nat -> $B`), which
   the parser only accepts in `(name: ...)` binder form.

(Resolved 2026-06-11: V-closed was previously enforced only against the pattern's own Pi-spine binder
variables, letting solutions capture transients from the actual side's patterns or from nested-domain
unification. It is now the watermark check in `solveOpenedCaptures`.)
