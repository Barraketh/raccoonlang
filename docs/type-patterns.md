# Type Patterns: Specification

This document is the normative description of type patterns: their syntax, scoping, declaration-time
checking, freshening, and the matching performed at application sites. The implementation lives mainly in
`telescope/TypePatternOps.scala` (value level) and `Elaborator.scala` (name level); this document is written
so that each implementation step can be audited against a rule here.

The central judgment is **matching, not unification**. A binder pattern is matched against the actual
argument's type: the actual side is read-only input, captures are outputs, and solving is a single
deterministic left-to-right traversal of the pattern. There is no constraint store, no postponement, and no
search. Wherever two *rigid* values must agree, the pattern machinery delegates to definitional equality
(`defEq`) — solving is structural, equality is semantic, and the two never mix.

Notation: `Γ`, `Δ` are value environments (`Env`). `σ` is a finite map from captures to values. `deps(v)` is
`v.synDeps` (every var id reachable from a value, including through its type); `deps(Γ)` is `Γ.allDeps`.
`nf(A)` is the (normalizer-)normal form of a value — values in this kernel are maximally reduced, so this is
how the value is already presented. "Type" below means a `Sort`-classified value.

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

**D1 (capture initialization).** Extend `Γ` with a fresh neutral variable `α_x` for each `x ∈ captures(Q)`,
in order. The type of `α_x` is determined by the position of its binding occurrence:

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

**D3 (matchability).** The pattern must be *matchable*: every capture must sit in a position the matching
judgment of section 5 can traverse. Captures under a stuck match (`Vec(Nat, pred($n))`), under level
expressions outside the `u + k` fragment (`Sort(Level.max(Level.one, $u))`), or in application spines that
are neither presentations nor higher-order patterns, can never be determined by any argument type, and the
declaration is rejected with `UnmatchablePattern`. Operationally this is decided by matching the pattern
against an independent fresh opening of itself (an α-renamed copy): the self-match exercises every rule on
the pattern's own shape, so it succeeds exactly when some argument presentation could.

D1 running to completion before D2 is what makes S3's forward references work: by the time any domain is
checked, every capture of the whole pattern is already in the environment.

## 4. Opening and freshening

Capture *variables* exist only when a binder is **entered without an argument**. They are ordinary neutral
atoms — opaque locals, exactly like a freshened term binder — not unification metavariables. Binding sites
(section 6) never create capture variables: matching assigns capture *values* directly.

**O (open)**: `open(Γ, Q) = (V, Γ')`:

- `Γ'` extends `Γ` with fresh neutral atoms `α_x` for `captures(Q)` not already present, typed exactly as in
  D1 (CC constraints are re-evaluated; App-argument captures are typed from freshly opened head telescopes;
  for [Pi], initialization walks the whole pattern first).
- `V = eval(compile(Q), Γ')`.

**F (freshen)**: `freshen(Γ, b: Q) = Γ', b := fresh β : V` where `(V, Γ') = open(Γ, Q)`. Used wherever a
binder must be entered without an argument: codomain checking, body checking, Pi equality, instance search,
inductive checks.

Invariant **O-fresh**: every opening creates brand-new atoms; two openings of the same pattern are
α-equivalent but share nothing.

## 5. The matching judgment

`match(Q, A)` over an environment `Δσ` (the callee env extended with the solutions accumulated so far)
either fails or extends `σ` with values for the captures whose binding occurrences lie in `Q`. `A` is a type
value — the *presentation* the kernel already holds, in normal form.

Three principles govern every rule:

- **Directional**: `A` is input and is never refined. Only captures of `Q` receive values.
- **Presentation-directed**: matching reads `nf(A)` structurally. It never searches for a decomposition and
  never inverts a function; if the presentation does not exhibit the pattern's shape, the match fails. The
  certificate check (M3 below) is what makes this safe: matching merely *proposes* capture values, and the
  proposal is then verified by full definitional equality.
- **Total traversal**: the traversal visits every capture position in `Q` left to right, so a successful
  match assigns every capture exactly once — at its binding occurrence, or at an earlier reference position
  when S3 forward references put a reference before the `$` occurrence. "The argument does not determine
  this capture" can only surface as a structural failure or as a solution that mentions match-local
  variables (V-closed).

The rules, by case on `Q` (or argument pattern `P`):

- **[Type] / rigid leaves**: `match(T, A)` succeeds iff `defEq(eval(T, Δσ), A)`. All semantic power
  (normalizers, proof irrelevance, cumulative levels inside `defEq`) lives here; none of it solves anything.

- **[Capture]**: `match($x, A)` assigns `x := A`. The assignment is then *classified*: the declared type of
  `x` at this position (the head telescope's domain — see [App]) must accept `type(A)`, which recursively
  matches if that domain is itself a pattern, or is a `≤` check (cumulativity) if it is rigid.

- **[CC]**: `match($x of Q', A)` assigns `x := A`, then classifies the assignment against the constraint:
  - if `captures(Q') = ∅`: require `type(A) ≤ eval(Q', Δσ)` — constraints *classify*, so cumulativity and
    proof irrelevance apply;
  - else: `match(Q', type(A))` — the constraint's own captures are read off the assignment's type. This is
    one recursion, not a separate pass: `$x of $A of Sort($u)` solves `x`, then `A := type(x)`, then
    `u := level of type(A)`, in that order, in place.

- **[App]**: `match(h(P1...Pn), A)`:
  1. `H = eval(h, Δσ)`; `H`'s type must be an n-ary Pi — its telescope `(t1: R1)...(tn: Rn)` over closure
     env `Δh`.
  2. `nf(A)` must be an application spine `H'(B1...Bn)` with `defEq(H, H')`; otherwise the match fails.
     Matching never re-associates, η-expands, or unfolds `A` beyond its normal form to find such a spine.
  3. For `i = 1..n`, threading `σ` and `Δh`:
     - `match(Pi, Bi)` — bare captures assign, rigid arguments `defEq`-check, nested patterns recurse;
     - bind `H`'s binder `(ti: Ri)` with `Bi` *by this same matching discipline* (rule M of section 6
       restricted to a sub-position): if `Ri` has captures, `match(Ri, type(Bi))` solves `H`'s own hidden
       captures (e.g. `$u` in `Vec`'s `(A: Sort($u))`) into `Δh`; otherwise `type(Bi) ≤ eval(Ri, Δh)`.
  4. Finally `defEq(type(A), codomain of H's telescope at B̄)`.

  Decomposition is by presentation, not by injectivity: for a non-injective head the spine `A` actually
  exhibits is the one that is read, and the certificate check vouches for the result.

  Note that `h` need not be opaque: a transparent head is evaluated like any pattern position, and matching
  proceeds against whatever shape its expansion *presents* — `Set($A)` with `Set(A) = (x: A) -> Prop`
  matches by the [Pi] rule, not by spine decomposition.

  Spine decomposition for *solving* applies only to **intrinsically rigid** heads: inductive and struct
  constants, constructors, axioms and builtins, and neutral variables (including flex capture heads). A
  spine that exists only as the presentation of a stuck `stable` definition — a re-folded blocked
  application, or the named form of a definition stuck on an opaque scrutinee — is not decomposable;
  captures inside one are rejected at declaration (D3). Pattern legality and match outcomes therefore never
  depend on the `stable` annotation, which keeps its equality role only: capture-free presentation spines
  are ordinary `defEq` leaves, where keys and normalizers see them as named spines.

- **[Flex-spine]**: a capture in *head* position applied to pairwise-distinct rigid variables —
  `$F(x1, ..., xm)` arising from a transparent expansion, with each `xi` a binder variable — matches any
  actual piece `B` whose free variables are permitted at `F`'s scope: `F := λx1...xm. B`, the unique
  solution in the higher-order pattern fragment. This is higher-order *matching*, not unification: the head
  must be a capture, the spine must be distinct rigid variables, and the abstraction either exists uniquely
  or the rule does not apply. (`Subset($s of Set($A), $t of Set(A))` solves `s`, `t` this way: its expansion
  presents `s(x)` and `t(x)` under the [Pi] rule's shared variable `x`.) The abstraction is quoted in the
  environment the matched value lives in (`argEnv`), so solutions may close over the call site's ambient
  locals — `s := λx. r(x, a)` with `r`, `a` caller binders is a legitimate solution. When an abstraction
  exists but cannot be quoted, the failure reason is carried into the eventual error rather than swallowed
  by the fallback spine rule.

- **[Pi]**: `match((y1: Q1)...(yk: Qk) -> Q0, A)`:
  1. `nf(A)` must be a `VPi` with exactly `k` binders and pointwise equal instance flags; otherwise fail.
  2. For `i = 1..k`:
     - **skolemize** the actual binder: open it (rule O) with fresh atoms for any captures *it* declares —
       the actual side is input, so its pattern structure is opaque; its atoms are match-local and may not
       end up in any solution (V-closed);
     - `match(Qi, actual domain_i)` — the pattern's domain reads the actual's domain; rigid domains
       `defEq`-check, captures assign;
     - create one fresh **shared atom** `s_i`, typed at the (now σ-instantiated) domain, and enter it as the
       value of both sides' binders (registering instance keys for instance binders). `s_i` is match-local.
  3. `match(Q0, actual codomain at s̄)`.

  Every atom created in step 2 — the actual side's skolems and the shared `s̄`, at any nesting depth — is
  match-local. A capture solution that mentions one has no meaning outside the match and is rejected by
  V-closed. This is the entire soundness story for matching under binders.

- **[Level]**: capture positions of type `Level` (reached through `Sort(...)` arguments or `Level`-typed
  head arguments) admit one arithmetic form: a compiled level expression consisting of a single capture plus
  a constant offset, `u + k`. It matches an actual level `ℓ` iff `ℓ ≥ k`, assigning `u := ℓ − k`. All other
  level shapes in capture position (`max` forms, multiple captures) are not matchable and fail. Rigid level
  expressions are `defEq` leaves like everything else.

**Determinism.** For fixed `Δ`, `Q`, and `A`, `match(Q, A)` has at most one result, computed by one
left-to-right traversal with no backtracking: each rule consumes a fixed position of `nf(A)`, and each
capture is assigned exactly at its binding occurrence. This is a theorem of the rules above, not a property
of an engine.

## 6. Binding at applications

Checking `f(a1, ..., an)` with `f : Π(b1: Q1)...(bn: Qn). T` processes binders left to right in the callee
env `Δ` (the Pi's closure env), with each argument value `v` supplied by the caller.

**M (bind)**: `bind(Δ, (b: Q), v) = Δ'`:

1. If `captures(Q) = []`: check `type(v) ≤ eval(compile(Q), Δ)` (the evaluation-only path may skip the
   check), and `Δ' = Δ, b := v`.
2. Otherwise:
   - **M1 (match)**: `σ = match(Q, type(v))` over `Δ`. Failure is a type error at this binder — there is no
     postponement (M-eager).
   - **M2 (V-closed)**: for every capture `x`: `deps(σ(x)) ⊆ deps(Δ) ∪ deps(type(v))`. A solution must be a
     value over variables that exist outside the match; the skolems and shared atoms of [Pi] (at any depth)
     are match-local and may not survive into it. Otherwise `PatternCaptureEscapesScope`.
     Since match-local atoms are exactly the variables allocated after matching began, and ids are
     monotonic, this is checked as: no id in a solution exceeds a fresh-id watermark taken at the start of
     M1.
   - **M3 (certificate)**: `E = eval(compile(Q), Δ ∪ σ)`; the checking path verifies `type(v) ≤ E`. This
     check carries the soundness of the whole judgment: matching only proposed `σ` from the presentation,
     and `E` is re-derived from the pattern itself.
   - **M4 (bind)**: `Δ' = Δ, captures := σ, b := ascribe(v, E)`.

Invariants:

- **M-local**: matching never refines anything in `Δ` or in the caller; its only outputs are `σ`.
- **M-ascribe**: the binder is bound at the *instantiated expected type* `E`, not at `type(v)`. Later
  binders, the codomain, and the caller compute with the pattern's view of the argument. This is also what
  makes instantiation (section 7) sound: a function accepted at a more specific type is subsequently *used*
  at that more specific type.
- **M-eager**: a pattern the argument's type does not fully determine is an error at this binder, not later.
- **E-once**: `E` is computed once per binding event and used for both the certificate and the ascription.

## 7. Pattern types and definitional equality

Pattern structure participates in equality in exactly two ways — neither involves solving both sides at
once:

- **defEq (symmetric)**: two Pi values with pattern binders are definitionally equal iff they are
  **α-equivalent as patterns**: same arity, pointwise equal instance flags, and pointwise α-equivalent
  binder patterns — captures correspond by position, rigid parts are `defEq` under shared fresh atoms, and
  codomains are `defEq` under shared atoms. Where flexibility *lies* is part of the type:
  `Vec($A, zero) -> X` and `Vec(Nat, $m) -> X` are different types. α-equivalence is an equivalence
  relation, so conversion stays transitive.
- **Instantiation (directional)**: a value whose type is a pattern Pi may be used where a *more specific* Pi
  is required: `v : Q-pattern-type` is accepted at expected type `T` iff `match(Q, T)` succeeds with closed
  solutions, and `v` is then used at `T` (per M-ascribe). This is the matching judgment applied at the type
  level, not a new mechanism. The reverse direction — supplying a value at a pattern-typed binder — is
  ordinary binding (section 6). When *both* sides are patterns, only α-equivalence applies; one pattern is
  never solved against another.

## 8. Soundness conditions (summary)

1. **Directionality** (M-local): matching reads the actual type and writes only capture solutions; nothing
   pre-existing is ever refined.
2. **Determinism** (section 5): at most one `σ` per (pattern, presentation) pair, by construction.
3. **Freshness** (O-fresh): atoms from distinct openings are distinct; match-local atoms are distinct from
   everything ambient.
4. **Closedness** (V-closed): every capture solution is a value over the pre-existing environment plus the
   argument's type; no match-local atom (skolem or shared binder atom, at any depth) leaks.
5. **Certification** (M3): every accepted binding is re-checked against the pattern's own compiled type by
   full definitional equality; matching proposes, `defEq` disposes.
6. **Ascription** (M-ascribe): binders are bound at instantiated expected types.
7. **Scope separation** (S3–S5): hoisted captures and their constraints live strictly outside the Pi's own
   binders.
8. **Equality discipline** (section 7): pattern equality is α-equivalence; crossing flexibility is always
   directional instantiation.

## Appendix A: implementation mapping

| Spec | Implementation |
|---|---|
| `captures(Q)` | `TypePatternOps.collectCaptures`, `Elaborator.typePatternCaptureNames` |
| `compile(Q)` | `TypePatternOps.compileType` |
| S1–S4 | `Elaborator.elabPattern` / `elabBinder` (`fixedCaptures` implements S3 hoisting) |
| D1/D2 | `TypePatternOps.toVBinder` (`initializePiCaptures` + `checkPattern`) |
| D3 | `TypePatternOps.validateMatchable` (self-match against a fresh opening) |
| O / F | `TypePatternOps.openPattern` / `openBinderPattern` / `freshenBinder` |
| M | `TypePatternOps.bindValue` / `bindValueAndCheck` / `solveOpenedCaptures` |
| M1 (match) | `TypePatternMatcher.matchBinderPattern` — value-directed over the opened pattern: `matchValue` walks the opened presentation, `linkCapture` is [Capture]/[CC] with classification fused, `matchLevel` is [Level], `trySolveFlexSpine` is [Flex-spine], `matchPi` is [Pi] with skolemized actual binders |
| M2 | watermark loop in `solveOpenedCaptures` |
| M3/M4 | `bindOpenedValueAndCheck` / `bindOpenedValue` |
| §7 α-equivalence | `ValueEquivalence.defEqPi` via `TypePatternMatcher.matchesUpToRenaming` (a match whose solutions form an injective atom renaming) |
| §7 instantiation | `TypeChecker.checkFits` → `TypePatternMatcher.instantiates` (a match with watermark-closed solutions; tried in both directions, instantiating whichever side is the pattern) |

The matcher is value-directed rather than pattern-directed: it walks the *opened* pattern value (capture
atoms embedded in rigid structure) against the actual type, which realizes the section 5 rules without a
separate pattern interpreter — a capture's declared type travels as its atom's type, so [App] step 3's
telescope classification happens at `linkCapture`, and transparent heads are matched at whatever shape
their expansion presents. Failures surface as `TypeMismatch`.

## Appendix B: known divergences (2026-06-11)

M1 is implemented by the directional matcher (`TypePatternMatcher`); the general unifier no longer runs at
binding sites, and in particular the Interpreter's application path performs no unification. §7 is
implemented as specified: `defEqPi` is α-equivalence (so conversion is transitive), and `checkFits` admits
directional instantiation of whichever side is the pattern. The only remaining mutual-flex Pi relation is
`tryRelatePiBinders`/`tryUnifyPis` inside the *unification* dispatch, which is no longer reachable from
pattern matching or definitional equality — its remaining callers (match-branch refinement, instance
search) are genuinely unification features. Remaining divergences:

1. **S5 is not checked at elaboration.** `(n: Nat) -> $B of Eq(n, n)` elaborates (the constraint resolves
   `n` into the Pi binder scope) and then crashes at declaration checking with a raw `n#1 not found`.
2. **D1-Pi restriction** (documented above): bare App-argument captures under a Pi are rejected; the error
   does not suggest the constrained-capture workaround.
3. **Pretty-printing does not round-trip**: pattern Pis print elided anonymous binders (`Nat -> $B`), which
   the parser only accepts in `(name: ...)` binder form.

Resolved earlier on this branch:

- *V-closed under-enforcement* (2026-06-11): previously only the pattern's own Pi-spine binder variables
  were forbidden; now the watermark check in `solveOpenedCaptures` covers every match-local variable.
- *Unification at binding sites* (2026-06-11): M1 previously ran `ValueEquivalence.unify` restricted to the
  capture atoms. The matcher replaced it; with that, the actual side is skolemized (its pattern type can no
  longer be instantiated to satisfy the expected pattern's rigid structure — such programs now need an
  explicit eta-wrapper), the [CC] classification is fused into assignment instead of a separate constraint
  pass, match failures surface as `TypeMismatch` rather than `UnificationFailed`, and non-matchable shapes
  are rejected at declaration (D3) instead of failing at every use site.
- *Mutual-flex pattern-Pi equality* (2026-06-11): `defEqPi` previously unified both sides' openings with
  both capture sets refinable — coarser than α-equivalence and non-transitive (`Vec($A, zero) -> X` equaled
  both `Vec($B, $m) -> X` and, through it, `Vec(Nat, one) -> X`). It now requires an injective capture
  renaming; pattern types with flexibility in different places are unequal, and the useful crossings are
  carried by `checkFits` instantiation instead.
- *`stable` presentation sensitivity* (2026-06-11): the matcher previously decomposed spines created by
  `stable` re-folding, so marking or unmarking `stable` on a definition changed which patterns were legal
  and which stuck call sites matched. Solving now requires intrinsically rigid heads (spec section 5), and
  blocked stable applications carry their stuck body so unblocking *resumes* the original instantiation —
  with captures solved once, in the call site's environment — instead of re-running it. `stable` affects
  equality strength (normalizers, stuck-spine comparison) and printing only.

One residual is documented rather than fixed: callers of binder instantiation that have no call site in
hand — `defEq`'s extensional lambda comparison and the termination checker — pass the callee's own env as
`argEnv` and therefore cannot quote solutions that close over ambient locals. Their failure mode is
conservative (equality answers false; the quote reason is surfaced if a match fails), and their arguments
are checker-internal fresh atoms, so the case is not believed constructible from source programs.
