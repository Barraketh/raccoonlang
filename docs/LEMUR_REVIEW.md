# Lemur implementation review and fix plan

This document records a review of the `lemur_features` branch against
`docs/LEMUR_ON_RACCOON.md`, and tracks the work that fixes what it found. The
review covered HEAD `1823e67`; the pre-Lemur base is `bfd5196`. Every finding
below was reproduced with a small program. A finding marked *pre-existing* is
present at `bfd5196`; the rest were introduced or exposed by the Lemur work.

## Status

| Step | Fixes | Status | Commits |
|---|---|---|---|
| S1 Ledger paths | F1, F5 | done | `7923f6e` |
| S2 Function-type identity | F2 | done | `3423042`, `57cc1ea` |
| S3 Constructor parameters from the scrutinee | F3 | done | `d776c80` |
| S4 Derived closures as capture lists; one containment rule | (refactor; retires F3's failure mode) | done | `0830800` |
| S5 Conversion assertions and hot paths | F4, perf nits | done | `6efcf4b`, `9f894c7` |
| S6 Sealing cleanup | F7, F8, F9 | done | `bbb24db` |
| S7a Parser and printer diagnostics | F10, F12, F13 | done | `973ae20` |
| S7b Elaborator field resolution and pattern spans | F11, F14 | done | `0d0f789` |
| S8 Confinement by sort scope | F6 (D1, decided) | done | `5035a69`, `b8c5f6f` |
| S9 The program's result is never linear | D2 (decided) | in progress | |

All steps are done, S8 included; the branch validates (710 tests), and every
finding's repro was rerun against the final build. Open decisions, not
scheduled: D3, D4 and the proposals under "Follow-ups" below.

## Findings

| ID | Severity | Summary | Where | Origin | Step |
|---|---|---|---|---|---|
| F1 | unsound | A token is dropped when an absurd lambda appears in its extent | `Ledger.scala:64` | Lemur | S1 |
| F2 | unsound; an internal error by default | Two different function types share a `ValueKey` | `Elaborator.scala:544`, `:371`; `Projection.scala` | pre-existing, widened by step 13b | S2 |
| F3 | kernel crash | A lambda capturing a pattern field in a branch whose index equation is stuck | `TypeChecker.scala:360`; root `MatchChecker.scala:71` | Lemur-exposed | S3, S4 |
| F4 | exponential time | Key-coherence assertions recurse under every key-equal comparison | `ValueEquivalence.scala:426` | Lemur (step 0) | S5 |
| F5 | spurious rejection | `LinearReused` after a branch that uses a local and then ends | `Ledger.scala:31` | Lemur | S1 |
| F6 | spec question | Confinement rejects types that mention a value computed under a scope elsewhere | `TypeChecker.scala:518` | Lemur | D1 |
| F7 | wrong diagnostic | A failed selector cascades into `NotFound` at `x.field` instead of a skip | `CoreAst.scala:283` | pre-existing, now routine (§3.5) | S6 |
| F8 | hardening | A custom prelude that seals `Nat` or `String` still gets literals | `Packed.scala:126` | Lemur | S6 |
| F9 | dead trust surface | The sealing exemption for fabricated terms never fires | `Sealing.scala:26` | Lemur | S6 |
| F10 | wrong diagnostic | §9 parse errors inside a function type's named binders are swallowed, and the message prints a JVM identity hash | `LanguageParser.scala:246`, `Parser.scala:221` | Lemur | S7a |
| F11 | spurious rejection | A recursive self or mutual peer shadows a sort field's forms | `Elaborator.scala:504` | Lemur | S7b |
| F12 | cosmetic | Printers drop parentheses around a function-type codomain, printing the form §9 rejects | `PrettyPrinter.scala:137`, `:239` | pre-existing, worse with closures | S7a |
| F13 | wrong diagnostic | `fun {}` and `{} A -> B` never reach "empty field list"; `returning` on the next line reads as missing; a qualified head's span starts at the dot | `LanguageParser.scala` | Lemur | S7a |
| F14 | wrong diagnostic | `h(Level.succ)` reports "not found"; a pattern field's `LinearUnused` underlines the whole branch | `Elaborator.scala:529`, `MatchChecker.scala:117` | Lemur | S7b |

### F1. A token is dropped when an absurd lambda appears in its extent

The ledger walks a lambda's body inline, as if it ran where the lambda is
written. A branchless `match` inside the body yields `ended`, and `andThen`
then counts every outer linear local as used on every path. Spec §3.2 has the
same flaw in prose: a branchless match "ends every path through it", and a
lambda's body "lies on those paths at the lambda's position".

```raccoon
inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
 | mk : Tok(l)

def drop {l: Lifetime}(t: Tok(l)): Nat := {
  let g := fun (e: Empty): Nat => match e returning Nat with
  7
}
```

This checks and returns 7; expected `LinearUnused(t)`. With the unchanged
`examples/leases/Lease.rac`, a client that binds an inline `Not(False)` proof
drops `issue(g)` inside `withLease` and never redeems it. The same drop works
for lets, parameters and pattern fields, and inside a closure's body.

### F2. Two different function types share a `ValueKey`

A function type's identity is its node id, which is its span's start offset.
`elabPi` starts the Core Pi's span at its first binder, and an anonymous binder
takes its domain's span, so `(A -> A) -> A` and its domain `A -> A` share an
id. Every generated selector header starts at the struct header, so
`P.a : (self: P) -> Nat` and `P.b : (self: P) -> Bool` collide.
`Projection.independentPiCodomain` copies a Pi and keeps its id. Step 13b's
`applicationSpan` added `(List(Nat) -> Nat) -> Nat` to the colliding shapes.

```raccoon
def k {A: Type}(f: (A -> A) -> A) : A := f(f)
{ k(fun (g: Nat -> Nat): Nat => g(5)) }
```

By default this is an internal error ("ValueKey disagrees with conversion").
With `-Draccoon.keyAssertions=false` it checks and then fails at run time with
"Cannot apply non-fn type Nat". Expected: `TypeMismatch` at `f(f)`.

### F3. Crash for a lambda in a branch whose index equation is stuck

When unifying a constructor's result type with the scrutinee's type is stuck,
`computeReachableCtors` falls back to `EqStore.empty`, and the branch's fields
keep the constructor's fresh family-parameter variables. A lambda that captures
such a field derives a closure naming a variable no local binds, and
`quoteParameter` throws. Kind parameters hit the same path. Without the lambda,
the same branch gives the pre-existing "expected: A, actual: A".

```raccoon
inductive Vec {S: Lifetime}(A: Type { scope = S }) indices (n: Nat) : Type { scope = S }
 | vnil : Vec(A, 0)
 | vcons (m: Nat)(head: A)(tail: Vec(A, m)) : Vec(A, Nat.succ(m))

def double (n: Nat): Nat := Nat.add(n, n)

def headOr {S: Lifetime}{A: Type { scope = S }}(k: Nat)(d: A)(v: Vec(A, double(k))): A := match v returning A with
 | .vnil => d
 | .vcons m h t => (fun (u: Unit): A => h)(Unit.unit)
```

Expected: accepted, with `h : A`. Parameters are uniform, so they never need
unifying; only indices do.

### F4. Key-coherence assertions are exponential on shared values

`keyAssertionsEnabled` defaults to true, in the CLI and the benchmark scripts
too. Every key-equal equation reruns `structurally`, and every sub-equation
does the same, walking a DAG as a tree. `dup(t) := node(t, t)` iterated `n`
times, then `Eq.refl(big(n))`: 3.6s against 0.86s at `n = 22`, 20s against
0.8s at `n = 25`. The assertion is also what turns F2 into an error rather than
a wrong answer, so it should stay on, at linear cost.

### F5. Spurious `LinearReused` after an ended branch

`Uses.andThen` treats `first`, a use on any path, as a use on a path that
continues. So a use followed by a branchless match in one branch counts against
a later use:

```raccoon
def f {l: Lifetime}(t: Tok(l))(b: Bool)(e: Empty): Nat := {
  let first := match b returning Nat with
    | .true => {
      let n := eat(t)
      match e returning Nat with
    }
    | .false => 0
  Nat.add(first, eat(t))
}
```

Every path reaching the last line uses `t` once. Actual: `LinearReused(t)`.

### F6. Confinement reads a value's whole dependency set

`requireInScope` answers from `synDeps`, which includes atoms held in closure
environments and in stuck calls. `later` in `examples/leases/main.rac` may
leave its scope, but `Eq.refl(later)` is `LifetimeEscapes`, and so is
`Eq(Nat, withLease(f), withLease(f))`, with a message naming a `scope` in
`Lease.rac`. The result also depends on representation: `Eq(Unit -> Nat, f, f)`
is rejected while the same equation about `fun u => f(u)` passes. This follows
§4.2's "the dependency set answers it" but contradicts its "a value … whose type
neither mentions l … may leave". It is over-conservative, not unsound. See D1.

### F7–F14

- **F7.** `Decl.references` skips a declaration that names a failed one only
  through `GlobalRef`, but `x.f` becomes `Family.f` at check time. With a
  failing selector, `def get (p: PS(True)): Nat := p.n` reports `PS.n not found`
  where `PS.n(p)` is skipped.
- **F8.** `Packed.validateNatFamily` and the String, Char and List layouts do not
  check `meta.seal`, so with a prelude declaring `sealed inductive Nat`,
  `def five : Nat := 5` checks while `Nat.zero` is `SealedConstructor`.
- **F9.** `Sealing.accessible` exempts sites in the synthetic source, but no
  checked term has a synthetic span. The exemption is unreachable trust
  surface, and `Seal.module` is optional only to allow it.
- **F10.** `namedSegment` wraps binders in `Attempt`, which turns a thrown
  `ParseError` into a backtrack. `def g (h: (A: Type { level = Level.one }) -> Nat)`
  reports `Failed to parse com.raccoonlang.Parser$OrParser@1937eaff` instead of
  "misplaced field level". The same for empty field lists, missing levels,
  unknown fields and misplaced closures inside a function type's binders.
- **F11.** Recursive self and mutual peers are bound as locals, which win over
  a field's forms: a recursive `def succ` whose body writes
  `Sort { level = succ(u) }` resolves `succ` to itself.
- **F12.** `Nat -> (Nat -> Nat)` prints as `Nat -> Nat -> Nat`; with closures
  the printer emits `Nat -> { scope = l } Nat -> Nat`, which §9 rejects.
- **F13.** `closureStart` requires `{ name =`, so `fun {} (x: Nat): Nat => x`
  gives a garbled message rather than "empty field list". A match header split
  before `returning` reports the clause missing. `Select` spans cover only
  `.name`, so `Nat.add(…)` is underlined from the dot.
- **F14.** An unapplied non-nullary form reports `Level.succ not found`, though
  the name exists; it should be an arity error. `LinearUnused` for a pattern
  field is located at the whole branch because `CoreAst.Case` refs carry no
  spans.

## Open decisions

- **D1 (F6). Decided 2026-09-29: adopt, as S8.** Confine by the type's sort scope instead of its dependency set.
  §2.4 built the sort scope to count exactly what a value can hand over, so
  `requireInScope` would become "the sort's scope, less the open atoms, is
  empty": constant time, and blind to atoms held inside data. It needs §5.1 to
  require every family, not only linear ones, to name each lifetime parameter
  in its scope; today `inductive Wrap (l: Lifetime) : Type` sits at scope `{}`,
  so `Wrap(atom)` would escape. The alternative is to keep the dependency-set
  rule and say in §4.2 that a type mentioning a value computed under a scope is
  confined to it.
- **D4 (from S8).** A family's declared scope is now fully determined: it may
  mention only the family's parameters and must name every lifetime parameter,
  so it is exactly their union. Writing it is checked ceremony. Keep writing it
  (explicit; `Lease (l: Lifetime) : Type { scope = l }` tells a reader it is
  confined), or derive it and disallow writing it (less to write, but it drops
  "kind and scope are declared, never derived" for scopes while kinds stay
  declared, and changes surface syntax across the prelude and tests).
- **D2. Decided 2026-09-29: reject, as S9.** The program's final `{ … }` result
  may have a linear type and is not tracked, so a client of a sealed module can
  end the program holding its token (`{ openFile(Unit.unit) }`, or a linear
  closure that would close it), the one place a token can be dropped outside its
  module; and `def main : Handle := …` is `LinearGlobal` while the same
  expression as the result is accepted.
- **D3.** Every family in a `mutual` block must have the same sort, kind and
  scope included (`InductiveChecks.scala:485`). `kernel.md` documents it; the
  spec only says a sibling is read by its declared classifier.

## Fix plan

Each step is one worker, one reviewed commit (or a few), and `sbt validate`
green. Every step adds regression tests for the findings it fixes: the program
the finding quotes must reach the expected outcome. Where a step changes a rule
the spec or `docs/kernel.md` states, it updates that text in the same commit.

### S1. Ledger paths (F1, F5)

Rework `Ledger.Uses` so it tracks the first use on a path that continues
separately from the first use on any path, and give a lambda and a function
type their own path boundary: a lambda whose `refs` do not mention the local
contributes nothing; otherwise its body's paths are summarized as one use at the
lambda's position, a path the body ends does not end the enclosing path, and a
body path that does not use the local still makes the local unused. Fix §3.2's
wording to match, and the Linearity section of `kernel.md`.

### S2. Function-type identity (F2)

Give every identity-bearing Core node (Pi, Lam, Match, Scope) a node id that no
other node of its kind with different syntax shares: build the Core Pi from the
surface Pi's own span, give each generated selector header its own span, and
give the Pi that `Projection.independentPiCodomain` builds an identity of its
own. Audit every place the elaborator and the inductive checks build a span for
an identity-bearing node. Add a test that no two such nodes with different
syntax share an id across the prelude, the examples and the diagnostic
fixtures. Update fixture underlines that move.

### S3. Constructor parameters from the scrutinee (F3)

In match checking, instantiate a constructor's family parameters from the
scrutinee type's parameter arguments, and freshen only its indices and fields.
Parameters are uniform, so this needs no unification, and a stuck index
equation no longer loses them. This fixes F3's crash at its root and the
"expected: A, actual: A" mismatch in stuck branches. If the same change makes
`tryUnifyNeutralMatches` succeed for parameterized families, apply it there too.

### S4. Derived closures as capture lists; one containment rule

A lambda's omitted closure field is carried in the residual as its captured
locals, and evaluation derives the kind and scope from their types' sorts, as
§4.3 defines them. This deletes `quoteParameter`, `quoteKind`, `quoteLifetime`
and `assertDerivedClosure`, and with them the invariant F3 broke. Fold the two
halves of `checkLamClosure` and the family field and parameter checks into one
containment helper for `KindExceeded`/`ScopeExceeded`, and add
`Sorts.checkedSort` for the two places that pair `LinearProp` with
`Sorts.sort`. Update spec §8 (Residuals) and `kernel.md`.

### S5. Conversion assertions and hot paths (F4)

Run the key-coherence assertion only at the outermost comparison, so nested
comparisons use the fast path and the check costs one structural pass; keep it
on by default. Also: make `VSort.tpe` a lazy val and give `Linearity.isLinear` a
`VSort` case; replace the `orElse` chain in `synthesize`; test `VPi | VLam |
NeutralThunk` before `isKnownProof` in `needsStructuralDefEq`; iterate
`bodyRefs` in `lambdaCaptures`; remove the unreachable `Var`-of-a-parameter arms
in `Level.fromValue` and `normalizeLevel`; share one helper between the kind and
lifetime normalizers and materializers; state "later-bound first" directly in
`unifyParameters`; stop `FreshVar.parameterNames` growing with runtime work if
that is simple; and update `benchmarks/nested_zip.py` to the current syntax.

### S6. Sealing cleanup (F7, F8, F9)

`Seal(family, module: SourceId)` with no synthetic exemption; the elaborator
attaches the seal to generated selectors, replacing `selectorOf` and the
family lookup in `Interpreter.evalDecl`; the native literal layouts refuse a
sealed family; `Decl.references` treats `base.f` as naming any `*.f`.

### S7a. Parser and printer diagnostics (F10, F12, F13)

A committed `ParseError` that `Attempt` does not swallow, thrown by the field
list and closure errors; one table-driven sort former, so bare `Sort` and
`Sort(u)` get the §9 message; an empty closure reaches "empty field list"; a
`Select` span starts at its base; `returning` may start the next line; both
printers parenthesize a function type in codomain position.

### S8. Confinement by sort scope (F6, D1)

Two rule changes. §4.2: a type is `LifetimeEscapes` when the scope of its sort
names an atom whose `scope` is not open, at the same three kinds of site as
today; a type's dependency set no longer decides it. §5.1: every family, not
only one at a kind other than `Kind.unr`, names each lifetime parameter in its
scope, so that §2.4's claim holds literally: a type's sort scope counts every
lifetime that can be read off it, a forced implicit's included. Without the
second change `Wrap(atom)` for `inductive Wrap (l: Lifetime) : Type` would sit
at scope `{}` and leave its scope, and a module that treats such a family as
evidence of being inside the scope would be fooled.

Expected outcomes (all against the unchanged `examples/leases/Lease.rac`):
`Eq.refl(later)`, a proposition about `withLease(f)` for an abstract `f` used as
a type, and `congrArg` over `withLease` are accepted; `later`, its eta-expanded
twin and concrete-callback statements stay accepted; a `Lease(l)`, a `Tok(l)`
or a closure capturing a lease still cannot leave `scope l`; and
`scope l => Wrap(l)` is rejected at the `scope`, where today the type value
escapes and only its later use is caught. Costs accepted: lifetime-parameterized
families must be scoped (about six test families, three `.rac` test files, the
§6.2 and §7.3 spec examples; the prelude already complies); instances of a
family at different lifetimes live in different sorts, so §6.2's lifetime
equations arise only between instances sharing a scope; confinement now rests
on the sort-scope bookkeeping, so each rule that computes a sort scope gets a
targeted escape test.

### S9. The program's result is never linear (D2)

The program's result is a value outside every binder, like a global, so its
type may not be linear. It is reported as `LinearGlobal`, generalized from a
definition to any value outside every binder, so §9's list is unchanged. §3.2
says so. Tests: against a sealed module whose protocol is "every handle it opens
is closed", `{ openFile(Unit.unit) }` and a result that is a linear closure are
rejected, and `{ closeFile(openFile(Unit.unit)) }` is accepted.

### S7b. Elaborator field resolution and pattern spans (F11, F14)

Field forms as a plain map consulted right after locals and before recursive
self and peers; one helper for "written field or default" in place of the
three copies; an unapplied non-nullary form is an arity error; pattern fields
carry spans, and `LinearUnused` for one points at it.

## Log

- 2026-09-29: review complete; plan written.
- 2026-09-29: S1 landed (`7923f6e`). Beyond the brief: code after a branchless
  match now lies on no path, so a double use there is no longer reported; the
  `Pi` boundary has no surface test, since a function type that mentions a
  linear local is already `LinearInType`. `docs/language.md` updated too.
- 2026-09-29: S3 landed (`d776c80`). One builder, `BinderOps.freshCtorFields`,
  now serves match refinement, `EqStore.allowEta` and `tryUnifyNeutralMatches`;
  the last now succeeds for parameterized families whose indices agree, where it
  used to give up on every parameterized family. The kind-parameter repro
  (`stuckkind.rac`) is now its correct `LinearUnused` rather than a crash.
- 2026-09-29: S2 landed (`3423042`, `57cc1ea`). Function types keep their
  surface span; selector headers take their field's span. A third collision
  turned up: a selector's result type was rewritten from the field's type but
  kept its spans. The first fix gave rewritten Pis synthetic identities; on
  review that was replaced by generating a selector's result type as the
  field's own type under `let`s binding the earlier fields it mentions, which
  deletes `rewriteFieldType` and makes identity correct by construction.
  `NodeIdentityTests` asserts the invariant over the preludes, examples and
  fixtures. Proposed, not scheduled: an explicit identity field on Pi, Lam,
  Match and Scope, so no future desugaring can reuse a span for different
  syntax.
- 2026-09-29: S4 landed (`0830800`). A derived closure field is carried as
  `ClosureField.Derived(captures)`, leaving out captures that contribute
  `Kind.unr`/`Lifetime.empty` at check time; `Interpreter.derivedField` derives
  it for checking and evaluation alike. `quoteParameter`, `quoteKind`,
  `quoteLifetime`, `assertDerivedClosure` and `evalSort` are gone.
  `Sorts.requireContains` is the one containment rule (four former call sites)
  and `Sorts.checkedSort` the one `LinearProp` check. No measurable change on a
  closure-heavy benchmark. Spec §8 and `kernel.md` updated. The merged branch
  validates (694 tests).
- 2026-09-29: S6 landed (`bbb24db`). `Seal(family, module: SourceId)` with no
  exemption; `Elaborator.familySeal` is the one place a seal is made, for a
  family's constructors (`InductiveDecl.seal`) and its selectors
  (`ConstDecl.sealedBy`), so `Interpreter.evalDecl` no longer looks the family
  up. A sealed `Nat`, `String`, `Char` or `List` makes its literal layout
  unavailable, and since `finishPrelude` rejects a malformed layout, such a
  prelude now fails to load. `Decl.references` treats `base.f` as naming any
  failed `*.f`. The merged branch validates (697 tests).
- 2026-09-29: S7a landed (`973ae20`). `Attempt` is deleted: a binder commits
  once `(name :` or `{name :` is read, so §9 errors inside Pi binders report as
  themselves (`ParseErrorTests` reaches each in eight positions). No parse
  failure prints a parser object any more. One table-driven sort former; `{}`
  closures reach "empty field list"; `Select` spans start at their base (seven
  fixtures' underlines moved to the qualified head); `returning` may start the
  next line; both printers parenthesize a function-type codomain; a stuck field
  projection prints as `P.x(v)` (heuristically: any one-branch match returning a
  field of a one-constructor family). Left alone: an implicit-first Pi in term
  position (`{A: Type} -> A -> A`) still parses as a block; `{ }` as a term now
  says "Empty field list". The merged branch validates (708 tests).
- 2026-09-29: S5 in review. First version asserted key verdicts one step deep,
  which removed the exponential cost (p2: 69s to 1.6s) but no longer caught a
  collision hidden under a parent whose keys agree because of it; sent back to
  assert at every depth with an identity memo of checked pairs.
- 2026-09-29: S5 landed (`6efcf4b`, `9f894c7`). Key assertions stay on by
  default and assert beneath every key verdict, each object pair once per
  outermost assertion (p1 n=22: 6.9s to 1.5s; p2 n=25: 53s to 1.8s; a test
  shows a collision beneath an agreeing parent is still an internal error).
  Also: `VSort.tpe` is lazy; `isLinear` short-cuts sorts; `synthesize` without
  by-name thunks; `needsStructuralDefEq` tests function types before proofhood;
  `lambdaCaptures` walks `bodyRefs`; the unreachable `Var`-of-a-parameter arms
  and `Level.fromValue` are gone; one `materializeParameter`; `unifyParameters`
  states later-bound first; `checkPi` has no default parameter;
  `benchmarks/nested_zip.py` generates current syntax. Skipped:
  `FreshVar.parameterNames` (any sort-parameter variable may be printed), and
  sharing `normalizeKind`/`normalizeLifetime` (longer, not shorter). The
  merged branch validates (710 tests).
- 2026-09-29: S7b landed (`0d0f789`). `elabPath` states the one resolution
  order: local, the field's forms, the recursive group's members (no longer
  bound as locals), then globals. One `elabField` helper; an unapplied
  non-nullary form is `ArityMismatch(arity, 0)`; pattern variables carry spans
  through `SurfaceAst` and `CoreAst` (`PatternVar`), so `LinearUnused` points at
  the variable, `_` included. The mutual-peer repro (n2c) passed `Nat` where a
  `Type { kind = lin }` is required, which is rightly `TypeMismatch`; the test
  uses a linear type. The merged branch validates (714 tests), and every
  finding's repro behaves as expected on the final build.

- 2026-09-29: S8 landed (`5035a69`, `b8c5f6f`). `requireInScope` reads the
  type's sort's scope and nothing else (a dependency-set pre-filter was dropped
  on review: it saved about 3% but made confinement rest on a second
  invariant). Every family names each lifetime parameter in its scope. With
  that, a family's scope is exactly its lifetime parameters, so the field-scope
  and parameter/index-type-scope containment checks could no longer fail and
  were deleted, with §5.1 stating why; field kind containment stays. Now
  accepted: `Eq.refl(later)`, a proposition about `withLease(f)` used as a
  type, and `congrArg` over `withLease`. Still `LifetimeEscapes`: every rule
  that computes a sort scope has an escape test (`ScopeTests`). Newly rejected:
  an unscoped lifetime-parameterized family, and `scope l => Wrap(l)` at the
  `scope`. Spec §2.4, §4.2, §5.1, §6.2 (`Pair` example) and §7.3 (`pairEq`)
  rewritten. The fixtures `scope-exceeded-parameter` and
  `scope-exceeded-lifetime-parameter` merged into `scope-exceeded`. The merged
  branch validates (710 tests).

## Follow-ups (proposed, not scheduled)

- **Explicit node identity** (from S2). Identity is a span's start offset, so
  any future desugaring that reuses a source span for different syntax brings
  F2 back. An identity field on Pi, Lam, Match and Scope, assigned by the
  elaborator, would make that impossible; `NodeIdentityTests` guards it today.
- **Field projection printing** (from S7a). The printer shows any one-branch
  match returning a field of a one-constructor family as `P.x(v)`, including a
  plain `inductive` that has no selector `P.x`; the kernel does not record which
  families are structs.
- **Implicit-first Pi in term position** (from S7a, pre-existing).
  `{A: Type} -> A -> A` as a term is read as a block.
- **`with` on the next line** (from S7a). `returning` may start the next line;
  `with` still may not.
- **Duplicated `parseFailure` helper** in `ClosureTests`, `UniverseTests` and
  `ScopeTests`.
- **Materializing shared values** (from S5 review). `ValueOps.materialize`
  rebuilds a shared value without a memo, so it walks a DAG as a tree whenever
  the store has solved variables it mentions.
