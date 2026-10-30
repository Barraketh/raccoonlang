# Kernel follow-ups after linear protocols

**Status: 2026-10-30.** Candidate changes for review and decision. 3.5 is
decided and implemented. On `kernel-followups-matching`, 1.3 is confirmed, the
bugs 1.5 and 1.6 are fixed, and 2.4 to 2.7 are implemented; each item's status
line says how. They were found while
implementing [linear protocols](../implemented/LINEAR_PROTOCOLS.md), porting
Track A (`lemur-raccoon/experiments/protocols-clean`), and running the
adversarial linearity review (`LinearEscapeTests`). Items marked *port* exist
on `main-new` and can be ported rather than designed. "Open question N" is
item N of the design record's open questions.

The language decides these, not the formalization. The formalization's design,
`raccoon-formalization/DESIGN.md` (in progress), checks each item against its
model, and a gap it finds is the model's to close.

## Summary

| # | Item | Group | Source | Open question |
|---|---|---|---|---|
| 1.1 | `Tensor` refinement at copyable arguments (gone with cumulativity) | bug | new | 19 |
| 1.2 | Results take their body's type, not the declared codomain (gone with cumulativity) | bug | new | 17 |
| 1.3 | Applying a stuck application, or a projection of a call (fixed) | bug | new | — |
| 1.4 | Smaller defects: an unlocated internal error, `AlreadyDefined` without a span, open shadowing | bug | new | — |
| 1.5 | Branch fields typed at fresh parameters when an index equation is stuck (fixed) | bug | port | — |
| 1.6 | Positive arguments of a family read its own occurrences as positive (fixed) | bug | new | — |
| 2.1 | Structure eta (implemented) | expressiveness | port | — |
| 2.2 | Positivity of stuck computations (implemented) | expressiveness | port | 18 |
| 2.3 | Bundled protocol families (implemented) | expressiveness | follows | — |
| 2.4 | Structural recursion on indexed families with variable indices (implemented) | expressiveness | new | 16 |
| 2.5 | Mutual inductives and mutual recursion (implemented) | expressiveness | port | — |
| 2.6 | Wildcard case (implemented) | expressiveness | port | — |
| 2.7 | Match equations (implemented) | expressiveness | port | — |
| 2.8 | Partial application and lambdas in types | expressiveness | new | 3 |
| 2.9 | Implicit arguments on definitions and inferred erased binders | expressiveness | partly port | — |
| 3.1 | Kind polymorphism (decided and implemented) | design | new | 10 |
| 3.2 | Linear closures | design | new | 11 |
| 3.3 | Supply splitting | design | new | 6 |
| 3.4 | Universe-polymorphic protocols | design | new | 12 |
| 3.5 | Relaxing S1 for reads (decided and implemented) | design | new | — |
| 3.6 | Exactly-once versus affine use (decided and implemented: affine) | design | new | 7 |
| 4 | Prelude, parser, diagnostics, checking speed | not kernel | — | — |

## 1 Bugs

### 1.1 `Tensor` refinement at copyable arguments (open question 19)

**Decided 2026-10-30:** superseded by [KINDS.md](KINDS.md). `Tensor` is retired, and removing cumulativity removes the level disagreement behind this bug. **Implemented:** without cumulativity `Tensor(Nat, Nat)` is `TypeMismatch`, and `Prod(Nat, Nat)` refines its fields (`LinearTests`).

**Problem.** Matching `Tensor(Nat, Nat)` leaves its fields' types as fresh
variables, so `Nat.add(a, b)` on the fields is `TypeMismatch`. `Tensor`'s
parameters are level-captured `Lin($u)` and `Lin($v)` in
`Lin(Level.max(u, v))`. The fields are refined as expected in each of these
cases:
- one argument is linear;
- the family has one level;
- one parameter is a `Sort` capture;
- the levels are fixed.

**Evidence.** `docs/kernel.md`, the limit after L9.

**Proposal.** Locate it; the likely suspect is unifying `Level.max(u, v)` when
both captures come from `Sort` arguments. It is not a blocker, since the
library's tensors always hold a packet, but it is a plain refinement bug.

### 1.2 Results take their body's type (open question 17)

**Decided 2026-10-30:** superseded by [KINDS.md](KINDS.md). Without cumulativity a value is used at exactly its universe, so its own type and its declared type cannot disagree. **Implemented:** `same(Nat)` for `same (A: Lin(0)) : Eq(Lin(0), A, A)` is `TypeMismatch`, and `same(LNats)` is used at its declared type (`LinearTests`).

**Problem.** A function's result is typed by the value its body computes, not
by the declared codomain. `Eq.refl(A)` returned at declared type
`Eq(Lin(0), A, A)` therefore comes back at `Eq(Type, Nat, Nat)` when `A := Nat`.
Cumulativity applies at arguments only, so the declared type is lost and
cannot be recovered.

**Evidence.** `docs/kernel.md` L8, and the prelude's `Eq.substLin`: a cast along
`Eq(Lin(0), A, B)` checks for linear `A` and `B` but not at copyable instances.

**Proposal.** An application's type is its function's declared codomain at the
arguments, and likewise a let's type is its annotation. Values may keep their
intrinsic types for evaluation, but the type checker reports the declared one.
This also makes cumulativity at results (`Sort ≤ Lin`) work.

### 1.3 Applying a stuck application, or a projection of a call

**Fixed 2026-10-30** with structure eta: applying a neutral function value, a stuck application or a projection, gives
a neutral application (`Interpreter.evalApply`). **Confirmed 2026-10-30** on the follow-ups branch: both symptoms
check, `g(k)(2)` for an axiom `g`, a cast along an axiom applied to an argument, and a projection of a recursive
call's result applied to one, as `ProjectionOfCall.rac` wrote it (`StructEtaTests`, "applying a stuck application").

**Problem.** Two symptoms:
- `Interpreter.evalApply` has no case for a stuck application (`VApp`), so
  applying one fails with "Cannot apply non-fn type". The adversarial review
  hit this with an axiom whose codomain computes to a function type.
- Track A hit the same message applying a projection of a recursive call's
  result. It unpacks such results with `let (a, b) := …` instead.

**Evidence.** `lemur-raccoon/experiments/protocols-clean/friction/ProjectionOfCall.rac`,
and `LinearEscapeTests` (the stuck-codomain S3 case).

**Proposal.** Applying a stuck application yields a stuck application,
blocked on its head's blockers. Confirm that this one change covers both
symptoms.

### 1.4 Smaller defects

**Decided 2026-10-30:** for the open-name precedence, a selective open (`open X.{a}`) beats a name in the enclosing namespace, and a wildcard open keeps today's rule. The other defects are plain fixes.

- **Unlocated internal error.** A constructor capture that does not match its
  parameter's universe throws "Cannot return idx 0 of Lin(…)" with no location.
  It should be a located type error. (Fixed for `Sort` and `Lin` captures, which
  now open on any universe and give a located `TypeMismatch`; a capture through
  a user alias for `Lin` still reports it.)
- **`AlreadyDefined` has no span**, so the redeclaration tests compare names.

A design question rides along: **should opened names win over the enclosing
namespace?** `docs/namespaces.md` specifies that members of the enclosing
namespaces resolve before opened aliases, and resolution follows it, so inside
`namespace Protocol` an opened `Proto.Valid` loses to the kernel's
`Protocol.Valid`. That is why the library's `Exclusive` and `Shares` are
top-level namespaces and `Morphism` opens the bundled families under aliases.
Letting an explicit `open` win would be closer to what a reader expects of a
local import, at the price of a name's meaning changing when an `open` is
added; either way it is a change to `docs/namespaces.md`, not a bug fix.

### 1.5 Branch fields typed at the scrutinee's parameters

**Fixed 2026-10-30**, porting `main-new`'s `f598d033` (`MatchChecker.freshCtor`; `docs/kernel.md`, "Refinement
outcomes"; `MatchRefinementTests`).

**Problem.** A match on `v: Vec(A, f(n))`, for an unknown `f`, rejected `| Vec.cons tail head => head` at result type
`A` with "expected A#3608, actual A#3614". Found while comparing `main-new` with `main-clean`
([EVALUATION_AND_PORTS.md](EVALUATION_AND_PORTS.md) §3, #3).

**Cause.** Match checking gave every binder of a constructor's telescope a fresh variable, the witnesses of the family's
parameters included, and related them to the scrutinee's parameters only through the branch's refinement. When an index
equation was stuck, the branch kept no refinement at all, so its fields' types were over parameters that nothing bound.

**Fix.** A constructor's telescope is opened at the scrutinee's own parameters: each witness of a parameter, an erased
binder or a capture named like the parameter, is linked to the scrutinee type's argument before refinement. Parameters
are uniform, so this needs no equation, and only the fields and the captures the parameters do not determine are
unknowns of the constructor's side. A witness whose type is narrower than its parameter's, such as `$A in Sort($u)` for
`A: Univ($k, $u)`, is related by the refinement, as an index is. The ledger and the read rules are unaffected: the
fields are the same locals, tracked by the same types, now at the scrutinee's parameters.

### 1.6 Positive arguments read a family's own occurrences as positive

**Fixed 2026-10-30** with mutual families (2.5; `docs/kernel.md`, "Mutual blocks"; `MutualTests`).

**Problem.** A family's positive arguments, those that may hold a nested occurrence of a later family, were computed in
one pass over its constructors, reading the family's own occurrences by its provisional metadata, in which every
argument is positive. So `inductive F (A: Type)(B: Type) | leaf | mk (f: (a: A) -> Nat)(x: F(B, A))` had `B`
positive, although it reaches `F`'s negative first argument, and `inductive H | mk (h: F(Nat, H))` was accepted with
`H` in a negative position. Found while porting the mutual families' positivity, which `main-new` computes as a fixed
point.

**Fix.** The positive arguments are the greatest fixed point over the block, a single family being a block of one,
starting from what the headers allow.

## 2 Expressiveness gaps that force encodings

### 2.1 Structure eta (*port*)

**Decided 2026-10-30:** follow `main-new`. Every family that has one constructor, no indices and no recursive field, and is not in `Prop`, gets structure eta and generated field selectors, at every kind, linear ones included. The model validates eta for carriers, and relaxed S1 lets conversion compare linear values. The `struct` keyword is removed: a struct is an `inductive` that meets those conditions. `Observed` and `Fresh` then get selectors without further change. **Implemented** (`docs/kernel.md`, "Structure eta and projections"). Every one-constructor family gets selectors, indexed ones too, as `struct` gave them; eta needs the conditions above, and a family whose field depends on a capture its arguments do not determine has neither.

**Problem.** Without eta, a variable `P : Proto` does not convert with
`Proto.mk(P.Atom, P.Step)`. This is half of why every protocol family and
primitive takes the atom type and step relation separately
([linear protocols](../implemented/LINEAR_PROTOCOLS.md) §3.1), and why
`Toks(Atom, Step, init, s, C)` has five arguments.

**Proposal.** Port `main-new`'s structure eta (`docs/kernel.md`, "Structure
eta and projections"; `docs/implemented/PAIRS_AND_PRELUDE.md`). It applies to
eligible non-Prop structure instances. It must not apply to linear
structures. That restriction holds without extra code: by S1, conversion never
compares linear values. Eta views of refinable values at the refinement
boundary, as `main-new` does them, need a check against the linear match rules
(L4).

### 2.2 Positivity of stuck computations (open question 18, *port*)

**Implemented 2026-10-30** (`docs/kernel.md`, "Family argument size", the
paragraph on fresh families): a stuck computation certifies the family's absence
when its type, captures, environment values and match term do not mention it.

**Problem.** Strict positivity rejects any stuck match in a constructor field
type: `InductiveHead.mayOccurIn(NeutralThunk)` is `true`. That rejects:
- a selector of a parameter, `List(P.Atom)`;
- a stuck call of a global defined before the family, `Eq(Nat, n, double(k))`;
- `Morphism` as a structure.

Predicates with computed parts must therefore be definitions over `And`, `Or`
and `Exists`.

**Evidence.** `lemur-raccoon/experiments/protocols-clean/friction/BundledReach.rac`
and `StuckFieldType.rac`.

**Proposal.** Port `main-new`'s declaration-time positivity
(`docs/implemented/DECLARATION_TIME_POSITIVITY.md`). There, a stuck
computation certifies the family's absence when its type, its captures, its
environment's locals and, for a declaration block, the term it evaluates do not
mention the family. A stuck application of an earlier global, or a selector of
a parameter, then passes.

### 2.3 Bundled protocol families, once 2.1 and 2.2 land

**Decided 2026-10-30:** bundle the families. Refine the nominal size rule so that a record argument is charged by its fields, so that `Toks(P, init, s, C)` stays in `Lin(0)`. A `Proto` costs level 0, since its fields are `Atom : Type` and a relation into `Prop`. `raccoon-formalization/DESIGN.md` §10 argues that the refinement is sound. **Implemented 2026-10-30:** the kernel families and primitives take a `Proto`, the size rule charges a record with structure eta by its fields, and the library's bundled wrappers are gone; the GPU port is not migrated.

With eta and the refined positivity check, the kernel families can take a
`Proto` again:

```text
Inst(P, init)
Tok(P, init, s, a)
Toks(P, init, s, C)
Observed(P, init, s, C)
Fresh(P, init)
```

So can `Reach`, `Valid` and the primitives. This reverses the
component-parameter decision ([linear protocols](../implemented/LINEAR_PROTOCOLS.md)
§3.1), and the library's bundled wrappers (`Protocol.Proto.Reach` and the
others) become the kernel's names. It is a migration of
`Kernel.ProtocolSource`, the primitives' argument positions, the tests, the
library and the GPU port. Do it in one step after 2.1 and 2.2.

**It changes a level unless the size rule changes with it.** Under the current
family argument size check a `Proto` parameter costs level 1, since
`Proto : Sort(1)`, so a bundled `Toks(P, init, s, C)` would be in `Lin(1)`,
not `Lin(0)`, with `Tok`, `Observed` and `Fresh`, and every packet function
would be in `Sort(1)`. The component form costs nothing, since a `Type`
parameter and a relation on it are charged level 0. The formalization's design
admits a refined size rule that charges a record by its fields, under which a
`Proto` argument costs level 0, as its components do: every `Proto` value lies
in the model's level-0 labels (`raccoon-formalization/DESIGN.md` §4.5 and §10).
Whether to adopt that rule, or accept `Lin(1)` packets, is part of this
item.

### 2.4 Structural recursion on indexed families with variable indices (open question 16)

**Implemented 2026-10-30** (`docs/kernel.md`, "Refinement outcomes"; `ProtocolTypesTests`). The unification that links
a variable scrutinee to the matched constructor refines the variables of the scrutinee's type too, exactly the set the
result refinement may refine, so a variable index is solved and the scrutinee linked in one step. The full suite and
the refinement tests pass unchanged. The proof-root link stays separate: unification compares proofs by their
propositions and never links one, and a Prop family's instances do not unify structurally, so a proof scrutinee still
takes the result refinement and its explicit link, made only where that refinement succeeds. `lib/Protocol`'s
`Toks.append` now recurses on the packet; `Toks.split`, whose packet is at the computed index `List.append(A, B)`,
still recurses on `A`.

**Problem.** `decreases structural(v)` on an indexed data or linear family
fails with `NonDecreasingRecursiveCall` whenever the index is a variable,
whether it is a captured index or an explicit parameter. Linear packets are
exactly this case. `split`, `join` and `exchange` therefore recurse on the
unrestricted list, or use `measure(List.length(…))`. Indexed Prop families
recurse already: a proof scrutinee is linked to its constructor explicitly,
in each branch whose refinement succeeds (`docs/kernel.md`, "Recursion on
proofs").

**Cause.** In `MatchChecker.computeReachableCtors`, the unification that links
a data scrutinee to the matched constructor may refine only the scrutinee and
the constructor's fresh variables. The index equation stays stuck there, so
the termination checker never sees the field as smaller.

**Proposal.** Let that unification also refine the variables of the
scrutinee's type, as the branch refinement already does. It touches every
match, so it needs the full suite, the refinement tests and a review of the
proof-root linking, which could then become the same link.

**Evidence.** `ProtocolTypesTests` pins the failing and the working form.

### 2.5 Mutual inductives and mutual recursion (*port*)

**Implemented 2026-10-30** (`docs/kernel.md`, "Mutual blocks"; `MutualTests`): `mutual { … }` of only families or only
definitions, checked and published as a block. Families are checked each against its own declared universe (L1, L2,
the size rule), with strict positivity in every family of the block and positive arguments as a fixed point over it
(which fixed 1.6). Definitions call their peers through raw calls that compare the callee's metric at the call with
the caller's own; the ledger and the read rules are those of any application. Two departures from `main-new`, neither
needed for soundness: the families need not share a parameter telescope, since `main-clean` already lets a recursive
occurrence stand at other parameters (L9), and a block may mix `measure` with one-component metrics, since every
component is ordered by one well-founded order on all values.

**Proposal.** Already planned. `main-new` has mutual families; its nominal
size rule charges "each mutual family's own grade". For linear families,
mutual blocks need the same field rules (L1–L3) and the ledger over mutually
recursive definitions, but nothing beyond them.

### 2.6 Wildcard case (*port*)

**Implemented 2026-10-30** (`docs/kernel.md`, "Wildcard cases"; `WildcardCaseTests`), as on `main-new`: the residual is
the expansion, each case with a fresh copy of the body, and `RedundantCase` is new. A wildcard drops linear fields,
each expansion is its own path for the ledger, and a read extent's expansions keep separation per call. Not ported:
`main-new` frames a failure inside an expansion with its constructor, and `main-clean`'s diagnostics have no frames.

**Problem.** Every match lists every reachable constructor. In Track A, 67 of
the 88 frame-lemma cases were trivial.

**Proposal.** Port `| _ => e` (`docs/implemented/WILDCARD_CASE.md`): one case
for each reachable constructor that the earlier cases do not name, each checked
under its own refinement. For linear scrutinees the ledger must check `e` once
per expanded case. A wildcard binds each case's fields anonymously, so it
drops a linear field, which affine use allows.

### 2.7 Match equations (*port*)

**Implemented 2026-10-30** (`docs/kernel.md`, "Match equations"; `MatchEquationTests`). As on `main-new`, `e` must be
copyable data (`MatchEquationUnavailable` for a linear, kind-polymorphic or proof scrutinee), and the `Eq` used is the
global one only when it is exactly the equality family. Unlike `main-new`, which refused every indexed family, an
indexed family is accepted wherever a case's refinement equates the constructor's indices with the scrutinee's, and a
case where it does not is `MatchEquationIndexed`: rejecting the others would refuse sound programs for no saving.

**Proposal.** Port `match h : e returning M with …`
(`docs/implemented/MATCH_EQUATION.md`), which binds `h : Eq(T, e, C(…))` in
each case. This is the "inspect" pattern, which Track A wrote by hand. `e` must
be unrestricted, since `Eq` has no linear carrier (L8).

### 2.8 Partial application and lambdas in types (open question 3)

**Decided 2026-10-30:** no partial application. Raccoon functions are n-ary telescopes, and partial application would hide arity errors, while at a linear argument it would be a linear closure. Every use in Track A was a predicate inside a statement, so lambdas in types cover it. Lambdas in types stay in scope.

**Problem.**
- A two-argument function value cannot be applied to one argument, so every
  higher-order argument is eta-expanded by hand.
- Types cannot contain lambdas, so Track A needed about 11 named predicate
  helpers.

**Evidence.** `friction/PartialApplication.rac`, `friction/LambdaInType.rac`.

**Proposal.** Partial application elaborates to a lambda. It may not capture a
linear argument (F5); a partial application that would capture one is
`LinearCapture`. Lambdas in types need the elaborator and positivity to accept
them. S1 allows one with a linear parameter in a type, and F5 still forbids it
to capture a linear local.

### 2.9 Implicit arguments on definitions and inferred erased binders (*partly port*)

**Held 2026-10-30** for a later design discussion.

**Problem.**
- Definition headers have no erased binders: `{xs: …}` does not parse.
- Constructors' erased binders must be passed explicitly, as in
  `And.intro(a, b, x, y)`.

**Proposal.** `main-new`'s `docs/proposals/NAMED_IMPLICITS.md` is a historical
starting point. A linear implicit binder cannot be solved: its solution would
come from a type, where a linear value is only read (S1), so binding it would
copy the value. Implicit binders are therefore unrestricted (as L2 already
makes erased constructor binders).

## 3 Language design questions

### 3.1 Kind polymorphism (open question 10)

**Decided 2026-10-30:** adopted as designed in [KINDS.md](KINDS.md), with universe cumulativity removed. **Implemented** (`docs/kernel.md`, "Kinds and universes"); `LList` and `Tensor` are gone.

**Problem.** `List` and `LList`, and `Prod` and `Tensor`, are separate
families with separate libraries. `LList(Nat)` and `Tensor(Nat, Nat)` are
linear even though their contents are copyable.

**Observation.** Functions are already kind-polymorphic in effect. A
`Lin($u)` capture accepts copyable arguments, and the body tracks such
values, as Rust generic code treats a type parameter that is not bounded by
`Copy`. What is missing is families whose universe follows their arguments'
kinds.

**Proposal sketch.** A kind variable ranging over `Sort` and `Lin`. A family
`List (A: Kind($k, $u)) : Kind(k, u)` is unrestricted at `List(Nat)` and linear
at `List(Tok(…))`. A family with several parameters takes the join of their
kinds. Tracking is already decided from the instantiated type at each binder,
so the ledger needs little change. The work is in universe checking,
cumulativity and the nominal size rule over kind variables.

**Why early.** Every library family written before this lands is written
twice.

### 3.2 Linear closures (open question 11)

**Deferred 2026-10-30** until a client needs callbacks that own tokens.

A second function type, written `A ⊸ B` here, whose values own what they
capture and are used at most once. Callbacks that should own tokens would no
longer take them as arguments. This extends F5 rather than changing it: the
copyable function type keeps its rules. Partial application of a linear
argument (2.8) would produce one.

### 3.3 Supply splitting (open question 6)

**Deferred 2026-10-30** until needed.

`split : Supply ⊸ Prod(Supply, Supply)`, drawing names from disjoint parts of
the name space. One way is to read names as paths in a binary tree, which the
formalization already lists. Independent code could then allocate without
threading one supply through every call.

### 3.4 Universe-polymorphic protocols (open question 12)

**Deferred 2026-10-30** until a protocol needs large atoms.

`Atom : Sort($u)` instead of `Atom : Type`, so protocols over large atoms (for
example atoms that carry types) can be written. There is a known tension in
the model: the ledger's type would range over protocols at every level. The
formalization's design records the options.

### 3.5 Relaxing S1 for reads

**Decided and implemented.** S1 follows the formalization's `DESIGN.md` §6.
Observation is not what fails; duplication is. Types and proofs are read
extents, which may read live linear locals, observe them, and run closed
resource computations, consuming nothing. Inside them, each call takes linear
inputs of pairwise disjoint provenance, so `observe(join(t, t))` is refused,
and combines only tracked locals that were live together. No tracking of which
primitives a term reaches is needed. See `docs/kernel.md` S1 and
[linear protocols](../implemented/LINEAR_PROTOCOLS.md) §3.9. This supersedes
the item's first proposal, which would have banned observation in types and
tracked the primitives a type-level term reaches.

### 3.6 Exactly-once versus affine use (open question 7)

**Decided and implemented 2026-10-30:** affine. Dropping is sound and the ban bought nothing. `Protocol.discard` is removed, and scoped exactness is no longer planned ([KINDS.md](KINDS.md) §6; [linear protocols](../implemented/LINEAR_PROTOCOLS.md) §3.8).

The original text, for the record: soundness needs only no-duplication.
Exactly-once use was kept so that a scoped exactness primitive could be added
later. Its cost showed in the library: Track A's `Shares` has no rule without
outputs, so a program holding `Shares` tokens could never finish, and the
token entry used `Exclusive` instead. The options were:
- keep exactly-once, with a library convention that every protocol has
  terminal drop rules (elaboration's `terminal`);
- move to affine use and drop the scoped-exactness plan.

### 3.7 A warning for dropped linear values

**Deferred 2026-10-30.** Affine use makes dropping a token legal and silent,
although forgetting to release one can be a logic bug. An opt-in lint for
linear values dropped on some path, as a warning rather than an error, would
catch it.

## 4 Not kernel

- **Prelude gaps:**
  - `False.elim` into a proposition (Track A);
  - `max` and the order lemmas for `≤` and `<` (`lib/Protocol/Nats` has some);
  - list `Mem`, `Perm` lemmas and `flatMap` (`lib/Protocol/Lists`).
- **Parser:**
  - `A -> B` as a binder type;
  - `f(x)(y, z)`;
  - a binder type that is an application followed by `->`, or headed by a
    projection, needs parentheses;
  - dotted `def` names;
  - a comment right after `{`;
  - `use` as a keyword;
  - `decreases` must be on the result type's line.
- **Diagnostics:**
  - stuck selectors print as `match#LocalId(…)`;
  - mismatches print as "expected VPi, actual VPi";
  - `Protocol.Tok.mk` as a term reports `NotAType` rather than "no such
    constructor".
- **Checking speed:** `GpuClientFootprint` takes about 13 s to check. The
  cause was measured on 2026-10-30, and `step` firing is not it: checking
  evaluates proof-valued calls that nothing reads, about 19M of them. See
  [EVALUATION_AND_PORTS.md](EVALUATION_AND_PORTS.md), which also proposes the
  fix, with a prototype that brings the check to 1.1 s.

## 5 Suggested order

1. **The bugs (1.1–1.4)** are independent of each other and of everything
   else.
2. **2.1 and 2.2 together, then 2.3.** The protocol migration is cheapest
   before more library and client code depends on the component form.
3. **2.4,** before the packet library grows.
4. **3.1 decided before the library grows further,** since every family
   written before it lands is written twice.
5. **2.5–2.9** in any order; 2.6 and 2.7 are small ports.
6. **3.2–3.6** as design work, each checked against the formalization's
   design.
