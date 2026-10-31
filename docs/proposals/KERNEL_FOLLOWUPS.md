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
| 1.4 | Smaller defects: an unlocated internal error, `AlreadyDefined` without a span, open shadowing (fixed) | bug | new | — |
| 1.5 | Branch fields typed at fresh parameters when an index equation is stuck (fixed) | bug | port | — |
| 1.6 | Positive arguments of a family read its own occurrences as positive (fixed) | bug | new | — |
| 1.7 | A family in its own constructors' result indices (decided: refused, implemented) | bug | new | — |
| 2.1 | Structure eta (implemented) | expressiveness | port | — |
| 2.2 | Positivity of stuck computations (implemented) | expressiveness | port | 18 |
| 2.3 | Bundled protocol families (implemented) | expressiveness | follows | — |
| 2.4 | Structural recursion on indexed families with variable indices (implemented) | expressiveness | new | 16 |
| 2.5 | Mutual inductives and mutual recursion (implemented) | expressiveness | port | — |
| 2.6 | Wildcard case (implemented) | expressiveness | port | — |
| 2.7 | Match equations (implemented) | expressiveness | port | — |
| 2.8 | Partial application and lambdas in types (decided: lambdas in types, implemented) | expressiveness | new | 3 |
| 2.9 | Implicit arguments on definitions and inferred erased binders | expressiveness | partly port | — |
| 2.10 | Over-rejections found by the matching review (`Nat` metrics by `<` and rank components: decided and implemented; par-5 kept; positivity and guards for decision) | expressiveness | new | — |
| 2.11 | Field projection as a kernel operation (decided and implemented) | expressiveness | new | — |
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

**Decided 2026-10-30:** for the open-name precedence, a selective open (`open X.{a}`) beats a name in the enclosing namespace, and a wildcard open keeps today's rule. The other defects are plain fixes. **Implemented:** names resolve to locals, then selective open aliases, then the enclosing namespaces, then wildcard aliases (`docs/namespaces.md`; `NamespaceTests`). `AlreadyDefined` is located at the redeclared name or binder. The capture mismatch is still reachable, as a `TypeMismatch` in a constructor's result or a pattern argument, located at the argument that does not fit. A capture through a user alias for `Lin`, such as `$u` in `L($u)` with `L(u) := Lin(u)`, now opens as one through an alias for `Sort` does: a universe of constant kind reads as `Sort(l)` or `Lin(l)`, with its level at position 0, and the binding's re-check (`docs/kernel.md`, "Type patterns") requires `L(l)` to convert with the universe read, so a value opened through `L` stays linear (`LinearEscapeTests`, "universe aliases"; `KindTests`).

- **Unlocated internal error.** A constructor capture that does not match its
  parameter's universe throws "Cannot return idx 0 of Lin(…)" with no location.
  It should be a located type error. (Fixed for `Sort` and `Lin` captures, which
  now open on any universe and give a located `TypeMismatch`, and for a capture
  through a user alias for `Lin`, which now opens. An alias whose parameters are
  not the target's arguments in order is still refused: a two-parameter
  `U(k, u) := Univ(k, u)`, since a universe reads only as `Sort(l)` or `Lin(l)`,
  is a located `FailedToOpenCapture` that names the capture, and a permuted
  `Flip(B, A) := Prod(A, B)` a `TypeMismatch` from the re-check. Accepting them
  would need the alias unfolded in the pattern; **deferred 2026-10-30** until a
  program needs it.)
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

### 1.7 A family in its own constructors' result indices (fam-10)

**Decided 2026-10-30: refused, as in Coq and Lean.** Found by the matching review (`MatchingAttackTests`, fam-10).
With propositional extensionality, which Lean assumes, `Bad` proves `False`: a match on `Bad(True)` yields the index
equation, so `Not(Bad(True))` holds with no axiom, and `propext` makes `Not(Bad(True))` equal to `True`, along which
`Bad.mk` proves `Bad(True)`. **Implemented:** `checkFamily` refuses an occurrence of the block's families in a
constructor's result index with `FamilyInResultIndex`, at the constructor's result; a field the index reads is a
variable, so no occurrence (`docs/kernel.md`, strict positivity; `MatchingAttackTests` fam-10, fam-10b, fam-10c).

**Problem.** A family, or a sibling in its mutual block, may occur in its own constructors' result indices, even
negatively:

```text
inductive A indices (T: Type) : Type
 | mk : A(A(Nat))

inductive Bad indices (P: Prop) : Prop
 | mk : Bad((h: Bad(True)) -> False)
```

Strict positivity reads only the fields' types (`InductiveChecks.checkFamily`, step 3), and a constructor's result
arguments are checked only for its head, its arity and the uniformity of its parameters. Coq and Lean refuse both
declarations: a family being declared may not occur in its constructors' result indices.

**Analysis.** An index is no field, so a match never hands a branch the value an index names, and the review found no
contradiction in the kernel alone. But a match does yield the index equation, and an equation that names the family
being defined need not have a solution: in any model with propositional extensionality, including Lean's, `Bad(True)`
would be equivalent to its own negation. The behaviour predated the matching cluster for a single family; a mutual
block extended it to siblings. No known program needs the form.

## 2 Expressiveness gaps that force encodings

### 2.1 Structure eta (*port*)

**Decided 2026-10-30:** follow `main-new`. Every family that has one constructor, no indices and no recursive field, and is not in `Prop`, gets structure eta and generated field selectors, at every kind, linear ones included; since 2.11, projections instead of selectors. The model validates eta for carriers, and relaxed S1 lets conversion compare linear values. The `struct` keyword is removed: a struct is an `inductive` that meets those conditions. `Observed` and `Fresh` then get selectors without further change. **Implemented** (`docs/kernel.md`, "Structure eta and projections"). Every one-constructor family gets selectors, indexed ones too, as `struct` gave them; eta needs the conditions above, and a family whose field depends on a capture its arguments do not determine has neither.

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

**Decided 2026-10-30:** no partial application. Raccoon functions are n-ary telescopes, and partial application would hide arity errors, while at a linear argument it would be a linear closure. Every use in Track A was a predicate inside a statement, so lambdas in types cover it. Lambdas in types stay in scope. **Implemented** (`docs/kernel.md`, "Lambdas in types"; `LambdaInTypeTests`): a lambda parses and checks in binder types, codomains, annotations, field types and motives, under F4, F5 and S1; positivity and the size rules read it as a function value. A linear record's selector whose field type's lambda names an earlier field is `LinearCapture`, by F5.

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

### 2.10 Over-rejections found by the matching review

**Decided 2026-10-30,** except the last item, which is for decision. The matching review (`MatchingAttackTests`)
found three sound programs the kernel refuses, and ordering `Nat` metrics by `<` two more. Each is for the user to
judge against the principle that a sound program is rejected only when accepting it would cost significant
implementation or performance.

- **par-5: tracking is decided at the binder.** In
  `def dup (A: Univ($k, $u))(o: CopyOpt(A))(b: Univ(k, $v))(y: b)(z: b)`, `y` is tracked, since its kind is the
  variable `k`. In the case `CopyOpt.some x`, refinement solves `k := Kind.copy`, so `y` is copyable there, but
  `Prod.mk(b, b, y, y)` is `LinearReused`: the ledger decides tracking once, from the type at the binder, and
  refinement never changes it (`docs/kernel.md`, "The ledger"). The workaround is the rule's own, `let y2 := y` in the
  branch, which uses `y` once and binds an untracked `y2`. Accepting it would make a branch drop from its use summary
  every tracked local whose refined type is copyable, before the binder rule reads the summary, and give such a local
  no provenance there: a filter in `MatchChecker.checkBranch`, small, but a change to an invariant the ledger and S1 now
  rely on, that a local's tracking never changes.
  **Decided 2026-10-30:** kept. It keeps the invariant that a local's tracking never changes, which the ledger and
  relaxed S1's provenance rely on, and the workaround is one `let`.
- **mut-14: a proof-decreasing member cannot call a data-decreasing one.** Members compare metrics component by
  component, each by the order of the caller's current value, so a data candidate against a proof root is neither
  smaller nor equal. A disjoint sum of the two orders, one ranked below the other, would accept calls in one direction
  only, so the review's cycle, `f` decreasing a proof calling `g` decreasing data, which passes the proof back, would
  still be refused, and so it would be with both members decreasing the proof, since `g`'s call passes it back
  unchanged; accepting it needs a different principle, such as size-change termination, which sees that the proof
  shrinks over the two calls. The workaround is to inline the member that passes the proof back, so that every call
  decreases. Significant cost; keeping the restriction is recommended.
  **Decided 2026-10-30:** rank components: a `lexicographic` component may be a measure, `measure(e)`, as well as a
  parameter, and a constant measure is a rank. **Implemented** (`docs/kernel.md`, "Mutual blocks"; `RankAttackTests`):
  a measure component follows a `measure` clause's rules, in `Type`/`Sort(u)`, evaluated again at each call and only
  reading its arguments (L6), a parameter component keeps its own, and every component keeps `compare`'s order, so the
  metric's order stays the lexicographic product of well-founded ones. The review's blocks, as written, are still
  refused (mut-14 in `MatchingAttackTests`); ranks are the way to write them. In the proof block, `f` decreases
  `lexicographic(h, measure(0))` and `g` `lexicographic(h, measure(1))`, so `g`'s call keeps `h` and lowers the rank;
  in the measure block, `f` decreases `lexicographic(measure(Nat.add(a, b)), measure(0))` and `g`
  `lexicographic(measure(Nat.add(x, y)), measure(1))`. The adversarial review found no break.
- **mut-14: measures are ordered structurally, not by `<`.** In a block with
  `f (a: Nat)(b: Nat) decreases measure(Nat.add(a, b))` calling `g(k, b)` from `a = Nat.succ(k)`, the candidate `b`
  is below `k + b + 1` numerically but is no structural subterm of it, since summands are not structural subterms
  (`docs/kernel.md`, "Natural number normal forms"). Ordering a `Nat` component by `<`, decided by the normal forms'
  signed difference as `Nat.ble` is, would accept it. That order contains the structural one on `Nat`, and no value
  of another type is a structural subterm of a `Nat`, so every component, structural or measure, could compare `Nat`
  values by it and stay well-founded; the comparison is stable under substitution. A
  moderate change to `TerminationChecker` with a real gain in expressiveness, comparable to well-founded recursion on
  `<`; it also applies to single definitions.
  **Decided 2026-10-30:** order `Nat` components by `<`. **Implemented** (`docs/kernel.md`, "Mutual blocks";
  `NatOrderAttackTests`): a `Nat` component, a measure or a parameter, in a block or a single definition, is smaller
  when the caller's value, refined in the branch, minus the candidate is at least 1 on the normal forms
  (`NatNormalForm.differenceBound`), and at most the caller's value when it is at least 0. Other components keep their
  orders, and the structural test runs first, so nothing that checked before does arithmetic. The review's block itself
  stays refused, now at `g`'s call back to `f`: the candidate `y + x` is above `g`'s root `y` unless `x` is zero, and no
  one-component metric of `g` lies strictly between `f`'s measure `k + 1 + b` and its next one, `b + k`. Like the proof
  case, it terminates only because `f`'s measure decreases over two calls (mut-14 in `MatchingAttackTests`), and ranks
  write it (above). The adversarial review found no break.
- **lt-16: a term is not known positive, and a guard is not read.** `<` decides only what the normal forms' signed
  difference shows (`NatOrderAttackTests`, lt-16). With `f (n: Nat) decreases measure(Nat.pow(2, n))`, the call
  `f(k)` from `n = Nat.succ(k)` is refused: the difference `2^(k+1) - 2^k` is the term `2^k`, with no constant, though
  a power of a positive base is at least 1, and `Nat.ble(1, 2^k)` is stuck for the same reason. With
  `up (i: Nat)(n: Nat) decreases measure(Nat.sub(n, i))`, the call `up(Nat.succ(i), n)` in the `false` case of
  `match Nat.ble(n, i)` is refused: `sub(n, i)` and `sub(n, i + 1)` are unrelated atoms, and the comparison does not
  read the case's guard, `i < n`. Accepting the first needs a lower bound for terms known positive, such as a power of
  a positive constant, in `NatNormalForm.differenceBound`: small, though `<` would then decide more than `Nat.ble`
  unless `ble` takes the same bound. Accepting the second means letting termination use the branch's facts: the case
  would record what its scrutinee's value gives, `Nat.ble(n, i) = false`, and the comparison would derive
  `sub(n, i + 1) < sub(n, i)` from it, a larger change to refinement and `compare`. The workarounds are a measure
  whose difference has a constant, such as `n` for `2^n`, and recursion on the count left, `n - i`, rather than on a
  guard. For decision.

Two more follow the spec and need no change. **root-5:** since 2.4 links the root at a variable index, a nested match
on the same root sees its constructor and its other cases are `UnreachableCase`, as they always were for a family
without indices. **wild-6:** each case a wildcard stands for knows the scrutinee's constructor, so its body cannot
match the scrutinee again on the other constructors, exactly as the cases written out could not.

### 2.11 Field projection as a kernel operation

**Decided 2026-10-30:** replace the elaborator's generated selectors by a projection the kernel checks and evaluates.
**Implemented** (`docs/kernel.md`, "Structure eta and projections"; `ProjectionAttackTests`). `r.field` is, for every
record, the canonical projection that eta views already were, whose type is read off the constructor's telescope at the
record's type; its checked term is a node of its own, `ElabAst.Term.Proj`, and no global is generated. A record's
fields are declared in its namespace, so `Prod.fst(p)` stays an explicit spelling of `p.fst`, an `open` aliases a
field, and no global shares a field's name; `Prod.fst` unapplied is `UnappliedField`. A selection names a field and
nothing else: the selectors' fallback that applied any global `Fam.name` to a record, as a method, worked only for
records, and nothing in the suite, the library or the GPU experiment relied on it, so it was dropped (decided
2026-10-30), with `NotAStruct`; a selection that names no field is `NotFound`.

**Problem.** Each selector was a lazily checked definition `Fam.field (self: Fam(…)) : T := match self returning T
with | mk … => field`, whose `T` restated the field's type as surface syntax with the earlier fields rewritten to
selector calls. The generator gave up on a type capture that shadows an earlier field and on a hidden dependency, which
cost the whole family its selectors, and a selector of a linear record whose field type held a lambda over an earlier
field was `LinearCapture`. An application of a selector was a call, so in a read extent its result covered the whole
record: `observe(join(p.fst, p.snd))` in a proof was refused, though destructuring `p` was accepted.

**What changed.** In a read extent a projection is field `i` of its record's region, as a match field is, so that
program is accepted, while one field twice still overlaps. A field whose type no argument determines has no projection
(`InvalidStruct`), but the record's other fields project. An indexed record projects as before, now by unifying the
constructor's result with the record's type one argument at a time, which types `s.v` as a `Vec(Nat, n)` at
`Sized(n)` where a selector typed it by `s.k`. A projection out of a proof also checks the earlier fields its type
reads, as a selector's declared type did: `e.proof` of an `Exists` is refused, since it would hold `e.witness` in a
type.

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

- **Prelude gaps** (**filled 2026-10-30**, `PreludeTests`):
  - `False.elim` into a proposition (Track A) (now `False.elimProp`);
  - `max` and the order lemmas for `≤` and `<` (`lib/Protocol/Nats` has some)
    (now `Nat.max`, `Nat.le_max_left` and `Nat.le_max_right`, and `Nats`'s
    laws under their names; `Nats` stays, empty, for its importers);
  - list `Mem`, `Perm` lemmas and `flatMap` (`lib/Protocol/Lists`) (moved
    under their names, with `flatMap`'s laws stated with lambdas; `Subset`,
    `Every`, `Pairwise`, `Nodup` and the maps `single` and `compose` stay in
    the library, which still checks).
- **Parser** (**fixed 2026-10-30**, `ParserTests`; README, "Syntax and layout";
  EVALUATION_AND_PORTS #10, from `main-new`'s `ef5a2d31`, `c352d5bd` and
  `d50f04ee`):
  - `A -> B` as a binder type, and as a term, such as an argument;
  - `f(x)(y, z)`;
  - a binder type that is an application followed by `->`, or headed by a
    projection, needs parentheses;
  - dotted `def` names (now a namespace block around the declaration, for
    `def`, `axiom` and `inductive`);
  - a comment right after `{`, and blank and comment lines between a block's
    statements, a match's cases and an inductive's constructors;
  - `use` as a keyword (now an identifier except at a statement's start);
  - `decreases` must be on the result type's line;
  - parse errors print parser objects (now they name what was expected).

  A definition without parameters whose type is a function type, such as
  `def f : Nat -> Nat := Nat.succ`, was elaborated as a function of that type's
  binders, and is a constant of its type now. A recursive one, a mutual member
  or a single definition with `decreases`, crashed (mut-13, "Local ref f#0 is
  already bound"): its peer or self slot took the type's first binder's. It is
  now the function of its type's parameters, unnamed, whose body is the written
  one applied to them, with its recursive slots after them (`docs/kernel.md`,
  "Mutual blocks").
- **Diagnostics** (**fixed 2026-10-30**, `ValuePrintingTests`; EVALUATION_AND_PORTS #9,
  after `main-new`'s `d50f04ee` and `6a0c6192`):
  - stuck selectors print as `match#LocalId(…)` (now a record's projection
    prints as `P.Atom`, and any other stuck match as its syntax under its
    environment);
  - mismatches print as "expected VPi, actual VPi" (now a function type prints
    as `(x: A) -> B`, its binder types as written and its codomain opened on
    its binders, a local lambda as its binders and opened body, and a level as
    `Level.succ(…)` source syntax);
  - `Protocol.Tok.mk` as a term reports `NotAType` rather than "no such
    constructor" (now `NotFound`: "Protocol.Tok has no constructor mk").

  Error messages are computed when read, so a caught error prints nothing.
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
