# Raccoon kernel reference

This document records the semantic rules implemented by the current trusted
checker and evaluator. It states the behavior that code may rely on. Historical
design alternatives and proposed extensions do not belong here.

## Trust boundary

The elaborator resolves source names and lowers surface syntax to `CoreAst`.
From `CoreAst` onward, declaration checking, evaluation, conversion,
unification, inductive validation, match refinement, termination checking, and
residual construction form one trusted implementation. There is no smaller
independent kernel that rechecks a certificate produced by those components.

A declaration is checked once. The checked value is then published in the
environment and trusted by later declarations. Transparent definitions publish
their evaluated values. Data-valued opaque definitions and axioms publish
symbolic heads; proof-valued declarations are canonicalized from their exact
propositions before publication.

The bundled source prelude is a trusted bootstrap. A prelude is still parsed,
elaborated, and typechecked, but prelude loading alone may install builtin
declarations and native equations. Selecting `--prelude` therefore selects a
different trusted bootstrap.

## Equality and evidence

Three judgments must remain distinct.

| Judgment | Meaning | Main consumers |
|---|---|---|
| Definitional equality, `a ≡ b` | The terms are interchangeable during typechecking. | Conversion and type fitting |
| Constructor consequence | An equation is forced inside a branch because the scrutinee is that constructor. | Index refinement and branch checking |
| Propositional equality, `Eq(A, a, b)` | The object theory contains a proof of equality. | User proofs and any claim of uninhabitedness |

Definitional inequality is not propositional disequality. A failed or stuck
unification attempt is not evidence that a constructor is impossible.

### Definitional equality

`ValueEquivalence.defEq` is the ordinary unifier run with an empty set of
refinable variables. Its successful rules are:

- evaluation, including beta reduction, constructor-match reduction, and
  registered builtin reduction;
- structural congruence for values and applications;
- extensional comparison of lambdas on shared fresh arguments;
- normalized universe-level equality;
- proof irrelevance at definitionally equal propositions;
- structure eta for eligible non-Prop inductive instances;
- equality and constructor peeling for validated packed values;
- conservative congruence of blocked matches with the same checked behavior.

Function binder grouping is exact. Two Pi values compare binder-for-binder and
must have the same binder count and implicitness within the current group.
`(a: A)(b: B) -> C` is not convertible with
`(a: A) -> ((b: B) -> C)`.

Conversion does not include universe cumulativity. Type fitting succeeds by
definitional equality, with eta adaptation for the supported implicit-function
case, not by a general subtyping relation.

### Refinement unification

The match checker runs the same unifier with a controlled set of refinable
variables. A link may be recorded only when the presented equation forces that
solution. In particular:

- genuine inductive family and data-constructor frames are invertible;
- arbitrary applications, Pi components, blocked computations, and closure
  captures are not invertible frames;
- an occurs failure or an equation that has several possible solutions remains
  stuck;
- level variables link only when normalization leaves a forced solution;
- refinable values at eta-eligible structure types are expanded at the
  refinability boundary, where eta makes the expansion unique.

The store records consequences, never guesses. Evaluation does not consume a
refinement store.

### Apartness

Apartness is the stronger result used to omit an unreachable match branch. It
is produced only by evidence that supports propositional no-confusion:

- a clash between distinct constructors of a non-Prop inductive, when both
  constructor heads carry checked no-confusion evidence;
- unequal payloads of a packed codec that explicitly certifies that finite
  decoding reaches such a constructor clash. The Nat codec has this property.

Proof constructors, quotient constructors, family heads, opaque applications,
level failures, and ordinary unification failures do not produce apartness.

## Universes and function types

The primitive universe equations are:

```text
Prop = Sort(Level.zero)
Type = Sort(Level.one)
Prop : Type
```

Levels normalize to maxima of offset atoms plus an optional constant.
`Level.succ`, `Level.max`, and `Level.imax` construct normalized levels.
`imax(a, b)` reduces when `b` is known to be zero or positive and otherwise
remains a conditional atom. Normalized representation equality is level
equality.

A telescope

```text
(x1 : A1) ... (xn : An) -> B
```

has universe

```text
imax(u1, ... imax(un, v) ...)
```

where each `Ai : Sort(ui)` and `B : Sort(v)`. Consequently, a Pi whose
codomain is a proposition lives in `Prop`, regardless of its domain universes.
A codomain equal to the sort `Prop` is different: `Prop` itself lives in
`Type`.

Universes are non-cumulative. Constructor-field universe checks enforce the
declared inductive's size bound, but they do not introduce general sort
subsumption.

An implicit binder is accepted only with a compiled projection that recovers
it from later explicit arguments. Checked applications retain only explicit
arguments. Checking and evaluation reconstruct every implicit with the same
projection and then check it against its instantiated binder type. Constructor
family parameters that cannot be projected are demoted to explicit arguments;
other unforced implicits are rejected.

## Inductives and matching

An inductive declaration is installed only after checking:

- that the family result is a sort;
- universe bounds for every constructor field;
- that every constructor result is the declared family with uniform
  parameters and well-typed indices;
- strict positivity of recursive occurrences;
- nested positivity only through parameters that the referenced inductive
  block certifies as positive.

The Core AST supports atomic mutual-inductive blocks. Every family in a block
has the same parameter telescope and universe. All provisional family heads
are visible while constructors are checked, but the block publishes only after
every family succeeds. Positivity and recursion metadata are computed for the
whole block. The surface parser currently emits singleton blocks only.

Constructor values erase family parameters and retain ordinary constructor
fields. Each family records only its own constructors for match
exhaustiveness.

A checked match establishes all of the following:

- the scrutinee has an inductive family type;
- every case names a constructor of that family;
- case field counts and field types agree with the constructor;
- no constructor is duplicated;
- every reachable constructor is present;
- constructor-result equations provide only justified branch refinements;
- every branch has the instantiated motive.

An omitted constructor is valid only when its result is apart from the exact
scrutinee type. A stuck equation keeps the constructor reachable and provides
no refinement.

Evaluation reduces a match only when the scrutinee exposes a justified
constructor view. Otherwise it retains a blocked match with the dependencies
that could make reevaluation productive.

## Proofs and elimination

Proof irrelevance is definitional:

```text
p : P, q : Q, P and Q propositions
-----------------------------------
p ≡ q  iff  P ≡ Q
```

Operational behavior must be congruent with that equality. A proof's canonical
outer representation is chosen only from its exact proposition:

1. A declaration-certified, one-constructor recovery plan may reconstruct a
   constructor after every field is recovered and the constructor result is
   definitionally equal to the exact proposition.
2. A Pi proposition becomes a synthetic proof eta-lambda. Applying it produces
   the canonical proof of the instantiated codomain; the checked source proof
   body does not run.
3. Every other proof is the structureless `VProof(proposition)`.

This is finite, type-directed reconstruction, not proof search. It performs no
runtime unification. A data field is recoverable only when the exact family
instance directly determines it. A proof field is recoverable from its
instantiated proposition. Hidden existential data, constructor choice, and
values occurring only underneath another function are not recovered.

For example, any inhabitant of
`Eq(Nat, Nat.zero, Nat.zero)` canonicalizes to
`Eq.refl(Nat.zero)`. An inhabitant of `Eq(Type, Nat, Bool)` cannot reconstruct
`refl` and remains `VProof`.

A match from a proposition to a proposition is ordinary small elimination. A
match from a proposition to data is accepted only when:

- no constructor is reachable at the exact proposition; or
- every field of every reachable constructor is recoverable from that
  proposition.

Eligibility alone does not force reduction. Evaluation selects a branch only
after exact constructor-result validation reconstructs a constructor. A
non-reconstructible proof leaves a data-valued match blocked. This separation
prevents constrained indexed propositions from manufacturing data.

Proof constructor identity and fields provide no injectivity, apartness, or
termination evidence. Recursive proof fields are exposed one layer at a time,
so canonicalization never builds an infinite proof value eagerly.

## Structure eta and projections

Every one-constructor family records positional field metadata. A non-Prop
instance is structure-eta eligible exactly when the checked family has:

- one constructor;
- no indices;
- no recursive constructor field in its inductive block.

Eligibility depends on the checked family, not on whether the source used
`struct`. Prop instances use canonical proof representation and never structure
eta.

Eta is a rule, not a representation invariant. At an eligible type, a value is
definitionally equal to its constructor applied to its fields. A
constructor-headed value exposes stored fields; a neutral value exposes virtual
field projections. Conversion, match evaluation, and structural-subterm
checking all use the same eta view.

There is no primitive projection value. A positional projection is the
ordinary one-branch match that returns the chosen field. Surface `struct`
selectors are generated definitions containing those matches. Therefore a
projection from `Prop` is governed by the proof-elimination rules above.

## Termination

Recursive functions are checked with a well-founded strict-subterm order over
strictly positive inductive data.

- A structural metric must become a strict constructor-field descendant.
- A lexicographic metric compares an equal prefix followed by one strict
  descendant.
- For a measure specification, the same expression is evaluated in the current
  call environment and with the proposed recursive arguments. The proposed
  value must be smaller in the same structural order; a measure does not
  introduce a user-defined relation.
- Applying a function-valued constructor field may produce one of that node's
  structural children.
- Fields reached virtually through valid structure eta are structural children
  of the structure value.
- Packed Nat values use numeric `<`, which is the compact form of repeated
  predecessor descent.

Every metric must have a genuine non-Prop inductive type. Proofs, quotients,
and values of user-axiomatized types are rejected as metrics.

While checking a recursive body, a raw recursive reference is valid only as
the head of a direct call whose metric decreases. It cannot escape into a
closure, constructor field, argument, return value, or opaque application.
Runtime recursion uses the already checked lambda and performs no further
decrease test.

Core mutually recursive definition blocks are published atomically. Their
members have compatible lexicographic metric shapes, and every cross-component
call must decrease from the caller's current metric. Measure specifications are
not supported for recursive definition blocks. The surface parser currently
emits only singleton recursive definitions.

## Axioms, opacity, and quotients

Axioms and opaque definitions break closed canonicity. A closed value of an
inductive type may remain a symbolic or blocked application instead of reducing
to a constructor. Kernel code must therefore never assume that every closed
inductive value is constructor-headed.

User `axiom` declarations may introduce arbitrary symbolic inhabitants. They
are typechecked, but their consistency is the user's responsibility. Proof
axioms still canonicalize according to their exact proposition; data axioms
remain symbolic.

The bundled quotient interface is the fixed non-inductive primitive surface:

- `Quot` is an axiomatically declared type former;
- `Quot.mk`, `Quot.lift`, and `Quot.ind` are prelude-only builtins;
- `Quot.sound` is an axiom identifying related representatives.

`Quot.mk` is not a no-confusion constructor. Quotient equality is intentionally
coarser than representative structure, so quotient values supply neither
constructor injectivity nor apartness. `Quot.lift` reduces on `Quot.mk` only
through its registered builtin equation; `Quot.ind` provides the Prop-valued
eliminator.

## Trusted bootstrap and native values

Only a trusted prelude may publish builtin declarations or native literal
layouts. Ordinary modules cannot gain native semantics by declaring a reserved
name.

### Natural numbers

At the end of prelude loading, a declaration named `Nat` is accepted for
literal syntax only if it is exactly a Type-valued unary inductive with the
no-confusion constructors:

```text
Nat.zero : Nat
Nat.succ : Nat -> Nat
```

Ground natural numbers then use an arbitrary-precision packed payload.
Constructor formation folds ground `zero` and `succ` values into that form;
matching and mixed conversion decode one constructor layer on demand. The
representation is definitionally transparent to ordinary unary Nat programs.

The kernel has one closed table of binary Nat equations:

```text
add sub mul pow div mod gcd land lor xor shiftLeft shiftRight
beq ble blt
```

An equation attaches only to the exact transparent lambda published under its
canonical `Nat.*` name while a trusted prelude loads, after its two explicit
Nat arguments and Nat/Bool result are validated. The declaration body is
typechecked but not semantically recognized; agreement between that body and
the host equation is part of the bootstrap trust assumption. Application never
consults a global name registry, so later same-named source cannot acquire the
equation.

Subtraction truncates at zero. Division by zero returns zero, modulus by zero
returns the dividend, and `pow(a, 0)` returns one. `pow` and nonzero
`shiftLeft` reject exponents or counts above `2^24`; sufficiently large
`shiftRight` returns zero without allocating an enormous intermediate value.

The bundled prelude defines and accelerates `add`, `sub`, `mul`, `pow`, `beq`,
`ble`, and `blt`. Other table entries become available only if the selected
trusted prelude declares their exact validated definitions.

### Strings

String literals require an optional validated bootstrap layout:

- a Type-valued `Char`;
- `List(Char)` with exact `nil` and `cons` constructors;
- an eta-eligible one-field `String` with constructor `String.mk` storing
  `List(Char)`;
- a closed checked `Char.ofNat : Nat -> Char`.

The kernel trusts the exact `Char.ofNat` identity to map Unicode scalar values
injectively. A string evaluates to `String.mk` containing a packed scalar list.
The outer `String` remains constructor-headed, preserving structure eta. List
matching decodes one `nil` or `cons` layer at a time. The bundled prelude does
not currently install this layout.

## Value identity

Fast equality keys may prove definitional equality, so every value component
used to build a key must be semantically identifying. Source and synthesized
Pi, lambda, and blocked-match nodes carry distinct AST node identities;
captured values are part of closure identity. Packed keys include the codec,
canonical payload, and packed type. Source spans are diagnostic metadata and
are not identities.

Blocked applications and matches carry dependency sets describing which
refinement-store events could make reevaluation productive. An empty dependency
set means the computation is rigid. Materialization may rerun a blocked
computation after one of its dependencies is solved, but it does not use that
mechanism to invent proof or structure representations.

## Maintained invariants

Changes to the checker or evaluator must preserve these rules:

1. Conversion success is justified by a definitional equality rule.
2. Refinement links are forced consequences; the unifier never chooses among
   several solutions.
3. Match pruning uses apartness, never ordinary unification failure.
4. A proof's behavior depends only on its exact proposition.
5. Runtime proof reconstruction is finite and never invokes unification.
6. Proof structure supplies no no-confusion or termination evidence.
7. Structure eta applies only to checked non-Prop, nonrecursive,
   zero-index singleton families.
8. Recursive calls are accepted only from genuine structural descent.
9. Axiom, opaque, and quotient values are allowed to remain closed neutrals.
10. Native equations and literal layouts are installed only by a selected
    trusted prelude and remain attached to validated values, not global names.
