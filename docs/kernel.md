# Raccoon kernel

## Trust boundary

The elaborator resolves source names and lowers surface syntax to `CoreAst`.
The checker, evaluator, conversion, inductive validation, match refinement,
termination checking, and residual construction form one trusted implementation.
There is no independent certificate checker.

Declarations are checked once and published in an environment. Transparent
definitions publish their evaluated values; opaque data definitions and axioms
publish symbolic heads. Axioms are explicit assumptions and may occur in any
module. Only the selected prelude may install primitive quotient bodies.
The prelude otherwise contains ordinary checked source declarations.

## Universes and function types

A sort carries only a universe level:

```text
Prop = Sort { level = Level.zero }
Type = Sort { level = Level.one }
Prop : Type
Sort { level = u } : Sort { level = Level.succ(u) }
```

`Level` is a second-class universe parameter. Its forms are `zero`, `one`,
`succ`, `max`, and `imax`, qualified by `Level` outside a sort field. Levels
normalize to maxima of offset variables, conditional `imax` atoms, and an
optional constant. A form must be supplied all its arguments. Universe
conversion is exact; there is no cumulativity.

The level of a dependent function type folds the domain levels with `imax`
over the codomain level. Consequently, a function into a proposition is itself
a proposition regardless of its domain universes. A codomain equal to `Prop`
is different: `Prop` itself lives in `Type`.

A declaration header or family parameter may bind a level. A telescope binding
a level has the internal classifier `Large`, because no sort contains it.
`Large` is not source syntax and cannot be quantified over. Other binder sites
require ordinary types. Expressions of `Level` occur only in universe fields
and arguments at level parameters; a large reference occurs only as an
application head, and a large type only as a declaration type.

Function binder grouping is exact. `(a: A)(b: B) -> C` has two arguments;
`(a: A) -> ((b: B) -> C)` has one and returns a function.

## Equality and evidence

Definitional equality, constructor consequences inside a match, and proofs of
`Eq` are separate judgments. A failed conversion is not evidence of
propositional disequality.

Conversion uses evaluation, structural congruence, extensional lambda
comparison, level normalization, proof irrelevance, structure eta, and
conservative congruence of blocked matches. Checking a term against a type is
synthesis followed by conversion: an expected type never changes synthesis.

Match refinement uses the same unifier with a controlled set of refinable
variables. Genuine family and data-constructor frames are invertible. Arbitrary
applications, function type components, and blocked computations are not.
Occurs failures and equations with several possible solutions stay stuck.
Level variables link only when normalization forces a solution.

Only a clash between distinct constructors carrying checked no-confusion
evidence proves apartness and permits omission of an unreachable branch.
Proof constructors, quotient constructors, family heads, and ordinary
conversion failures do not supply that evidence. Structure eta expands eligible
refinable variables at the refinement boundary, recording forced identities.

## Inductives and matching

Inductive declarations have uniform parameters, indices, and constructors.
Their result must be a sort. Every constructor returns the declared family at
the common parameters; source fields must be strictly positive in every family
of a mutual block. For data families, field universe levels must fit the
family's declared level. Each sibling uses its own declared sort.

Mutual blocks are checked atomically. Family signatures see the incoming
environment, and constructors see provisional heads for every sibling. No
partially checked block is published. Positivity information is compiled once
for each common parameter.

Matches synthesize their written `returning` motive. Checking refines the
scrutinee and indices separately for each constructor, rejects duplicate and
unreachable cases, and requires every case not proven impossible. A stuck index
equation cannot justify dropping a case.

## Proofs and elimination

Proofs of definitionally equal propositions are irrelevant. Their runtime
representation depends on the exact proposition, rather than on the proof's
origin or transparency. Proof functions use canonical eta lambdas. Other proofs
are erased unless declaration-certified reconstruction can recover a unique
constructor and its fields from the proposition and indices.

Elimination from `Prop` into data is allowed only when the declaration's
reconstruction information supports it. An erased proof cannot expose a hidden
data witness. Proposition-valued matches can erase their results directly.
Proof canonicalization is reapplied after refinement when a formerly unknown
universe becomes `Prop`.

## Structure eta and projections

A suitable nonrecursive single-constructor data family has structure eta.
Its constructor value compares fieldwise with its virtual projections; a neutral
unit structure is equal to its sole inhabitant. Two neutrals with nonempty
fields are not repeatedly decomposed into themselves.

Named selectors are ordinary checked functions whose bodies match on `self`.
An implicit binder must be recoverable from later explicit arguments through
a structural projection compiled at function type formation. Application
checking reconstructs implicit values, then verifies every argument against its
instantiated binder type. Evaluation uses the same projection specifications.

## Termination

Recursive calls require a declared structural, lexicographic, or measure-based
decrease. Structural descent follows ordinary constructor fields and eligible
structure projections. Applications of a strictly positive function field count
as descendants of that field. A proof cannot provide a data decrease metric.

During checking, recursive names denote stubs that enforce the decrease and
may only occur as application heads. Checked recursive groups publish lazy
bindings over one shared environment; bodies do not execute while that knot
is formed.

## Axioms, opacity, and quotients

An axiom declares a symbolic constant of a checked type. Opaque definitions
check their bodies but retain a symbolic data head. Proof representation remains
independent of opacity.

The prelude declares `Quot`, `Quot.sound`, and the primitive bodies of `Quot.mk`,
`Quot.lift`, and `Quot.ind`. A quotient constructor has no injectivity or
no-confusion rule: `Quot.sound` may equate distinct representatives. Lift and
induction reduce when their argument is a quotient constructor.

## Numerals

Natural-number literals are elaboration sugar: `2` becomes
`Nat.succ(Nat.succ(Nat.zero))`. They are checked and evaluated as ordinary
constructor applications. Arithmetic uses recursive source definitions in the
prelude. The kernel has no alternate numeric representation, native arithmetic,
string literals, or prelude layout validation.

## Value identity

Function types, lambdas, and matches carry stable node identities. Rebuilding a
checked residual preserves its source node's identity; new nodes receive fresh
identities. Evaluation combines an identity with the values of captured locals.
Only referenced locals enter a runtime closure.

Value keys accelerate conversion. Keys include universe levels for sorts,
constructor types for stored-field applications, and proposition types for
erased proofs. A differing key cannot settle forms whose equality requires
extensionality, proof irrelevance, structure eta, or blocked-match comparison.
Fresh variable identities are globally unique and monotonically increasing;
the implementation assumes a single checking thread.
