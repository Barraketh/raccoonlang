# Raccoon kernel

## Trust boundary

The elaborator resolves source names and lowers surface syntax to `CoreAst`.
The checker, evaluator, conversion, inductive validation, match refinement,
termination checking, and residual construction form one trusted implementation.
There is no independent certificate checker.

Declarations are checked once and published in an environment. Every
definition is transparent and publishes its evaluated value. Axioms publish
symbolic heads and may occur in any module. Only the selected prelude may
install primitive quotient bodies. The prelude otherwise contains ordinary
checked source declarations.

## Universes and function types

Propositions and data types use separate universe tags. `Prop` is the universe of
propositions, and `Prop : Type`. Bare `Type` denotes data universe zero;
`Type { level = u }` denotes data universe `u` and has type
`Type { level = succ(u) }`. In particular, `Type : Type { level = one }`.
There is no `Sort` former. Universe levels are second-class parameters whose
forms are `zero`, `one`, `succ`, and `max`, qualified by `Level` outside a
`Type` level field. Universe conversion is exact; there is no cumulativity.

A dependent function type whose codomain is a proposition is itself a
proposition, even when its domain ranges over data universes or has the
internal `Large` classifier of a level binder. A data-valued function type
lives in the data universe given by the maximum of its domain and result
levels; a proposition-valued domain contributes level zero. A codomain equal
to `Prop` is different from a proposition: `Prop` itself is a data type.

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
variables. Matching a proposition family at the root of the scrutinee type can
refine that family's indices from a constructor result. That rule does not
recursively invert proposition families occurring inside another equality
index. Data-family argument inversion under equality uses the separate,
restricted N1 premise: one argument of the same checked data-family head at a
time. Family signatures are checked, but N1 remains a trusted type-generativity
premise; no independent kernel verifies it.
Arbitrary applications, function type components, and blocked computations
are not invertible. Occurs failures and equations with several possible
solutions stay stuck. Level variables link only when normalization forces a
solution.

Only a homogeneous equality between distinct constructors of the same checked
data family at common parameters, with no-confusion evidence for both
constructors, proposes apartness. A proposed exclusion becomes an unreachable
branch only after an ordinary contradiction term checks. The proposal is
formed using a private, checked equality basis bootstrapped without a source
prelude, then checked in the original environment. Unsupported quotation or
any failed check leaves the branch reachable. Match reachability decisions
share this gate; a conversion failure alone never drops a case. This validates
exclusions, not successful refinement links, and does not remove the trusted
N1 premise above. Proof constructors, quotient constructors, and family heads
do not supply constructor apartness. Structure eta expands eligible refinable
variables at the refinement boundary, recording forced identities.

## Inductives and matching

Inductive declarations have uniform parameters, indices, and constructors.
Their result must be a sort. Every constructor returns the declared family at
the common parameters; source fields must be strictly positive in every family
of a mutual block. For data families, field universe levels must fit the
family's declared level. Parameters and indices are checked elementwise by the
universe of their type, descending through data-valued function types. Thus a
family parameter of type `Type -> Type` requires a family result in at least
`Type { level = one }`, because `Type` itself lives in that universe. A
proposition family has no data-universe bound. Each sibling uses its own
declared sort.

Mutual blocks are checked atomically. Family signatures see the incoming
environment, and constructors see provisional heads for every sibling. No
partially checked block is published. Positivity information is compiled once
for each common parameter. The occurrence and positivity scans are local to
the declaration or mutual block being checked. Nested uses of an already
checked family reuse its published positivity facts; no global summary is
attached to runtime values.

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
reconstruction information supports recovering a unique constructor and its
fields, or when match refinement certifies the selected fiber empty. An erased
proof cannot expose a hidden data witness. Proposition-valued matches can erase
their results directly. Refinement may sharpen the exact proposition and its
indices, enabling proof recanonicalization; it never changes a sort tag from
data to `Prop`.

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

Tail calls in a definition's final position, including a match branch or block
result, run in an evaluation loop. Other calls use the ordinary evaluator; if
evaluation exhausts the host stack, checking reports `EvaluationTooDeep`.

During checking, recursive names denote stubs that enforce the decrease and
may only occur as application heads. Checked recursive groups publish lazy
bindings over one shared environment; bodies do not execute while that knot
is formed.

## Axioms and quotients

An axiom declares a symbolic constant of a checked type and has no body. Every
definition computes during checking and evaluation. Proof representation
remains determined by its type, regardless of whether the value came from an
axiom or a definition.

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

Value dependencies and keys are computed eagerly from child metadata as values
are created, avoiding repeated recursive walks through deep value chains. Printing
uses an explicit work stack for values and residual syntax. Materialization
shares an identity memo across one root operation and one immutable equality
store, including environments reached while reducing blocked terms; a memo is
not reused with another store.
