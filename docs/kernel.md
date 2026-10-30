# Kernel rules

## Natural number normal forms

`Bool`, `Nat`, their constructors, and the native `Nat.add`, `Nat.mul`,
`Nat.pow`, `Nat.sub`, `Nat.pred`, `Nat.isZero`, `Nat.beq`, `Nat.ble`,
`Nat.div`, `Nat.mod`, and `Nat.expand` are kernel declarations present beneath
every prelude and program; they cannot be redeclared. Ordinary source functions
acquire no arithmetic laws merely from their names.

Arithmetic evaluates to sums of products with arbitrary-precision nonnegative
coefficients, constants, and exponents. The normal forms decide exactly these
definitional laws: addition and multiplication are associative and commutative
with units, `0 * x = 0`, closed arithmetic computes, `Nat.succ(x) = x + 1`,
multiplying by a numeral distributes, `x^0 = 1`, a numeral power is a repeated
product, powers of equal bases multiply by adding exponents
(`x^a * x^b = x^(a + b)`, symbolic or not), and `1^e = 1`. Nothing symbolic
distributes: a product of sums stays a product whose factors are the sums, so
`a * (b + c)` and `a * b + a * c` are different forms, and a power with a
symbolic exponent keeps its whole base, so `(x * y)^a` and `(x^a)^b` are not
split. Distribution happens only on request: `Nat.expand` multiplies every
product of sums out and collects like terms, and the prelude's builtin
`Nat.expand_eq(n) : Eq(Nat, n, Nat.expand(n))` proves the expansion equal to its
argument. On a closed value `Nat.expand` is the identity; otherwise each
monomial of the expansion is stuck as `Nat.expand` of that monomial, an atom
that converts by congruence and expands again when it resumes, which keeps
`Nat.expand` stable under substitution. Two applications convert exactly when
their expansions do, and the stuck monomials add, show known successors, and
cancel in comparisons. The prelude theorem `Nat.mul_add`, proved by expansion,
states distributivity, and every other semiring identity follows from it and
conversion; the prelude theorems `Nat.mul_pow` and `Nat.pow_mul` state
`(x * y)^a = x^a * y^a` and `(x^a)^b = x^(a * b)`. Normalization needs no
limits; a closed power too large for the JVM to represent raises
`NatValueTooLarge`. Expansion can be exponential and has no budget either.

Each Nat value has one representation: zero is the `Nat.zero` constructor, a
lone neutral atom is itself, and everything else, including every successor, is
a compact form; constructing `Nat.succ(x)` yields the form `x + 1`. The
constructor view exposes a form with a positive constant as `Nat.succ` with
that constant decremented. A form with zero constant, including a product of
successors or a symbolic power, blocks on all its dependencies. A decimal
literal such as `42` has type `Nat` and evaluates directly to its constant.
Substitution recomputes affected arithmetic, including symbolic exponents and
bases, and blocked matches. Atom equality respects existing definitional
conversion, including when convertible atoms have different structural keys.

Truncated subtraction and the comparisons depend only on the signed difference
of their arguments: they cancel common whole terms and decide when one
remaining part is zero or the other has a known successor, and otherwise stay
stuck on the canonical parts. A sum inside a factor is opaque to cancellation.
They satisfy the recursive equations, such as
`sub(a, succ(b)) = pred(sub(a, b))`. A stuck subtraction absorbs only a known
constant subtrahend, so every result is stable under substitution.

Division and remainder compute on closed arguments. An open application
reduces only where a numeral argument fixes the result: a zero divisor gives
`div(a, 0) = 0` and `mod(a, 0) = a`, as in Lean, a divisor of one gives
`div(a, 1) = a` and `mod(a, 1) = 0`, and a zero dividend gives zero. Otherwise
it is stuck on its arguments, an atom of the normal forms that converts by
congruence and resumes under substitution. No law about them is definitional
at a symbolic divisor, and the prelude assumes none.

Unequal symbolic forms do not establish contradiction. Refinement keeps
whole-variable linking and successor cancellation, and otherwise leaves
arithmetic equations stuck. A Nat's structural subterms are its known
predecessors; monomials, factors, and summands are not structural subterms.
Termination orders a Nat metric component by `<` instead, decided on the same
signed difference: a candidate is smaller when the root minus it cancels to a
positive constant plus terms, so `b` is below `a + b + 1` but not below
`a + b` ([mutual blocks](#mutual-blocks)). Positivity treats
factor bases and symbolic exponents, including sums, as arguments of the Nat
operations, so a target occurring in one is never positive. The [Nat normal forms design](nat-normal-forms.md)
specifies the laws, the representation, and quotation.

## Packed lists and kernel strings

`Sort`, `List` with `nil` and `cons`, the natives `List.append` and
`List.length`, and the structs `Char` (`mk (val: Nat)`) and `String`
(`mk (data: List(Char))`) are kernel declarations beneath every prelude and
program; they cannot be redeclared.

Every cons application of a list-shaped type (one recursive constructor with a
single recursive field at its own parameters, no indices, not `Nat`) is a word:
its layers are stored in shared chunks, invisibly to conversion, matching,
refinement, quotation and printing, and every word is constructor data. A
word's key is a polynomial over the integers modulo 2^61 - 1 with fixed bases;
like every key, it guards against accidental collisions, not crafted ones.

`List.append` follows its source definition, sharing storage, and ends in an
ordinary stuck application at a stuck tail. `xs ++ [] = xs` and
`length(xs ++ ys) = length(xs) + length(ys)` hold definitionally; associativity
is the prelude theorem `List.append_assoc`. A string literal always has type
`String`. [Packed lists and kernel strings](packed_lists.md) specifies the
rules and justifies the design.

## Type patterns

A binder's type pattern, such as `List($A)`, is opened on the type of the
argument: a capture reads the value at its position in that type, or the level
or kind of a universe. Reading by position inverts the application only at a
family or opaque head. At a head that computes, such as
`def SList (A: Sort($u)) : Sort(u) := List(A)`, the position need not hold the
head's argument, which then need not fit the head's parameter: `SList($A)`
opened on `List(Protocol.Supply)` reads `A := Protocol.Supply`, which is no
`Sort(u)`. So every binding re-checks, on the values it opened, each
application in the pattern that has a capture below it, as the declaration
checked it on fresh ones: the values must instantiate the head's parameter
telescope, a constrained capture's value must have its constraint as its type,
and the type rebuilt from them must convert with the argument's type. The body
may then assume that every capture has its declared type. Argument checking,
the arguments that instance search infers by unification, and the fresh
arguments that compare function types are all bound this way. A declaration
refuses a capture that no binding can read, such as `$u` in
`Sort(Level.max($u, $v))` or `$k1` in `Univ(Kind.join($k1, $k2), $u)`
(`CaptureWithoutOpening`): in a universe, a level capture must be the level
or a `Level.succ` of it, and a kind capture the kind itself.

The reading by position is incomplete: a capture under a head that computes
matches only where the head keeps its argument at the position the capture
reads, the same position in the head's result as in the head's application.
A head that reorders its arguments matches only where they agree: with
`def Swap (A: Sort($u))(B: Sort($v)) : Sort(Level.max(u, v)) := Prod(B, A)`,
`Swap($A, $B)` opened on `Prod(Nat, Bool)` reads `A := Nat` and `B := Bool`,
rebuilds `Prod(Bool, Nat)`, and refuses the argument. A head that nests its
argument deeper matches no argument at all: with
`def S2 (A: Sort($u)) : Sort(u) := List(List(A))`, `S2($A)` opened on
`List(List(Nat))` reads `A := List(Nat)`, rebuilds `List(List(List(Nat)))`,
and refuses it. A universe of constant kind has the positions of `Sort(l)` or
`Lin(l)`, its level at position 0, and one of a variable kind has none: with
`def L (u: Level) : Sort(Level.succ(u)) := Lin(u)`, `L($u)` opened on
`Lin(Level.zero)` reads `u := Level.zero` and rebuilds it, and opened on
`Type` reads the same level, rebuilds `Lin(Level.zero)`, and refuses it. So a
head over `Univ` matches no universe: with
`def U (k: Kind)(u: Level) : Sort(Level.succ(u)) := Univ(k, u)`, `U($k, $u)`
finds no position 1. These refusals are sound.

## Function-type equality

A function type is one group of parameters: the parser reads an arrow chain
`(x: A) -> B -> C` as one function type of two parameters, and a parenthesized
codomain as a function type of its own, so `A -> (B -> C)` takes one argument
and returns a function. A lambda's or a definition's parameters are one group
the same way, so `fun (x: A): (B -> C) => …` has type `A -> (B -> C)`, not
`A -> B -> C`. Types of different groupings differ: application takes a group's
arguments together, so the two are not interchangeable.

Function types compare binder domains and constrained-capture classifiers by
exact definitional equality. Universes are not cumulative: an argument, too, is
checked by conversion of its type with the binder's, so `Type` is no
`Sort(Level.one)`, and a universe-polymorphic binder `Sort($u)` takes types of
every level.

Corresponding binders must have the same instance markers and capture
operations: capture roots, projection paths, level subtraction offsets, and
kind captures. A level capture opens on a universe of any kind; the binder's
type, which the comparison instantiates, tells `Sort($u)` from `Lin($u)` and
from `Univ($k, $u)`, and a constrained capture's constraint is checked as at a
binder.
Names may differ. After opening one telescope on fresh arguments, the checker
instantiates the other with those same arguments using exact checking, and the
reverse: each telescope must admit the other's generic arguments. It then
compares the codomains. Requiring matching capture operations is conservative;
in particular, `Sort($u)` and `Sort(Level.succ($v))` admit different domains and
cannot be equated by successfully matching an argument in just one direction.
Matching operations do not make the domains equal at a head that computes:
`(xs: SList($A)) -> List(A)` is not `(xs: List($A)) -> List(A)`, whose binder
takes linear elements too, though the eta-expansion
`fun (xs: SList($A)): List(A) => f(xs)` of an `f` of the second type has the
first.

## Lambdas in types

A lambda may stand in a type wherever the type holds a term: as an argument of
an application in a binder type, a codomain, a `let` annotation, a field or
constructor result type, or a motive, as in
`List.Every(xs, fun (x: Nat): Prop => Nat.le(x, 3))`. There is no partial
application: a function takes all its explicit parameters at once, so a
predicate argument is written as a lambda. A lambda in a type is checked as any
lambda, and is a function value, never a type: a lambda as a whole binder type
is `NotAType`. It is part of a read extent (S1), so it may have linear
parameters, which its body uses at most once (F4), but it captures no linear
local (F5).

Conversion compares two lambdas by their bodies on shared fresh arguments, so
`fun (a: Nat): Prop => Eq(Nat, a, a)` and `fun (b: Nat): Prop => Eq(Nat, b, b)`
convert. A body stuck on a match converts with a body stuck on the same match
written elsewhere, by its code ([stuck matches](#stuck-matches)), so a
predicate defined by cases may be written out in each type that shares it.
Positivity opens a lambda in a field type on fresh
arguments, so the family being declared occurs in neither its type nor its body
([family argument size](#family-argument-size)), and the size rules read the
types a lambda gives. A projection's type is a field type's lambda as a value,
over the earlier fields' projections, so it captures no local and F5 does not
arise: a linear record whose field type holds a lambda over an earlier copyable
field projects that field, while a lambda over an earlier linear field is
`LinearCapture` in the constructor's own telescope.

## Stuck matches

A match whose scrutinee is no constructor, nor, at a structure eta type, a
value with an eta view, is stuck: a value of its motive that waits on its
scrutinee and resumes when refinement makes it a constructor. A stuck match is
its checked code closed over the locals it reads, its *captures*. Two stuck
matches convert when their code is the same and their captures convert, in
order. The code is the checked match, compared exactly: its scrutinee, its
motive, each case with its constructor, fields, equation and body, and every
argument and proof the checker inserted, up to the names and source positions
of its locals and binders. A local it reads is compared by value, and the
captures are ordered by where the code first names them; a local it binds, a
field, a `let` or a binder, is compared by its position. So `isZ(x)` and
`isZ2(x)` convert for

```
def isZ (n: Nat): Bool := {
  match n returning Bool with
  | Nat.zero => Bool.true
  | Nat.succ m => Bool.false
}
def isZ2 (k: Nat): Bool := {
  match k returning Bool with
  | Nat.zero => Bool.true
  | Nat.succ j => Bool.false
}
```

and so do `isZ` and a lambda in a type that writes the same match. Matches that
differ in a case, in their motive or in their scrutinee do not convert, even
when they agree on every constructor: conversion does not compare branches,
and a motive is code even where its values convert. A case that names a field
it does not use binds a slot that an anonymous field does not, so
`| Nat.succ m => e` and the wildcard's `| Nat.succ _ => e` are different code.

**Recursive functions** convert as fixpoints. Two recursive definitions, or two
members at one position of mutual blocks of one size, convert when every pair
of members has one type and, opened on shared fresh arguments, their bodies
convert with the blocks' recursive slots bound to shared fresh variables, one
for each pair: the two blocks' bodies are then one function of their recursive
slots, and two terminating fixpoints of one function are the same functions.
Opening them with their slots bound to the functions themselves would compare
the same pair again inside the stuck matches that capture them, without end. A
recursive function does not convert with one of another shape, such as a
member of a mutual block with a single recursive definition, while a function
that is not recursive is opened as any lambda, so a wrapper
`def h (n: Nat): Nat := f(n)` converts with `f`.

**Quotation**, which motive inference uses, rebuilds a stuck match as its own
code over its captures: a capture that a local of the context holds is read
from that local, and every other is quoted once, in a `let` before the match.
Evaluating the quotation gives a stuck match of the same code on the same
values, which converts with the one quoted, whatever its captures hold.

It is sound because the code decides what a match computes: two matches of one
code resumed on convertible captures evaluate the same code on convertible
values, and node identities, names and positions change no result. Codes are
interned by exact structural equality, so a hash collision cannot make two
codes one, and a stuck match's key, its code's serial number and its captures'
keys, guards against accidental collisions as every key does. A capture may be
a recursive function, and comparing two that are terminates, since their
recursive slots are paired rather than unfolded.

## Nominal Type families

Fully applied, Type-valued inductive families obey these nominal principles,
and so do families of every kind, those declared in `Lin(u)` or `Univ(k, u)`
(see [linear types](#linear-types)); "Type" below covers them all:

- **N1 — injectivity:** equality of instances of the same declaration forces
  equality of their complete dependent argument tuples.
- **N2 — distinct declarations:** instances of different family declarations
  are distinct types, even when their constructors have the same shape.
- **N3 — distinct forms:** family instances, Type-valued function types, and
  Type universes are pairwise distinct forms. Universes whose kinds are
  different constants are apart, so `Sort(u)` and `Lin(v)` are; a universe
  whose kind holds a variable is not apart from either.

These rules apply inside nested Type-family arguments. Proof arguments compare
modulo proof irrelevance. Axioms and blocked computations provide no nominal
evidence. The unifier does not assume injectivity of function types. Failure to
compare universe levels remains inconclusive rather than a contradiction.

Proposition families have no general injectivity or distinctness rules. When
checking a constructor branch, the match checker obtains equations between
family arguments from the constructor's declared result and the scrutinee's
indices. These equations follow from indexed elimination. For example,
matching `Eq.refl(z)` against a proof of
`Eq(Prop, P(n), P(m))` supplies `z = P(n)` and `z = P(m)`. The resulting equation
`P(n) = P(m)` supplies no equation between `n` and `m` when `P` is a Prop family.
Proposition-valued function types supply no nominal distinctness evidence either.

### Refinement outcomes

Refinement unification has three outcomes:

| Outcome | Meaning |
|---|---|
| Success | The equation is discharged using only forced, permitted variable refinements. |
| `Contradiction` | No-confusion or a nominal rule refutes the equation. |
| `Stuck` | The checker can neither discharge nor refute the equation. |

For refinement-based coverage, only `Contradiction` justifies excluding a branch.
Failed attempts expose no partial substitutions.

A branch's fields enter fresh, at the scrutinee type's own parameter arguments:
the constructor's witnesses of the family's parameters, its erased binders and
the captures named like parameters, are linked to them. Parameters are uniform,
so this needs no equation. Refinement then relates the scrutinee to the
constructor applied to those fields, and the constructor's result indices to
the scrutinee type's. A stuck equation keeps the constructor reachable and
provides no refinement; the fields keep their types at the scrutinee's
parameters. A witness whose type is narrower than its parameter's, such as
`$A in Sort($u)` for a parameter `A: Univ($k, $u)`, cannot always be linked;
refinement relates it as it relates an index, so `k := Kind.copy` in that
branch.

A scrutinee that is a variable, the root, is unified with the constructor
applied to the branch's fields, which links the root to that value once their
types unify. That type unification refines the variables of the scrutinee's
type, its indices included, as the refinement of the constructor's result
does, so at a variable index, such as `v: Vec(A, n)` or a packet
`Toks(P, init, s, A)`, the index is solved and the root linked in one step. In
the branch the root's value is the constructor value, as a nested match on it
sees, and termination checking reads it: a field is a structural subterm of the
root at a variable index as at a known one. A proof root is linked explicitly
instead ([recursion on proofs](#recursion-on-proofs)), and any other scrutinee
is related by the result refinement alone.

After structural comparison and variable refinement, an exhaustive classifier
identifies data constructor values, fully applied Type-family instances,
Type-valued function types, and Type universes as rigid forms. Different
remaining rigid forms produce `Contradiction`; two function types remain `Stuck`.

Unrefinable variables, opaque symbols and applications, blocked matches,
function values, and partially applied family or constructor heads provide no
rigid-form contradiction. Neither do propositions, unresolved level equations,
or primitive forms without a nominal apartness rule. These cases remain
`Stuck`. Adding a value form requires an explicit classification. The constant
kinds `Kind.copy` and `Kind.lin` contradict, as values of `Kind` and as the
kinds of two universes; a kind that is one refinable variable is solved, and a
join of variables is `Stuck`.

### Family argument size

A Type family declared in `Sort(n)` or `Lin(n)` must have sufficiently small
parameters and indices for its nominal argument labels. The checker computes a conservative
minimum level for each argument's type:

| Argument type | Required level |
|---|---|
| `Sort(m)` or `Lin(m)` | `m` |
| `Level`, `Kind`, `Prop`, or a proposition | zero |
| A record with structure eta | The maximum of its fields' required levels, at the instance |
| A Type-valued function type ending in `B` | Maximum of its domains' classifier levels and the recursive bound for `B` |
| Any other type | Its classifier level |

Dependent function domains and results are evaluated under fresh typed binders.
A universe used as a function domain costs its successor classifier level;
a universe used as an argument type or function codomain costs its own level.
The resulting bound must be at most the family's declared level for every
valuation of symbolic level variables. Each family of a [mutual
block](#mutual-blocks) is bounded by its own declared level.

Thus `List(A: Type): Type` and a family with arguments `A: Type` and
`B: A -> Type` can remain in `Type`. A record is charged by its fields, since
each of its values is its constructor applied to its fields: so a `Proto`, an
atom type and a relation into `Prop`, costs level 0, as its two components
would, while a record holding a `Type -> Type` costs level 1, and a family with
two constructors still costs its own universe's level
(raccoon-formalization `DESIGN.md` §10, the elementwise rank lemma). A family taking `F: Type -> Type` or
`F: Type -> Prop` requires `Sort(Level.one)` or above. This check also applies
to families without constructors. `FamilyArgumentTooLarge` identifies the
argument and required minimum level.

Prop families are exempt from this size check. Stored fields of Type families
retain their stricter classifier-level bound. Both Type and Prop families remain
subject to strict positivity checks.

Function-valued family arguments must be free of the positivity target, even in
an otherwise positive argument position. The checker inspects both a lambda's
type and its body opened on fresh arguments. This also applies when computing
which family arguments are positive and when excluding recursion inside a
family's own arguments.

No family of the block occurs in a constructor's result indices
(`FamilyInResultIndex`), as in Coq and Lean. An index constrains the family by
an equation rather than storing a field, and an equation that names the family
need not have a solution: with propositional extensionality,
`inductive Bad indices (P: Prop) : Prop` with `mk : Bad((h: Bad(True)) -> False)`
proves `False`, since a match on `Bad(True)` yields the index equation. An index
may read a field whose type names the family, such as `T(p.fst)` for a field
`p: Prod(Nat, T(0))`: a field is a variable, not an occurrence.

The family being declared is fresh: no value made before its declaration can
name it, so a reference to it starts only at its own head and reaches a value
only through what that value is built from. So a stuck computation, such as a
projection of a parameter, `List(P.Atom)`, or a stuck call of an earlier global,
certifies that the family is absent when its type, its captures, the values of
its environment and its match term do not mention it (main-new's
declaration-time rule). A stuck computation that does mention it cannot certify
a positive occurrence, nor uniformity, and a stuck application whose arguments
mention it is not positive, as before.

### Current limits

Instance search does not infer candidate arguments through Prop-family
applications. For a reachable constructor, large elimination requires complete
result refinement; unresolved equations can reject otherwise valid matches.
After refinement, two fresh copies must agree on the types and values of stored
fields and type-pattern captures. Proof values compare by proof irrelevance
only at the same proposition; a proof field cannot hide an unforced data or
proposition capture. Captures determined by the scrutinee's parameters or
indices remain eligible for large elimination.

## Single-constructor matches and let patterns

The surface AST represents each ordinary let with a mandatory binding pattern: a
name, a discard, or an unpack of constructor fields. Instance lets are a
separate form requiring a name. Core and checked lets remain ordinary local
bindings.

`CoreAst.Term.MatchOne` supplies a scrutinee, field binders, and a body without
naming a constructor. Its checker requires exactly one declared constructor,
including when the scrutinee is already a constructor or only one branch is
reachable. It resolves that constructor and uses the same coverage, refinement,
branch, and Prop elimination checks as a named match. Both forms produce the
existing checked match representation.

Let-pattern lowering is syntactic. The elaborator saves the RHS in one ordinary
let, retaining any whole-RHS annotation, and places the remainder of the block
inside a `MatchOne`. Nested patterns produce nested matches; all immediate field
slots are allocated before descendants. Erased constructor arguments and
type-pattern captures are excluded from the field binders. No pattern checking
occurs in the ordinary let checker.

Both match forms use an explicit motive when present, otherwise a contextual
expected type, otherwise a common branch result type expressible in the outer
context. Inference checks branch agreement under each branch's own refinements.
It cannot quote an outer local through a refinement that changes that local's
type. A result requiring branch-local information needs an appropriate
annotation, or must remain inside the branch.

The feature introduces no runtime value form. Its equality rule is structure
eta, below.

## Wildcard cases

A match's last case may be `| _ => e`. It stands for one case for each
reachable constructor that the written cases do not name, which are exactly
the constructors a missing case would be reported for: the scrutinee's own when
it is a known constructor, and otherwise every constructor whose result is not
apart from the scrutinee's type, so a stuck equation keeps one. Each case binds
its constructor's fields anonymously and checks `e` under that constructor's
own refinement, as the case written out with `_` for every field would. A
wildcard that stands for no constructor is `RedundantCase`, at the wildcard;
one that is not last, a second one, or one that binds fields is a parse error.

The checked match is the expansion, one case per constructor in declaration
order, and each case has its own copy of `e` whose function types, lambdas and
matches have fresh node identities (`CoreAst.freshCopy`): two expansions may
check to different residual code, since their refinements differ, so they must
not share an identity; a stuck match is identified by its code instead
([stuck matches](#stuck-matches)), so two expansions that check to the same
code are the same match. Evaluation, conversion, the ledger and the termination
checker see only written-out cases. So a wildcard over a constructor with a
linear field drops that field, as `_` does (L4, affine use); each expansion is
its own path, on which a linear local may be used once; and in a read extent
the expansions only read, with separation checked at every call of each.
A diagnostic inside an expansion is located in `e`, but does not name its
constructor.

## Match equations

`match h : e returning M with …` binds `h` in every case, after the case's
fields: in the case of constructor `C` with fields `x̄`, `h : Eq(T, e, C(x̄))`,
where `T` is the scrutinee's type and `e` the scrutinee, both read through the
case's refinement, and `C(x̄)` is at the constructor's own result type. Nothing
else changes: the cases, the motive and coverage are as for `match e`, and
neither the motive nor another hypothesis is rewritten by the equation; a proof
uses `h` with `Eq.subst` or `Eq.substProp`. Each case a wildcard stands for binds
`h` at its own constructor. `h` is a local of the cases only, not of the
scrutinee or the motive, and a field may not share its name.

- **Copyable data.** `T` must be in a `Sort`. `Eq` has no linear carrier (L8),
  so a scrutinee of linear or variable kind is `MatchEquationUnavailable`, at
  `h`, and so is a proof, since `Eq` ranges over no proofs.
- **Indexed families.** The equation relates values of one type. In an indexed
  family, a case's refinement must therefore equate the constructor's indices
  with the scrutinee's, as it does at a variable index, or the case is
  `MatchEquationIndexed`, as at a stuck index such as `f(n)`.
- **The equality family.** The equation's `Eq` is the global `Eq`, when that is
  exactly the prelude's equality family, `Eq (A: Sort($u)) indices (x: A)(y: A)
  : Prop` whose one constructor is `Eq.refl (x: $A in Sort($u)) : Eq(A, x, x)`,
  checked at the match (`MatchEquation.validate`). Otherwise a named equation is
  `MatchEquationUnavailable`, so no prelude or program can make `h` state
  something false.
- **Evaluation.** A case runs only when the scrutinee's value is its
  constructor applied to the fields' values, or, at a structure eta type, is
  viewed as one; `h` is then bound to `Eq.refl` of that value. A blocked match
  binds nothing. A case the checker takes for a known constructor is checked
  with that same proof, since the match's value is then the case's; every other
  case is checked with `h` a hypothesis.
- **The ledger.** `h` is a proof, so it is never tracked and may be used
  freely, and the copyable `e` puts nothing linear in the proposition.

It is safe because `h` adds to each case a hypothesis that holds whenever the
case runs, by reflexivity; a case no run reaches, such as one whose refinement
is stuck, is checked under an unprovable hypothesis, as it is already checked
against impossible field values. Evaluation never reduces by `h`.

## Structure eta and projections

A family with exactly one constructor is a **record**. There is no `struct`
keyword: records are ordinary `inductive` declarations. A record's named fields
are declared in its namespace, beside its constructor, so no global shares a
field's name (`AlreadyDefined`), and `open Prod` aliases `fst` and `snd`.

**Projection** is a kernel operation. `r.field` selects a named field of a
value `r` of a record, and `Prod.fst(p)` writes `p.fst` explicitly, requiring
`p` to be a `Prod` and taking exactly that one argument. `Prod.fst` unapplied is
no function value (`UnappliedField`). A selection `r.name` that names no field
of a record is `NotFound`; in particular a family with more than one
constructor, or none, has no fields, and a global `Fam.name` in a record's
namespace is applied as written, `Fam.name(r)`.

A projection is the stuck evaluation of a canonical one-branch match,
`match r returning T with | mk x0 … xn => xi`, one match node per field of the
family, whose motive `T` is the field's type at `r`. On a constructor value it
is the stored field; on any other it is stuck, so two projections of one field
of convertible values convert ([stuck matches](#stuck-matches)), and a
projection of a recursive record's
neutral value reduces no further. The checked term is a node of its own
(`ElabAst.Term.Proj`), which evaluates the same way and quotes back to itself:
the projector is a closed term over its own locals, with a motive that is a
value, so a residual could not splice it in.

The field's type at `r` is read off the record's **template**, its
constructor's telescope opened once on fresh variables: the field's type there,
with the constructor's result unified with `r`'s type one argument at a time,
and the earlier fields linked to their projections. An argument that unifies
states what every constructor value of that type satisfies; one that does not,
such as a stuck index equation, leaves the template's variables free, as a
match leaves a stuck branch unrefined. So an indexed record projects too. For
`Sized indices (n: Nat) | mk (k: Nat)(v: Vec(Nat, k)) : Sized(k)`, `s.v` is a
`Vec(Nat, n)` at `s : Sized(n)`, since every constructor value there has `k`
equal to `n`, though `s.k` stays a projection. For `G indices (k: Nat) | mk
(m: Nat)(v: Vec(Nat, m)) : G(Nat.succ(m))`, `g.v` is a `Vec(Nat, g.m)` at a
variable index, whose equation is stuck, and a `Vec(Nat, 2)` at `G(3)`. A field
whose type still depends on a variable of the template, a capture that no
argument determines, such as `$n` in `(v: Vec(A, $n))`, has no projection at
that type (`InvalidStruct`), and neither has a field whose type depends on that
one; the record's other fields project, and a constructor-headed record projects
every field, to the stored one.

A projection is checked as its one-branch match would be:

- **Prop.** Projecting out of a proof is that match's elimination: a data field
  is a large elimination, refused unless the family allows it
  (`PropEliminationRestricted`), and a proof field a small one. The motive holds
  the projections of the earlier fields that the field's type depends on, and
  those are checked too: `e.proof` of `Exists`'s `intro (witness: A)(proof:
  p(witness))` is refused as `e.witness` is, since it would hold the witness's
  projection in a type, where an elimination of `Eq` into data reads it back.
  An earlier field that the type's arguments solve is no projection there, so
  `x.h` of `W indices (n: Nat) | mk (n: Nat)(m: Nat)(h: Eq(Nat, n, n)) : W(n)`
  is `Eq(Nat, k, k)` at `W(k)`, while `x.m` is refused.
- **The ledger.** A projection uses its record, so a second projection of a
  linear record on one path is `LinearReused`, and the other fields are dropped
  (L4, affine use). In a read extent it is no call but an inspection, as a match
  is, and its provenance is field `i` of its record's (S1): `(r, p ++ [i])` of a
  record that is exactly the region `(r, p)`, and the record's whole provenance
  otherwise. So `observe(join(p.fst, p.snd))` in a proof reads two separate
  regions, while `join(p.fst, p.fst)`, a field with its record, or a field with
  the same field taken by a match of the record, overlap; a stored field's
  index counts no erased argument or capture, as a match's fields do not.

A record is **eta-eligible** when it also has no indices and no recursive
field, is not in `Prop`, and its arguments determine every field's type; its
kind and level do not matter, so linear and kind-polymorphic records are
eligible, and so are the kernel's `Proto`, `Observed` and `Fresh`. Proofs of a
`Prop` record are irrelevant instead.

Each condition protects the eta view:

- **One constructor.** A neutral value of a family with several constructors is
  none of them, so there is no constructor form to expand it to.
- **No indices.** At a variable index the expansion can have another type:
  `G.mk(g.m, g.v)` is a `G(Nat.succ(g.m))`, not the `G(k)` that `g` is, so a
  match on `g` would run a branch checked under `k = succ(m)` at a `k` that is
  only a variable. This asks more than soundness does, since a record whose
  result every index can take would expand correctly, but eta there needs a
  field that the index solves to expand to the index, and no program needs it.
- **No recursive field.** Match evaluation on a neutral value takes its branch,
  so a structurally recursive function applied to a neutral value of a
  recursive record would unfold forever during checking, `last(x)` to
  `last(x.next)` to `last(x.next.next)`. Any field that mentions a family of the
  block counts, even one that reaches it only under another family, as in
  `List(Tree)`, whose own stuck match would stop the unfolding: telling those
  apart is not worth its cost.
- **Not in `Prop`.** Proof irrelevance already identifies proofs, and the view
  would build data projections out of a proof in unification and match
  evaluation, which no elimination check sees: with irrelevance, the witnesses
  of any two proofs of one `Exists` would convert.
- **Determined field types.** The view holds a projection of every field, and a
  field whose type depends on a capture that no argument determines has none.

Eta is a rule, not a representation. At an eligible type, a value is
definitionally its constructor applied to its fields. Its *eta view* is its
stored fields when it is constructor-headed, and its field projections
otherwise. The view is read by:

- **conversion**: a constructor-headed value converts with a value that is not
  when its stored fields convert with the other's projections, and its type
  with the other's; two neutral values compare as before;
- **unification**, which unifies the types, then such fields pairwise, so a
  matched constructor's witnesses of the family parameters are solved before
  the fields whose types mention them;
- **match evaluation**, during checking and at run time: a match on a neutral
  value at an eligible type takes its one branch with the projections, so a
  destructuring computes;
- **structural descent**: a projection of a neutral value is one of its fields.
  A projection of a neutral value of a record without eta, such as `t.kids` of
  a tree, is no structural subterm of it, though once a match has refined the
  root to its constructor, a projection of the root is the matched field.

So `P` converts with `Protocol.Proto.mk(P.Atom, P.Step)`, and a pair `p` with
`Prod.mk(A, B, p.fst, p.snd)`, but a tree `t` not with `Tree.node(t.val,
t.kids)`. Applying a neutral function value, such as the projection of a
function field, gives a neutral application. Eta adds no use of a linear value:
it acts in conversion and evaluation, which the ledger does not see, while a
match still consumes its scrutinee (L4) and a projection is a use or a read as
L5 says.

## Recursion on proofs

A recursive function whose classifier is `Prop`, so whose result is a
proposition, may decrease a proof: as its `structural` metric, or as a
parameter component of a `lexicographic` metric. A function with any other
result may not, and a measure, a clause or a component, must live in
`Type`/`Sort(u)` in every function. `TerminationChecker.metric` enforces both
when it checks the metric.

The decrease test cannot use conversion. Proof irrelevance makes every proof of
a proposition convertible with every other, so a converted comparison would
accept any call, including a call on the matched proof itself. A proof
component instead decreases when the call passes, by structural key, a proof
field of the current root or a proof field of one of those, transitively. It
is unchanged when its key equals the root's. A proof call keys as its forced
value ([proof calls](#proof-calls)). Any other proof is neither, and
the call is `NonDecreasingRecursiveCall`; this covers a rebuilt proof of a
field's proposition. As in conversion, equal keys are trusted to mean equal
values. The search follows proof fields only; it does not enter data fields,
such as the field of `Fact.mk(h)`. Data components keep their orders, by
conversion and structural subterms, or `<` on Nat, and data subterm search
still skips proof fields.

The root is read through the branch's refinement. Unification compares proofs
by their propositions and so never links a proof variable to the constructor a
branch matched. `MatchChecker.computeReachableCtors` therefore links a proof
variable scrutinee to its constructor value in each reachable branch whose
refinement succeeds, once that refinement has unified the constructor's type
with the scrutinee's. A branch whose refinement is stuck links nothing: its
constructor's type was never unified with the scrutinee's, and the link would
change the proof's type. Termination checking reads the link. Elsewhere a proof
and the constructor value it is linked to convert, as proofs of one
proposition, but the link is the proof's value in the branch, as for a refined
data variable: a nested match on the same variable sees a known constructor, so
its other cases are `UnreachableCase`.

## Mutual blocks

`mutual { … }` declares inductive families only, or recursive definitions only,
that may refer to each other. A block is checked as a whole and published only
once every member has checked, each under its full name.

**Families.** Each family's header, its parameters, indices and universe, is
checked where no family of the block exists yet, so it names none. Its
constructors are checked with every family's provisional head, see no
constructor, and return their own family at its own parameters (uniformity);
the families need not share parameters. Each family is checked against its own
declared universe: its fields' kinds and levels (L1), its arguments (L2) and
their sizes ([family argument size](#family-argument-size)) are its own, and a
sibling's field is read by the sibling's declared universe at its arguments,
so a copyable family holds no field of a linear sibling, while a linear one may
hold a copyable sibling. Strict positivity is in every family of the block: an
occurrence of a sibling is positive where one of the family itself would be,
and no family of the block occurs in the arguments of one. A field is
recursive when it mentions any family of the block, which decides each
family's list shape and structure eta. Each family has its own constructors,
which its matches cover.

A family's *positive arguments*, those that may hold a nested occurrence of a
family declared later, are the greatest fixed point over its block: an argument
is positive when its header allows it and it occurs positively in every
constructor's fields, each family of the block read by the assignment being
computed. A single family is a block of one. Reading the block's own
occurrences as positive in every argument would accept `F (A)(B)` with fields
`(a: A) -> Nat` and `F(B, A)` as positive in `B`, which reaches the negative
position of `A`, and so a negative `H` through `F(Nat, H)`.

**Definitions.** Each member is a function definition with a `decreases`
clause and a term body; none is an instance or a builtin. A recursive
definition, a member or a single one with `decreases`, is a function, since its
calls are where its decrease is checked and its peers bound: one whose header
has no parameters, such as `def f : (n: Nat) -> Nat decreases measure(1) := t`,
takes those of its declared function type, unnamed, and its body is `t` applied
to them. Its type is checked first, where no member exists yet, so it names
none. Then each body is checked
with every member bound, after its parameters, to the raw call from it to that
member, which only an application head may name. A call decreases when the
callee's metric at its arguments is lexicographically smaller than the
caller's at its own arguments, read through the caller's branch refinement;
a single recursive definition's calls are checked the same way. Each
component compares by the order of the caller's value: a proof by the field
order ([recursion on proofs](#recursion-on-proofs)), a Nat, measure or
parameter alike, by `<`, and other data by the structural subterm order. A
Nat candidate is smaller when the caller's value minus it is at least 1 on
the normal forms, as `Nat.ble` decides
([natural number normal forms](#natural-number-normal-forms)), and the
comparison moves on past a component that is equal or, on Nat, at most the
caller's. So all members' metrics have one length. `structural(x)` is one
component, the parameter `x`, and `measure(e)` is one, a measure. A
`lexicographic` clause lists its components, each a parameter or a measure,
written `measure(e)`: `lexicographic(n, measure(Nat.add(a, b)))`. A measure
component follows a `measure` clause's rules: it lives in `Type`/`Sort(u)`, is
evaluated again at each call's arguments, and only reads them (L6). Every
component compares by one well-founded order on all values, whatever it comes
from: `<` on Nat contains the structural order on Nat, and no value of another
type is below a Nat, so a chain that reaches a Nat descends by `<` from there.
What the forms decide holds for every value of their atoms, so at run time,
and every chain of calls through the block descends, by the lexicographic
product of that order.

A constant measure is a *rank*. It writes a cycle whose metric decreases only
over a round trip: each member gets its rank as a last component, so that a
call which keeps the earlier components goes to a lower rank.

```text
mutual {
  def f (n: Nat)(h: P(n)) : True decreases lexicographic(h, measure(0)) := {
    match h returning True with
    | P.z => True.intro
    | P.s m h2 => g(m, h2)
  }

  def g (n: Nat)(h: P(n)) : True decreases lexicographic(h, measure(1)) := f(n, h)
}
```

`f`'s call passes a proof field of `h`; `g`'s passes `h` back unchanged, from
rank 1 to rank 0. Without the ranks, `g`'s call would not decrease.

Once checked, the members are published together, each
closed over the published block, where a running member finds each peer by its
name.

A call to a member is an application, so the ledger and the read rules are
those of any lambda: it uses its linear arguments once, or only reads them in
a read extent, where its linear inputs keep separation. Mutual families and
definitions follow L1 to L9 as single ones do.

## Evaluation

Checking is evaluation: the checker computes each checked term's value with the
evaluator, and that value's type is the term's type. Evaluation is strict: an
application evaluates its head and then its arguments to values, a block its
lets and then its result, and a match its scrutinee before choosing a branch.
The same evaluator runs a program's body once it has checked.

A branch's refinement solves variables, and the checker reads values through it
by materializing them: substituting the solutions and resuming the
computations they blocked. Materialization is a function of the value and the
solutions, so one materialization rebuilds each value and environment it
meets, by identity, once: a graph whose parts are shared, such as a tree whose
two children are one value, is rebuilt in time linear in its distinct parts,
and stays shared.

### Proof calls

A call to a checked lambda whose function type is a proposition (F2) is a
*proof call*. Applying the lambda does not run it, except inside a demanded
proof: the call's value is a suspension of the lambda and its argument values.
The suspension runs the lambda the first time something reads the proof's form,
and keeps the result, its *forced value*. Conversion never reads a proof's form,
since proof irrelevance decides first, so only these force one:

- a match on it or a projection of its field, which is a match, during checking
  and at run time, and the checker's view of a match's scrutinee as a known
  constructor, under which the other cases are `UnreachableCase`;
- applying it, as a proof of a function proposition;
- its key, which the termination checker compares (see [recursion on
  proofs](#recursion-on-proofs)), and conversion when two proofs' propositions
  do not convert;
- quotation, for an inferred motive or a `derive` result, and printing, of the
  program's result or a diagnostic;
- the walks that read a value's form: positivity, the axiom lint S3, and
  reading a type-pattern capture by position.

A demanded proof runs as every call ran before: a proof call inside it runs at
once, so demanding a proof costs what evaluating it eagerly cost. A proof
nothing demands never runs, so an exponential proof that nothing inspects costs
nothing. Materialization keeps a suspension suspended, over the materialized
lambda and arguments; a forced one keeps its forced value, materialized.

A suspension's proposition is the lambda's codomain at its arguments, computed
when first read, without running the body. Evaluation used to take the forced
value's own type instead. The two convert, since the body checked against the
codomain, and as normal forms they are the same outside the proofs and
functions inside them. Every reader of a proof's type reads it by conversion or
by its universe, or forces the proof first; a proof whose codomain does not fit
an expected type is tried at its forced value's type, so a mismatch reports
that type, as before.

A suspension's dependencies are the lambda's and the arguments', computed
without running it. Evaluation introduces no free variable, so they include its
forced value's, but may include more: a variable that only the arguments
mention. Such a variable occurs in no rigid position of the forced value or its
type, so unification never reaches it, and a refinable set that includes it
refines nothing more. The decisions that a dependency makes conservative
confirm it through forced values instead: the occurs check, positivity, a
record's eta eligibility, and instance search's test of a solved argument. A
link whose value mentions its variable only in a proof call's arguments holds
that value with those calls forced, as it did before.

**Why the results do not change.** A forced value is the value eager
evaluation computed: evaluation is deterministic, the arguments are values, and
the lambda reads only its closure and its arguments; a global it names was
checked where the name was checked, never where it runs. Every reader of a
proof's form forces it, and the other readers read a proof by its proposition,
which converts with the one before. In particular:

- **The ledger and the read rules** (S1) decide from the checker's view, not
  from evaluation: a checked node's summary of uses is built from its syntax as
  it is checked, and its role, a type or proof, a linear value or an ordinary
  one, from its value's universe, which is `Prop` for a proof call as for its
  forced value.
- **Protocol primitives and ghosts.** The primitives are natives, which never
  suspend, and their reductions are functions of their arguments, R1 of the
  supply's index, so a proof that applies one gives the same ghosts whenever it
  runs; checking never allocates either way. Quotation forces a proof before it
  refuses a ghost in it.
- **`--no-user-axioms`** rejects a program's axioms from its declarations,
  before anything is evaluated.
- **Running a program** forces its result, and printing forces the proof calls
  inside it, so a program prints what it printed before; a running program
  reads a proof only where the list above forces it. A run that fails while
  the result prints fails the program, as it did when the body ran it. A
  diagnostic is printed outside every evaluation boundary, so there a call
  whose run fails, by an error or by exhausting the stack, prints as the call.
- **A recursive call's check** inside a local lambda in a recursive body ran
  again whenever eager evaluation applied the lambda during checking; it ran
  first when the lambda's body was checked, on its parameters, and the subterm
  order holds after substitution.

Skipping an undemanded proof also skips what it would have exhausted: time,
host stack, and `NatValueTooLarge` for a closed power too large for the JVM. A
program that only such a proof made fail may now check. Evaluating a checked
term raises no other error.

### Evaluation depth

Evaluation takes no host stack for a term in tail position, whose value is the
value of the term being evaluated: a block's result after its lets, a match's
chosen branch, and a core lambda's body where the lambda is applied, after the
application's arguments. The evaluator continues with that term in a loop
instead of recursing into it. The loop changes no value, neutral or blocking
set, and an error is located at the innermost term being evaluated, as before:
it removes host frames only, so evaluation that exhausted the stack may now
finish. A native's result, a constructor's or a neutral head's application,
and a proof call are values at once; a demanded proof call runs its body in a
loop of its own.

Recursion outside tail position, and checking, recurse on the host stack. The
CLI runs its whole pipeline on a thread whose stack `--stack` sets, 256 MB
unless it is given. A stack overflow is caught only at the boundary of a
declaration, the prelude's included, or of the program's body, and becomes
`EvaluationTooDeep`, located at the whole declaration or body; no rule inside
them observes one. The body's boundary covers checking and evaluating it,
applying an entry to the root supply, and printing the result, which forces the
proof calls in it. A demanded proof call runs where it is demanded, so its
depth adds to its demander's. A proof call whose argument holds another call,
directly or through data, recurses into it to compute its dependencies, and
into its run where its body matches on it, where eager evaluation had run the
inner call already: a chain of such calls, built by a loop, needs stack in
proportion to its length. An overflow while loading, parsing or elaborating
is not a diagnostic.

## Axioms

Any module may declare an `axiom`. Its type is checked; its consistency is the
author's responsibility. The prelude's axioms are the trusted bootstrap; the
bundled prelude declares none. Axioms declared by the program or the modules it
imports are user axioms: `Interpreter.axioms` lists them, in declaration order,
from the program's own declarations, since the loader merges every loaded module
into the program while the prelude's declarations stay in `Prelude.Config.core`.

A `:= builtin` declaration is trusted further than an axiom: its native's
behaviour is taken to match its declared type, which is not checked. Only the
kernel and the prelude declare builtins. `Interpreter.run` rejects one declared
by the program, or a module it imports, as `ProgramBuiltin` at its `builtin`,
before evaluating any declaration, whatever the axiom policy. The bundled
prelude's builtins are `Level.succ`, `Level.max`, and `Nat.expand_eq`, whose
value is its own application, a proof that holds because the kernel's expansion
preserves value. A custom prelude given with `--prelude` is trusted as the
bundled one is, builtins and axioms included; the CLI lists its axioms on
standard error.

The CLI reports user axioms on standard error. With `--no-user-axioms`,
`Interpreter.run` rejects the first one as `UserAxiom` at its declaration
before evaluating any declaration. A theorem checked under that flag depends on
the kernel, the prelude, and nothing the program assumed. The default stays
permissive.

## Resource protocols

The kernel declares the mathematics of resource protocols, beneath every
prelude: `List.Perm`, the permutation relation; `Protocol.Proto`, a record of an
atom type `Atom` and a step relation `Step` from consumed to produced atoms;
`Protocol.Reach`, the configurations reachable from an initial inventory by
framed steps and permutation; and `Protocol.Valid`, the configurations that are
part of a reachable one. They are ordinary checked inductives. The kernel owns
them because the protocol primitives' types name them, so a prelude must not be
able to redefine them. The design and its rationale are recorded in
[linear protocols](implemented/LINEAR_PROTOCOLS.md).

It declares the types of protocol instances and their tokens in the same way.
Each takes a protocol `P: Proto` and an initial inventory `init: List(P.Atom)`,
as `Reach(P, init, C)` and `Valid(P, init, C)` do:

- `Protocol.Supply : Lin(Level.zero)`, from which instances are allocated;
- `Protocol.Inst(P, init) : Type`, the identities of instances;
- `Protocol.Tok(P, init, s, a) : Lin(Level.zero)`, a token of the atom `a` held
  by the instance `s`;
- `Protocol.Toks(P, init, s)`, indexed by a list of atoms `C`: a packet of
  tokens of `s`, `nil`, or `cons(a, t, C, rest)` with `t` a token of `a`;
- `Protocol.Observed(P, init, s, C)`, whose `mk(toks, valid)` holds a packet and
  a proof of `Valid(P, init, C)`;
- `Protocol.Fresh(P, init)`, whose `mk(next, s, toks)` holds the next supply, an
  identity and its packet of `init`.

A concrete protocol is `Proto.mk(Atom, Step)`, and by structure eta a variable
`P` converts with `Proto.mk(P.Atom, P.Step)`.

`Supply`, `Inst` and `Tok` are opaque builtins: each is a symbol of its declared
type, as an axiom is, with no constructors and no reduction. An application of
one is a stuck symbol application. It converts with another only when their
arguments convert, and unification derives nothing from it, neither
injectivity nor apartness: an equation between `Inst(P, x)` and `Inst(P, y)`
refines neither `x` nor `y`. So tokens of different
identities have different types. The symbols are not inductive families, so a
`match` on a token or a supply is `NonInductiveMatch`, even with no cases, and
no constructor of them exists: `Protocol.Tok.mk` is a selection from a function,
`NotAType`, and as a case it is `NotFound`. Outside an absurd branch, tokens
come only from the primitives below, and a term holds only the tokens it is
given or obtains from them, alone or in packets.

`Toks`, `Observed` and `Fresh` are linear inductive families, checked by the
ordinary rules (see [linear types](#linear-types)). `Observed` and `Fresh` are
records, so they have projections and structure eta: `o.valid` reads `o`, and
`o.toks` consumes it. `Toks` has an index, so a packet is
a constructor value, never a packed word. The [family argument size
check](#family-argument-size) charges a `Proto` by its fields, an atom type and
a relation into `Prop`, which cost nothing, so the three families are in
`Lin(Level.zero)`, with `Tok` and `Supply`.
Identities are ordinary data in `Type`: they can be stored in lists and in
unrestricted families, returned, and packaged in a linear family together with
a packet of their own, whose type mentions the earlier identity field (L3).

The families and primitives once took the atom type and step relation as two
parameters, because positivity rejected the stuck projection `List(P.Atom)` in
a field type, structure eta was missing, and the size rule charged a `Proto`
its whole `Sort(Level.one)`. Declaration-time positivity, structure eta and the
refined size rule removed all three.

A packet function whose packet is at a variable index recurses structurally
on the packet, `decreases structural(left)` for `left: Toks(P, init, s, A)`:
matching the packet refines its index and links the packet to its constructor
(see [refinement outcomes](#refinement-outcomes)). One whose packet is at a
computed index, such as `List.append(A, B)`, recurses on the unrestricted list
that the index is computed from, matching the packet in each branch, where that
list's constructor makes the index known.

The kernel evaluates in two stages. `Kernel.coreEnv` holds `Sort`, `Lin`,
`Bool`, `Nat`, `List`, `Char` and `String` with their natives; `Kernel.env` evaluates
the protocol declarations over it. The core natives and their accessors read
the core stage. A protocol declaration's type calls `List.append`, whose stuck
result names the native through those accessors, so a single stage would
re-enter its own initialization. The primitives' natives read the protocol
families and constructors from `Kernel.env`; no kernel declaration applies a
primitive, so evaluating it never runs one. The elaborator resolves both stages
as one namespace.

### Primitives

The kernel declares three primitives, each taking a protocol and an initial
inventory:

```text
new (P)(init)(sup: Supply): Fresh(P, init)
step (P)(init)(s: Inst(P, init))(A B: List(P.Atom))(h: P.Step(A, B))
    (toks: Toks(P, init, s, A)): Toks(P, init, s, B)
observe (P)(init)(s: Inst(P, init))(C: List(P.Atom))
    (toks: Toks(P, init, s, C)): Observed(P, init, s, C)
```

`new` allocates an instance from a supply and returns the next supply, the new
identity and a token of each atom of `init`. `step` consumes a packet of the
atoms a rule consumes and returns a packet of the atoms it produces, with no
inputs when the rule consumes none. `observe` returns a packet with a proof
that it is part of a reachable configuration; that proof is the one fact the
primitives reflect, and it holds jointly only for tokens observed together.
Use is affine, so a program drops a supply or a token it no longer needs.

They are natives with these reductions, where `canon(s, [])` is `Toks.nil` and
`canon(s, a :: C)` is `Toks.cons(a, tok#(P, init, s, a), C, canon(s, C))`:

```text
R1  new(P, init, supply#(n))          ⇒  Fresh.mk(supply#(n+1), i, canon(i, init)),  i = inst#(P, init, n)
R2  step(P, init, s, A, B, h, t)      ⇒  canon(s, B)
R3  observe(P, init, s, C, t)         ⇒  Observed.mk(t, valid#(P, init, C))
```

R1 fires on a canonical supply and a known `init`, and R2 on a known `B`. A
known list is `nil` or a chain of conses ending in `nil`, whatever its elements.
Otherwise the application is stuck, blocked on the supply's and the list's
reduction blockers, and resumes when one is solved, as a stuck `List.append`
does. R3 always fires. R2 and R3 ignore the contents of their input
packet: tokens carry no data.

`supply#`, `inst#`, `tok#` and `valid#` are ghosts, constants of their own kind
built only by these natives. No environment binds them, and their names are no
identifiers, so no source term names one, and quotation refuses them, so no
inferred motive or `derive` result holds one. Each ghost application carries
its precise type, and in its arguments everything that type depends on, since
keys ignore types. Ghosts convert by congruence only, so identities of one run
are distinct, tokens of distinct identities have distinct types, and `valid#`
converts with every proof of its proposition.

A program body of type `(sup: Protocol.Supply) -> R` is an **entry**. It checks
as any body does; `R` must be unrestricted (`LinearGlobal`, decided from the
body's type before anything runs). `Interpreter.run` then applies its value to
the root supply `supply#(0)` and returns the result, which the CLI prints. A
body of any other type is the program's result, as before. Only the entry
module has a body, no global is linear (S2), and protocol programs run with
`--no-user-axioms`, so a run has one root supply, and a body of type
`Supply -> Fresh(…)` cannot leak one.

Checking never allocates. The root supply exists only once the entry has
checked, and only R1 makes another, so during checking every supply is a
variable or stuck and R1 never fires: an entry's result that depends on its
initial packet is stuck while it checks and computed by `run`. R2 and R3 do
fire during checking. A type or proof may contain
a primitive application, since a read extent may compute with live linear
values (S1), and then converts by these reductions. That is sound because a
read consumes nothing and its value is a type or a proof, which no linear
binder receives, and because each call in it takes linear inputs from disjoint
regions of locals that were live together. So an `observe` in a type or proof
reads a packet the program could observe at that point, as in the model's
hypothetical run, and the `valid#` it returns holds; `observe(join(t, t))` is
refused. R2 fires only on a known output list, whose index already excludes
every branch its canonical packet excludes.

### The protocol library

`lib/Protocol` is untrusted library code over these declarations, loaded with `--root lib`. Its theorems
are ordinary checked definitions; like every protocol theorem, they are trustworthy under `--no-user-axioms`.

- **Prelude support.** Packets travel in the kernel's `List` and the prelude's `Prod`, which are kind-polymorphic,
  with `Fact(p)`, a proof as copyable data, so that a fact travels in a `Prod` beside the tokens it is about, and
  `Eq.subst` transports a linear value, such as a packet along an equation of its atom lists. A `Prod` projection
  consumes a pair of packets and drops the other one (L5), so the library destructures them.
- **Protocols.** The laws take a protocol `P: Proto`, as the kernel families do; `Protocol.Rel(Atom)` abbreviates a step
  relation's type, and a concrete protocol is `Proto.mk(Atom, Step)`.
- **Packets** recurse structurally on the packet at a variable index, and otherwise on the unrestricted list their
  index is computed from, matching the packet in each branch (see above).
  A `List.Perm` proof cannot be eliminated into a linear result, so packets reorder by `exchange` and `swap`, each with
  the permutation lemma that carries validity along.
- **Name resolution.** Members of the enclosing namespaces resolve before opened aliases (see
  [namespaces](namespaces.md)). The building blocks `Exclusive` and `Shares` are top-level namespaces that open the
  kernel's `Reach` and `Valid`.

## Linear types

`Kind`, `Univ`, `Sort` and `Lin` are kernel declarations beneath every prelude
and program, and cannot be redeclared. A type is **linear** when its kind is not
provably `copy`, and a value is linear when its type is. Types, universes,
proofs and function values are never linear. A type determines its universe,
so linearity is read off the type at hand, never off a family's fields.

### Kinds and universes

- **K1 Kinds.** `Kind` is a kernel sort like `Level`. Its values are
  `Kind.copy` and `Kind.lin`, variables bound by captures, and
  `Kind.join(a, b)`. A kind's normal form is `Kind.lin`, or a finite set of
  variables, the empty set being `Kind.copy`: joins with `copy` vanish, a join
  with `lin` is `lin`, and `join` is associative, commutative and idempotent.
  So `copy < lin`, with the variables between them, ordered by inclusion. A
  kind that is one variable converts with that variable.
- **U1 Universes.** A universe is `Univ(k, l) : Sort(Level.succ(l))`, whose
  types are of kind `k`. `Sort(l)` and `Lin(l)` are names for
  `Univ(Kind.copy, l)` and `Univ(Kind.lin, l)`, and `Prop` stays outside `Univ`.
  A type is linear when its kind is `lin`, or a normal form that holds a
  variable.
- **U2 No cumulativity.** Universes are not cumulative, for levels or for
  kinds: a value is checked against an expected type by conversion, so a type
  is used at exactly its universe. `Nat` is no `Lin(Level.zero)` and no
  `Sort(Level.one)`, and `Nat -> Type` is not `Nat -> Lin(Level.zero)`. A
  function that takes types of every level is universe-polymorphic,
  `(A: Sort($u))`; one that takes copyable and linear values alike is
  kind-polymorphic, `(A: Univ($k, $u))`. Only family formation (L1) and the
  nominal size rule still order universes, and neither relates values.
- **U3 Captures.** `Univ($k, $u)` binds a kind and a level variable, as
  `Sort($u)` binds a level; `Sort($u)` and `Lin($u)` fix the kind. A level
  capture opens on a universe of any kind, and the binder's type then fixes
  the kind: `List(Protocol.Supply)` is a list of supplies, but
  `Eq(Protocol.Supply, a, b)` is `TypeMismatch`. A capture nested in a
  pattern has its parameter's type, so `$A` in `List($A)` is of any kind; a
  constraint fixes it, as in `List($A in Sort($u))`, whose element type must
  be copyable at every use. A capture under a head that computes is checked
  against the head's parameter ([type patterns](#type-patterns)), so `$A` in
  `SList($A)`, for an alias `SList (A: Sort($u)) := List(A)`, is copyable.
- **U4 Kind-polymorphic code** treats values of a variable kind `k` as affine,
  as Rust's generic code treats a `T` without a `Copy` bound: they are tracked
  and used at most once. A caller instantiates `k := copy` and passes copyable
  values freely. There is no case analysis on kinds; code that copies elements,
  such as the prelude's `List.filter`, constrains them to `Sort`.

### Linear and kind-polymorphic families

A family declared in `Lin(u)`, or in a `Univ(k, u)` whose kind is an
expression over its parameters' kind variables, is an ordinary inductive
family: positivity, uniformity, refinement, coverage and packed list storage
are unchanged. The kernel's `List (A: Univ($k, $u)) : Univ(k, u)` is one, and
so are the prelude's `Prod`, `Option`, `Sum`, `Sigma` and `Subtype`: `List(Nat)`
is copyable and `List(Protocol.Supply)` is linear.

- **L1 Fields.** A field's kind is at most its family's in the kind lattice:
  the family is `lin`, or the field kind's variables are among the family
  kind's. A field's level is at most the family's, and a proof field is always
  allowed. So a `Sort` or `Prop` family has no field of linear or variable kind
  (`LinearFieldInUnrestrictedFamily`), and `Prod(A, B)` is in
  `Univ(Kind.join(k1, k2), …)`. This is family formation, not subtyping of
  values.
- **L2 Parameters and indices** have unrestricted types
  (`LinearFamilyArgument`), in every family: a parameter `A: Univ($k, $u)` is a
  type, and an index is of kind `copy`. Erased constructor binders and capture
  witnesses name parameters, so they are unrestricted too. The nominal size
  rule is unchanged, and kinds cost nothing.
- **L3 Dependency.** A field type, a later binder type and the constructor's
  result are read extents of the constructor's telescope (S1), so they may read
  earlier fields, linear ones included.
- **L4 Matching** consumes the scrutinee. A pattern field whose type, read after
  the branch's refinement, is linear is tracked, and a `_` for one drops it;
  a match that is itself a read extent only reads its fields. The motive is a
  read extent, so it may read the scrutinee:
  `match xs returning Tag(count(xs))`. The root is still refined, for
  termination checking.
- **L5 Projections.** A projection is the one-branch match that returns its
  field ([projections](#structure-eta-and-projections)), so the ledger and the
  read rules decide it as they decide that match. A projection of a linear
  record that returns data consumes the record and drops its other fields, so
  two projections of one record are `LinearReused`; destructuring with
  `let (…) := p` keeps every field. A field's type that mentions an earlier
  field holds that field's projection, a read of the record, and a projection
  that returns a proof or a type is a read extent: it reads the record and does
  not consume it. In a read extent a projection is the field's region of its
  record.
- **L6 Recursion** may decrease through linear data. A parameter component of
  a metric only names a parameter and is not a use; a measure, a clause or a
  component, is evaluated again at every call without consuming anything, so it
  is a read extent of its own.
- **L7 Binders.** Instance binders and `let instance` have unrestricted types
  (`LinearInstance`), since instance search copies instances. A type-pattern
  capture of linear type, such as a capture of a linear parameter of a
  pattern's head, is `LinearInType`: it would bind an untracked linear local that
  a term could consume. So every local of linear type is tracked.
- **L8** `Eq` has no linear carrier: its carrier is `Sort($u)`, so a carrier of
  linear or variable kind is `TypeMismatch`. A linear value moves along an
  equation of unrestricted data, such as its index, with the prelude's
  `Eq.subst`, whose motive is into `Univ(k, v)` for a kind `k` it takes. An
  equation between linear types, `Eq(Lin(u), A, B)`, is an equation of types,
  whose `A` and `B` are linear.
- **L9 Recursion** in a linear family follows ordinary strict positivity, as in
  an unrestricted one: a recursive occurrence may be nested in another family's
  arguments (`kids: List(Tree)`), sit under a binder (`f: Nat -> Tree`), or be
  at other parameters. A linear family may store copyable functions, including
  ones into or out of linear types.

### Function types

- **F1** A function type whose codomain is in a `Univ` is classified `Sort` of
  the maximum of its levels, whatever the kinds of its domains and codomain:
  `Univ(k, v)` domains and codomains contribute `v`, propositions nothing.
  Every function value is unrestricted, so a function type has no closure
  flag. When the codomain's level depends on a `Level` or `Kind` binder, as in
  `(u: Level) -> Sort(u)`, that maximum mentions the binder's variable, out of
  scope above the function type. The classifier is sound but inert: the
  variable converts with no concrete level, so the type is never a value of a
  universe, only the declared type of a global, and so cannot be fixed to a
  level and passed where an ordinary type is expected.
- **F2** A function type whose codomain is a proposition is `Prop`, whatever
  its domains. Its body is a read extent over its linear parameters, which are
  only read, and applying it is a proof, whose linear arguments are only read.
- **F3** A codomain or later binder type is a read extent, so it may read
  earlier linear binders: `(xs: List(A)) -> Tag(count(xs))`.
- **F4** A parameter of linear type, tracked from its binder's type, is used
  at most once in the lambda's body, or only read when the body is a read
  extent.
- **F5 No linear captures.** A lambda references no linear local bound outside
  it, in its body or its type, read or not (`LinearCapture`, at the reference),
  including a lambda inside a type ([lambdas in types](#lambdas-in-types)).
  A read would run when the function is applied, where nothing ties the captured
  local's liveness to the arguments'. A callback that should own a linear value
  takes it as an argument.

### The ledger

A tracked local is one whose type at its binder is linear: a lambda or
definition parameter, a `let`, including `let _` and the root a let pattern
saves, or a match field, named or `_`. Tracking is decided once, when the local
is bound, and refinement never changes it. Its extent is the lambda body, the
later lets and the block's result, or the branch. Binding a refined local
afresh is intended: where refinement has given `x : A` the type `Nat`,
`let y := x` uses `x` once and binds an untracked `y`, exactly as
`let y := id(x)` would.

A tracked local is used at most once on every path through its extent, and may
be dropped: use is affine. Soundness needs only that nothing is duplicated, and
forgetting a token keeps the protocol invariant. A path takes one branch at each
match. An application evaluates its head and then its arguments, a block its
lets and then its result, and a match its scrutinee on every path through it. A
use after an empty match counts too, although no run reaches it. Lambdas are
never uses (F5), and neither is anything inside a read extent (S1): reading
consumes nothing. A second use on some path is `LinearReused`, at that use. A
binder whose extent is a read extent, such as a parameter of a function
returning a proposition, a `let` in a proof, or a field of a match that returns
a type, is only read, as often as its extent likes.

Every checked node carries a summary of its uses, combined bottom-up as it is
checked, which a tracked binder tests when its extent is done. A node that is a
read extent keeps none of its parts' uses. Programs without tracked locals
carry the empty summary, and evaluation makes none of these checks.

### Separation from types and proofs

- **S1 Reads.** A *read extent* is a maximal checked term whose value is a type
  or a proof: a binder type, a codomain, a let annotation, a motive, a field or
  constructor result type, an explicit type argument, a proof argument, a
  proof's body, and a `measure` term. A read extent may contain linear-typed
  subterms: tracked locals, linear computations over them, observations, and
  closed resource computations such as `observe(Toks.nil)` or a `step` from
  `Toks.nil`. Its uses do not count toward the enclosing extent's ledger, and
  it may drop linear values it creates itself. In the model (formalization
  `DESIGN.md` §6, R1–R5), a read extent formed where linear locals are live is a
  hypothetical run from the current ledger: it changes nothing, and its
  admissibility persists after the locals are consumed.

  Inside a read extent, every linear-typed term has a *provenance*: the
  *regions* it is built from. A region is a *root*, a tracked local with no
  defining value of its own (a parameter, or a binder of a Π type or a
  constructor), with a path of field indices into it. Two regions overlap when
  one path is a prefix of the other, so a value overlaps each of its parts.
  - A root `xs` is the region `(xs, [])`.
  - A `let` is never a root: it aliases its value's provenance, so after
    `let a := t; let b := t` both `a` and `b` are `(t, [])`.
  - A match field `i` of a scrutinee that is exactly one region `(r, p)` (a
    root, a field, or a `let` of one) is `(r, p ++ [i])`. So sibling fields
    are separate, the same field taken by two matches of one value overlaps,
    and a field overlaps its scrutinee. A field of any other scrutinee, such as
    a constructor application, gets the scrutinee's whole provenance, since it
    may be any part of it.
  - A linear-typed result of an application or a constructor has the union of
    its linear inputs' regions, so `lid(xs)` and `append(xs, ys)` carry their
    sources forward; a match's linear result is its branches'.
  - An unrestricted value or a proof has none, since plain data copies freely,
    and so has a closed computation with no linear input, which any read may
    recompute (R5).

  A match inside a read extent only inspects its scrutinee, as in the model, so
  it is no call. Two rules hold at every call, an application or a constructor
  application, of its linear inputs:

  - **Separation.** Their provenances are pairwise disjoint
    (`LinearReusedInType`, at the input that repeats one). So
    `count(append(xs, xs))`, `count(append(lid(xs), lid(xs)))`,
    `pairCount(xs, xs)` and `observe(join(t, t))` are refused, while
    `Eq(Nat, count(xs), count(xs))` and `Nat.add(count(xs), count(xs))` are
    accepted: each `count` gets `xs` once, and `Nat.add` and `Eq` get
    unrestricted values.
  - **Joint liveness** (R7). The roots of their union were all live at one
    point on the path (`LinearNotJointlyLive`). Every root records the roots
    consumed on the path before it was bound, by the lets, earlier arguments
    and scrutinees that precede it; the union is jointly live when none of its
    roots was consumed before its latest-bound root was bound. A value built
    from the roots since, through lets and fields, is recomputed from that
    point, so only roots are tested. A single root is always fine, consumed or
    not, since its admissibility persists. The arguments of one application see
    the locals live at its start, so `g(xs, lemma(xs))` is accepted. A packet
    combined with its successor aliases it, so it overlaps; joint liveness
    refuses a type whose binder was bound after a root it reads was consumed.

  A call outside every read extent that breaks either rule also uses a local
  twice, which the ledger reports as `LinearReused`; so each node passes its
  first violation up, and the nearest enclosing read extent reports it.

  **Why this keeps parametricity.** A function with several linear parameters
  is a contract that its inputs are separate: its body may join them and
  observe the result. A caller must honour the contract whatever the body does,
  as Rust refuses `f(&mut x, &mut x)` and separation logic's `P ∗ Q` requires
  disjoint resources. So `pairCount(xs, xs)` is refused although
  `Nat.add(count(xs), count(xs))`, equal to it, is accepted: the decision reads
  the callee's type, never its body.

  **Kept conservative**, each for a significant simplification:
  - A `let` or a field inside a read extent whose own block or match returns
    data, not a type or a proof, is used at most once, as in a term: knowing at
    the binder that an enclosing node is a read extent would need either that
    node's role before its arguments are checked, or deferring reuse errors to
    every entry point where a term is known to run.
  - A match's linear result unions the provenances of all its branches, so a
    later call over it tests regions that no single path combines.
  - A field of a scrutinee that is not exactly one region, and a call's result,
    get whole provenances, not paths: so the fields of a constructed value, or
    projections of a call's result, overlap one another.
  - F5 covers reads, as above.
  - Quotation still refuses linear values and never names a tracked local, so
    an inferred motive that would need one is `MissingReturningClause`, an
    elaboration limit: state the motive with `returning`. A type the checker
    computes, rather than checks, may hold a linear local inside a stuck
    computation, such as the type `Tag(count(xs))` of a let bound to
    `Tag.mk(count(xs))`; it is never quoted.
- **S2 Globals.** A definition or the program result of linear type is
  `LinearGlobal`, decided for a definition from its declared type before its
  body is checked: every reference to a global would copy it, and nothing
  consumes the result.
- **S3 Axioms**, a lint. An axiom is `LinearAxiom` when a linear type occurs
  anywhere in its evaluated type: as the type itself, as a binder type or
  codomain of a function type at any depth, or anywhere in an argument of an
  application, such as `Box(Nat -> Tok)`, `List(Nat -> Tok)` or a family applied
  to a function returning a linear type, whose body is opened on fresh
  arguments. `axiom T : Lin(Level.zero)` declares a type, not a linear value, and
  is allowed, as are data axioms such as `axiom magicNat : Nat`. Three forms are
  not seen: a stuck computed type, such as `axiom mint (b: Bool) : F(b)` where
  `F(Bool.true)` computes to `Nat -> Tok`; a type variable a use instantiates,
  such as `axiom pick (A: Type) : A` at `A := Nat -> Tok`; and the field types of
  a family the type names without linear arguments, such as `axiom m : Mint`
  for `inductive Mint : Type | mk (f: Nat -> Tok)`. S3 therefore does not make user
  axioms safe: protocol soundness assumes `--no-user-axioms` (see
  [axioms](#axioms)), which protocol theorems already require.

