# Kernel rules

## Natural number normal forms

`Bool`, `Nat`, their constructors, and the native `Nat.add`, `Nat.mul`,
`Nat.pow`, `Nat.sub`, `Nat.pred`, `Nat.isZero`, `Nat.beq`, and `Nat.ble` are
kernel declarations present beneath every prelude and program; they cannot be
redeclared. Ordinary source functions acquire no arithmetic laws merely from
their names.

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
split. The prelude axiom `Nat.mul_add` states distributivity, and every other
semiring identity follows from it and conversion; the prelude theorems
`Nat.mul_pow` and `Nat.pow_mul` state `(x * y)^a = x^a * y^a` and
`(x^a)^b = x^(a * b)`. Normalization needs no limits; a closed power too large
for the JVM to represent raises `NatValueTooLarge`.

Each Nat value has one representation: zero is the `Nat.zero` constructor, a
lone neutral atom is itself, and everything else, including every successor, is
a compact form; constructing `Nat.succ(x)` yields the form `x + 1`. The
constructor view exposes a form with a positive constant as `Nat.succ` with
that constant decremented. A form with zero constant, including a product of
successors or a symbolic power, blocks on all its dependencies. Substitution
recomputes affected arithmetic, including symbolic exponents and bases, and
blocked matches. Atom equality respects existing definitional
conversion, including when convertible atoms have different structural keys.

Truncated subtraction and the comparisons depend only on the signed difference
of their arguments: they cancel common whole terms and decide when one
remaining part is zero or the other has a known successor, and otherwise stay
stuck on the canonical parts. A sum inside a factor is opaque to cancellation.
They satisfy the recursive equations, such as
`sub(a, succ(b)) = pred(sub(a, b))`. A stuck subtraction absorbs only a known
constant subtrahend, so every result is stable under substitution.

Unequal symbolic forms do not establish contradiction. Refinement keeps
whole-variable linking and successor cancellation, and otherwise leaves
arithmetic equations stuck. Structural termination peels known successors;
monomials, factors, and summands are not structural subterms. Positivity treats
factor bases and symbolic exponents, including sums, as arguments of the Nat
operations, so a target occurring in one is never positive. The [Nat normal forms design](nat-normal-forms.md)
specifies the laws, the representation, and quotation.

## Function-type equality

Function types compare binder domains and constrained-capture classifiers by
exact definitional equality. Universe cumulativity is available when checking
ordinary arguments, but does not identify function domains such as `Type` and
`Sort(Level.one)`.

Corresponding binders must have the same instance markers and capture
operations: capture roots, projection paths, and level subtraction offsets.
Names may differ. After opening one telescope on fresh arguments, the checker
instantiates the other with those same arguments using exact checking, then
compares their codomains. Requiring matching capture operations is conservative;
in particular, `Sort($u)` and `Sort(Level.succ($v))` admit different domains and
cannot be equated by successfully matching an argument in just one direction.

## Nominal Type families

Fully applied, Type-valued inductive families obey these nominal principles:

- **N1 — injectivity:** equality of instances of the same declaration forces
  equality of their complete dependent argument tuples.
- **N2 — distinct declarations:** instances of different family declarations
  are distinct types, even when their constructors have the same shape.
- **N3 — distinct forms:** family instances, Type-valued function types, and
  Type universes are pairwise distinct forms.

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

After structural comparison and variable refinement, an exhaustive classifier
identifies data constructor values, fully applied Type-family instances,
Type-valued function types, and Type universes as rigid forms. Different
remaining rigid forms produce `Contradiction`; two function types remain `Stuck`.

Unrefinable variables, opaque symbols and applications, blocked matches,
function values, and partially applied family or constructor heads provide no
rigid-form contradiction. Neither do propositions, unresolved level equations,
or primitive forms without a nominal apartness rule. These cases remain
`Stuck`. Adding a value form requires an explicit classification.

### Family argument size

A Type family declared in `Sort(n)` must have sufficiently small parameters and
indices for its nominal argument labels. The checker computes a conservative
minimum level for each argument's type:

| Argument type | Required level |
|---|---|
| `Sort(m)` | `m` |
| `Level`, `Prop`, or a proposition | zero |
| A Type-valued function type ending in `B` | Maximum of its domains' classifier levels and the recursive bound for `B` |
| Any other type | Its classifier level |

Dependent function domains and results are evaluated under fresh typed binders.
A universe used as a function domain costs its successor classifier level;
a universe used as an argument type or function codomain costs its own level.
The resulting bound must be at most the family's declared level for every
valuation of symbolic level variables.

Thus `List(A: Type): Type` and a family with arguments `A: Type` and
`B: A -> Type` can remain in `Type`. A family taking `F: Type -> Type` or
`F: Type -> Prop` requires `Sort(Level.one)` or above. This check also applies
to families without constructors. `FamilyArgumentTooLarge` identifies the
argument and required minimum level.

Prop families are exempt from this size check. Stored fields of Type families
retain their stricter classifier-level bound. Both Type and Prop families remain
subject to strict positivity checks.

Function-valued family arguments must be free of the positivity target, even in
an otherwise positive argument position. The checker inspects both a lambda's
type and its body opened on fresh arguments. A blocked computation that might
contain the target cannot establish absence. This also applies when computing
which family arguments are positive and when excluding recursion inside a
family's own arguments.

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

The feature introduces no runtime value form or equality rule. Equality,
structural keys, substitution, quotation, and termination checking use their
existing representations and algorithms.
