# Kernel rules

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
