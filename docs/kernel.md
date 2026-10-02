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
environment and trusted by later declarations. Every definition is transparent
and publishes its evaluated value. Data-valued axioms publish symbolic heads;
proof-valued declarations are canonicalized from their exact propositions
before publication.

Checking and evaluation recurse on the host stack, except where evaluation
continues in tail position ([Evaluation depth](#evaluation-depth)). A stack
overflow is caught only at the boundary of a declaration, prelude declarations
included, or of the program's body, and becomes `EvaluationTooDeep` located
there; no rule inside them observes one. The declaration that overflowed is not
published, and checking stops, since the overflow may have unwound past the
restoration of the checker's state, thread-local and process-wide.

The bundled source prelude is a trusted bootstrap. A prelude is still parsed,
elaborated, and typechecked, but prelude loading alone may install builtin
declarations and native equations, and declare axioms. Selecting `--prelude`
therefore selects a different trusted bootstrap, which keeps the same audited
obligations (see
[Trusted bootstrap and native values](#trusted-bootstrap-and-native-values)).

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
- equality of normal forms for universe levels, kinds and lifetimes, and of
  sorts field by field;
- proof irrelevance at definitionally equal propositions;
- structure eta for eligible non-Prop inductive instances;
- equality and constructor peeling for validated packed values;
- conservative congruence of blocked matches with the same checked behavior.

Function binder grouping is exact. Two Pi values compare binder-for-binder and
must have the same binder count and binder modes (explicit, implicit or
evidence) within the current group.
`(a: A)(b: B) -> C` is not convertible with
`(a: A) -> ((b: B) -> C)`. Their closures compare exactly too: equal closure
kinds and equal closure scopes, as normal forms.

Conversion does not include universe cumulativity. Type fitting succeeds by
definitional equality, not by a general subtyping relation. Checking a term
against an expected type is synthesis followed by that equality: no check reads
the expected type, or its syntax, to decide the term's type.

### Refinement unification

The match checker runs the same unifier with a controlled set of refinable
variables. A link may be recorded only when the presented equation forces that
solution. In particular:

- Type-valued inductive family and data-constructor frames are invertible;
- a Prop family frame is invertible only at the root constructor-result-type /
  scrutinee-type equation. This permission does not pass to arguments, type
  congruence, or an equation between the propositions of two proof values;
- arbitrary applications, Pi components (closures included), blocked
  computations, and closure captures are not invertible frames;
- an occurs failure or an equation that has several possible solutions remains
  stuck;
- level variables link only when normalization leaves a forced solution;
- a kind or lifetime variable links only when it is alone on one side and does
  not occur on the other; when both sides are variables, the later-bound one
  links to the earlier-bound one. An atom is not a variable and never links:
  admitting a value's ids as refinable leaves its atoms out. Every other kind or
  lifetime equation, a join or union on both sides included, is stuck;
- refinable values at eta-eligible structure types are expanded at the
  refinability boundary, where eta makes the expansion unique.

The store records consequences, never guesses. Evaluation does not consume a
refinement store.

### Apartness

Apartness is the stronger result used to omit an unreachable match branch. It
is produced only by evidence that supports propositional no-confusion:

- a clash between distinct constructors of a non-Prop inductive, when both
  constructor heads carry checked no-confusion evidence and the two values are
  of one family at convertible parameters, one type up to its indices;
- distinct Type-family declarations and clashes among fully applied Type-family,
  Type-valued Pi, and Type-universe forms (the nominal principles below);
- unequal packed Nat payloads, which decode to `zero` against `succ` at
  finite depth, and a packed literal whose decoded head clashes with a
  constructor under the same condition. Packed character lists compare as
  their decodings do (see [Strings](#strings)), so they are apart only through
  such a clash there.

Constructor no-confusion relates values of one type. A clash between values of
families or parameters not known equal remains stuck. Independently, a nominal
clash between their types can exclude a constructor: for a family indexed by
`A: Type` with only a constructor at `A = Bool`, an instance at `A = Nat` has
no reachable constructor by N2. Arbitrary opaque types provide no such clash.

A key mismatch decides only that two values are not definitionally equal, so a
mismatch that one of these rules refutes at the two values' heads is decided
by the rule, whatever the keys. Same-head fully applied Type-family equations,
and the root-permitted Prop-family equation, also descend despite unequal
closed keys: their invertible arguments may contain a nested nominal clash.
Other conclusive key mismatches retain the stuck fast result.

Proof constructors, quotient constructors, Prop family heads, axiom applications,
level, kind and lifetime failures, and ordinary unification failures do not
produce apartness. No two kinds and no two lifetimes are apart, so refinement
never prunes a branch on one.

## Nominal Type families

Type-valued inductive families obey three principles. N1 makes a fully applied
family instance injective in its complete dependent argument tuple. N2 makes
instances of different declarations unequal. N3 separates family instances,
Type-valued Pi types and Type universes. These principles apply at arbitrary
depth, including nested Type-family arguments, and to sealed declarations.
They do not identify structurally identical declarations. Proof arguments are
compared modulo proof irrelevance; level, kind and lifetime annotations retain
their existing semantic equality rules.

Prop families have neither injectivity nor generativity: they may be equal
under propositional extensionality. Their decomposition during a match is
restricted to its root constructor-result-type / scrutinee-type equation.
It reflects the constructor witness at that exact fiber, rather than an
injectivity principle for a proposition's truth value. Nested Prop equations
are congruence checks: they cannot force links or propagate apartness.

Axioms, blocked applications and Quot type heads provide no nominal evidence.
Prop-versus-Type-sort comparisons and every sort-field failure remain stuck.
N3 applies to a Type-valued Pi, never a proposition-valued Pi. Two universes
convert only at equal level, kind and scope, but failure to compare those
fields is not a refutation.

For a Type family at level `n`, each ordinary parameter and index must satisfy
this sufficient elementwise bound:

| Argument type | Required level |
|---|---|
| `Type { level = m, … }` | `m` |
| `Prop`, or a proposition | zero |
| a Type-valued Pi telescope ending in `B` | maximum of each domain's ordinary classifier level and the recursive bound of `B` |
| any other ordinary type | its classifier level |

Annotation parameters (Level, Kind, Lifetime) are exempt. Dependent Pi domains
and results are checked under the fresh typed telescope. A universe domain
`Type_m` costs `succ(m)`, whereas a universe argument or codomain costs `m`.
Thus `List(A: Type): Type` and `Sigma(A: Type)(B: A -> Type): Type` remain
small, while a family taking `Type -> Type` or `Type -> Prop` must live at
level one or above. The check uses universally valid symbolic level inequalities
and each mutual family's own declared grade. `FamilyArgumentTooLarge` names
the argument and the required minimum grade. Ordinary stored constructor fields
still obey the stricter classifier bound. The rule is conservative: rejection
does not assert that every rejected declaration is individually inconsistent.

The [full informal model construction](nominal-model.md) interprets types as
extension/label pairs. Elementwise smallness bounds the nominal argument label;
a separate construction bounds extensions using small erased majorants and
monotone membership guards, including independent erased Prop witnesses.
Joint guarded least fixed points handle indexed, nested and mixed Prop–Type
mutual families. External typing prevents recursive payloads from containing
their complete type annotations. The construction also covers dependent
recovery-based large elimination, quotients, proposed propositional
extensionality, proof irrelevance, structure eta, annotations and polymorphism.
It is relative to the stated calculus and a consistent trusted prelude. It does
not prove collision freedom of the existing finite ValueKey hashes, or verify
every coverage/refinement implementation path. Local checked refutation
certificates remain a separate implementation obligation.

## Universes and function types

The sort formers are `Type { level = e, kind = k, scope = S }` for data and
`Prop { scope = S }` for propositions. Data levels begin at zero; omitted
fields are `Level.zero`, `Kind.unr` and `Lifetime.empty`. `Prop` has no level
or kind. The primitive universe equations are:

```text
Prop { scope = S } : Type { scope = S }
Type { level = u, kind = k, scope = S } : Type { level = Level.succ(u), scope = S }
```

`Level`, `Kind` and `Lifetime` are the sort parameters. Their forms,
`Level.zero`, `Level.one`, `Level.succ`, `Level.max`, `Kind.unr`,
`Kind.lin`, `Kind.join`, `Lifetime.empty` and `Lifetime.union`, are Core terms
too, always applied to all of their arguments. The kernel owns the parameters,
their forms and the sort formers: no declaration introduces them, the prelude
declares none of them, and no global or builtin carries a form's name.

Every sort parameter expression is normalized at birth, and its only neutrals
are variables:

- Levels normalize to maxima of offset atoms plus an optional constant.
- A lifetime is the set of its lifetime variables and atoms (see
  [Scopes and atoms](#scopes-and-atoms)); `Lifetime.union` is set union.
- A kind is `Kind.lin` or a set of kind variables, the empty set being
  `Kind.unr`; `Kind.join` unites the sets, and `Kind.lin` absorbs.

Normalized representation equality is equality of levels, kinds and lifetimes.
Each normal form is built only by its own constructors, which sort and
deduplicate, so one implementation of union, join and containment serves the
checker and the evaluator. A kind or lifetime has no neutral other than a
variable or an atom, so no two of them are ever apart.

Data sorts admit every kind at every level. Proofs are unrestricted: a
function type into a proposition must have closure kind `Kind.unr`.

A telescope

```text
{ kind = k, scope = C } (x1 : A1) ... (xn : An) -> B
```

that binds no level has the sort

```text
Type { level = max(u1, ..., un, v),
       kind = k,
       scope = union(C, S1, ..., Sn, SB, M)
               less the telescope's own lifetime variables }
```

where each `Ai : Type { level = ui, scope = Si }`,
`B : Type { level = v, scope = SB }`, and `M` is the function type's mentioned
scope: what the locals bound outside it that its binder types and codomain
mention contribute, by the rule a lambda's captures follow below. Those are
code, evaluated each time the type is instantiated, so the type belongs to
everything they hold. The closure `{ kind = k, scope = C }` is the function
type's closure kind and closure scope: how its values may be applied, and what
they hold. It is evaluated where the Pi
stands, outside its own binders. A proposition domain contributes level zero. A binder of type `Kind` or `Lifetime`
contributes neither a level nor a scope. Consequently, a Pi whose codomain is a
proposition lives in `Prop` at its scope, regardless of its domain universes. A
codomain equal to the sort `Prop` is different: `Prop` itself lives in `Type`.

A written function type has no body to derive a closure from, so the
elaborator writes an omitted closure field of one as the least, `Kind.unr` or
`Lifetime.empty`; what its code captures is its mentioned scope, not its
closure, and a declaration's own type is
always at that closure. A lambda's closure is part of its type and is decided by
the lambda alone. Its captures are the locals bound outside it that its body
mentions, in terms and in types written in the body; its binder types and
result are not its body, and implicit arguments are never written, so neither
contributes. Each capture contributes the kind and scope of its type's sort,
and a local of type `Lifetime` contributes the lifetime it holds to the scope: a
lambda belongs to every lifetime its code names. A variable of `Level` or `Kind`
contributes nothing, and neither does a recursive definition's reference to
itself, which names a global. The lambda's own lifetime binders are not
captures: its caller supplies them. An omitted closure field is the join of the
captures' kinds or the union of their scopes; a written one must contain it,
else `KindExceeded` or `ScopeExceeded` naming a capture it does not contain.
That test, a family's declared kind against its fields' and a type former's
declared scope against its lifetime parameters are one containment rule with
one implementation.

The residual carries a derived field as the captures it is derived from. Every
evaluation of the lambda, the one checking makes included, reads those captures
in the environment it is evaluated in and derives the field from their values'
types' sorts and the lifetimes they hold; one function does it. A capture that
contributes `Kind.unr` or `Lifetime.empty` to a field as checking saw it is
left out of that field, since every instantiation keeps it so: a lambda whose
captures are all unrestricted and unscoped carries none. Sorts commute with
substitution, so an evaluation derives what checking would derive under that
instantiation. A function type's mentioned scope is derived by the same
function, from the locals its binder types and codomain capture, wherever it is
evaluated. A printed residual shows a
derived field as omitted, as the source did.

A telescope that binds a level is instead classified by `Large`. A level binder
changes the universe of everything after it, so no sort contains the Pi. `Large`
is kernel-internal: it is not a sort, no program writes it, and it classifies
itself, which is harmless because nothing quantifies over it. A type's
classifier is therefore a sort or `Large`, and code that reads a Pi's
classifier handles both. Instantiating a large Pi's binders yields small types
again: its codomain is always a type. Kind and lifetime binders never make a
Pi large.

The sort parameters are not types: their classifier is not a sort. Every
checked term must have a type, except in the positions that admit something
else:

- a binder of a sort parameter is admitted only where its site allows: a
  parameter site (a declaration's header, the binders before its `:`, or a
  family parameter) may bind any sort parameter, a function type's or lambda's
  binder only a lifetime, and a family index or constructor field none.
  Everywhere else a binder's type must be a type. The elaborator records each
  binder's site, so a function type written after a declaration's `:` binds no
  level;
- an expression of a sort parameter stands only where a sort parameter is
  expected: a sort's field and the argument at a binder of a sort parameter,
  which is checked against that parameter rather than synthesized alone. A term
  of another type there, another sort parameter's included, is a type mismatch;
- a reference whose type is large stands only as the head of an application;
- a large type is admitted only as a declaration's type: a definition, axiom,
  family or constructor, and a definition's lambda at that type.

Anywhere else a sort parameter, an expression of one, or a large reference is
`NotAType`, except as the base of a selection `b.f`: only a value of a family
instance has selectors, so any other base, these included, makes `b.f`
`NotFound`.

Universes are non-cumulative, and so are kinds and scopes: two sorts are
convertible only when their levels, kinds and scopes are. A function type's
mentioned scope is part of its identity, beside its closure, so two function
types are convertible only when their mentioned scopes are, and a type
determines its sort. Constructor-field
universe checks enforce the declared inductive's size bound, but they do not
introduce general sort subsumption.

A sort is `Prop` exactly when it has the proposition tag, and a type is a proposition
exactly when its sort is `Prop` (a Pi by its codomain, so a large Pi into a
proposition is one too). The kernel has one definition of each, which the
checker and proof irrelevance share. Sorts are compared only by conversion.

An implicit binder is accepted only with a compiled projection that recovers
it from later explicit arguments. A sort's level, kind and scope, and a function
type's closure kind and closure scope, are projection positions; the kinds and
scopes recover a variable only when the field is exactly that variable. So are
a function type's domains, codomain and result where they do not depend on its
own binders, a proof's proposition, a no-confusion constructor's stored fields,
and the arguments of an application of a family or of a type former: a trusted
axiom whose type ends in a sort, such as `Quot`, which names each of its
lifetime parameters in its declared scope as a family does, else
`ScopeExceeded` at the axiom. The arguments of any other application, another
axiom's, a stuck builtin's or a parameter's, are not: such an
application is a blocked computation, and what its arguments hold is counted by
no type's sort; so is a checked recursive call. Only a type former's
application of its whole type, one binder group, is read. A function type's
mentioned scope is not a position either.
Positions are searched breadth-first from the explicit arguments, and a closure
field only once no other position is left: a closure is what a lambda derives
from its captures, so reading an implicit elsewhere lets a lambda written
without the closure its parameter declares fail its own check. Only explicit
binders are roots: an evidence binder is not, supplied or not, since its
argument is discharged from its proposition (see
[Evidence arguments](#evidence-arguments)). Checked applications retain only
explicit arguments. Checking and evaluation
reconstruct every implicit with the same projection and then check it against
its instantiated binder type. Constructor family parameters that cannot be
projected are demoted to explicit arguments; other unforced implicits are
rejected.

## Scopes and atoms

`scope l => e` is a Core term of its own. It opens an atom: an id in a
lifetime's set, allocated like a variable's and printed as the `scope`'s
binder, but not a variable. One registry, shared by checking and evaluation,
maps the term's node identity to its atom, so two `scope` terms are two
atoms and one term checked or evaluated any number of times is one atom, a
recursive call re-entering it included. Both checking and evaluation bind `l`
to the lifetime holding exactly that atom, and the term denotes its body's
value. A residual keeps the term with its node identity, so re-evaluating it
opens the same atom. An atom is never refinable, so refinement never links it,
and nothing abstracts over it: a function type's scope drops only its own
binders' variables.

Confinement is the one check an atom needs. A type whose sort's scope names an
atom whose `scope` does not enclose the position is `LifetimeEscapes`. A type's
sort is its classifier; a sort's own sort is at the same scope, so a type at a
type position is confined through its sort, and a large type or a sort
parameter names no atom. The checker keeps the atoms whose `scope` encloses the
position in its environment; they are lexical, and closing an environment over
a value drops them. One test applies the rule, reading the sort's scope and
nothing else; it returns at once until a program opens an atom. It is applied
at these choke points:

- every type the checker synthesizes, at the one exit of synthesis, so a
  `scope`'s own type is tested where its atom is no longer open; this is what
  keeps the body's type's sort from naming the atom;
- every type a term is checked against;
- a binder's type, which is the type of the local it binds, and a pattern
  field's type;
- an argument at a binder whose type is a sort, which is itself a type.

Evaluation never makes the check, and needs none: once a `scope` closes,
nothing can hold, create or use a value whose type's sort names its atom. A
value reaches an atom only through what it is made of, and each part is
counted in its type's sort's scope:

- a constructor's fields, through its family's declared scope, which contains
  every field's and names every lifetime parameter (see
  [Inductives and matching](#inductives-and-matching));
- a lambda's captures, through its closure scope;
- code that names a lifetime, through a lambda's closure scope or a function
  type's scope (see
  [Universes and function types](#universes-and-function-types));
- a type, through its own sort.

Two kinds of value hold an atom their type's sort does not name, and neither
runs: a computation blocked on an axiom or a builtin, or, while checking, on a
parameter; and a proof. Nor can an implicit read the atom back
out of one: a blocked computation's arguments are not projection positions (see
[Universes and function types](#universes-and-function-types)). So a global
value may hold an atom only inside a blocked computation or a proof, and never
a variable. The `scope`'s own type does not name its atom, by the check at its
exit, and no value bound before the `scope` opened can name it.

A derived closure holds an atom when a capture's type's scope does, or a
captured lifetime holds it (see
[Universes and function types](#universes-and-function-types)): either names
only atoms whose `scope` encloses the lambda.

## Linearity

A type is linear when its kind is not `Kind.unr`: `Kind.lin`, or a kind
involving a variable, which some instantiation makes `Kind.lin`. A function
type's kind is its closure kind, and any other type's is its sort's, so a
family instance is linear when its declared kind under its arguments is, and a
type variable when the sort its type states is. Sorts and propositions are at
`Kind.unr`. One function decides it, and every linearity rule asks it.

Every local of linear type is used exactly once within the extent of its
binder. The binders are a lambda's or definition's parameters, whose extent is
the later binders' types, the result type and the body; a `let`, whose extent
is the rest of its block, a destructuring's for each local it binds; and a
pattern field, whose extent is its branch. A pattern binds a local for every
field, a `_` an anonymous one no name resolves to, and so do `let _` and a
destructuring's `_`. Whether a local is tracked is decided once, from its
type at its binder, so refinement never changes it. A value outside every
binder is never tracked, so its type may not be linear: a definition, which
every reference uses, and the program's result, which
nothing uses, are `LinearGlobal` when their type is linear. The result is
checked once the entry program's body has checked, and reported where its
type comes from, as a mismatch is; an imported module has no body.

The ledger checks the residual of each tracked binder's extent once that
extent has checked. It counts uses along every path that takes one branch at
each `match`, and a use is any occurrence of the local. A match's scrutinee and
motive lie on every path through it; a match with no branch ends every path
through it, so it uses every linear local live at it, and nothing after it
lies on those paths. A lambda or function type is a path boundary: its body
runs only when it is applied, so a path through its body neither continues nor
ends a path around it. One whose cached references do not mention the local is
no use and is not walked. One that does is one use, by the lambda, at its
position, and its body must use the local exactly once on every path through
it, where a match with no branch ends a path as anywhere else. A term's paths
are summarized by whether one continues unused, the first use on a path that
continues, the first use on any path and the first second use, so a use on a
path that a match with no branch ends is never counted against a use after
that match. A lambda that uses a captured local is itself linear, since it
captures a local of a linear type, and is tracked like any linear value:
applying it is its use. A lambda's `decreases` clause is not in its body and is
not a use.

A second use on some path is `LinearReused`, located at that use; otherwise no
use on some path is `LinearUnused`, located at the binder. So matching a
linear scrutinee consumes it once, and its fields are released to the ledger
at the branch's extent, where `_` for a linear field is `LinearUnused`. A
destructuring consumes its value the same way, and releases
its locals at the rest of its block, each reported at its component. A struct
selector is a definition whose body is a match, so applying one to a linear
value is that value's use. The ledger is one walk, an exhaustive match over
Core terms with no wildcard arm, and runs only for a binder of linear type.
Evaluation makes none of its checks.

Types and proofs hold no tokens: a term whose type is a sort or a proposition
may not contain a subterm of linear type, else `LinearInType`, located at that
subterm. This covers a type at a type position, a type computed as a value, a
`returning` motive and a proof alike, and a lambda inside one that consumes
its own linear parameter; such a function is a definition, referred to by
name. Types and proofs are copied and dropped freely, and a proof never runs,
so a token inside one would escape the ledger. The test is made at the
checker's one synthesis boundary: each synthesized subterm of linear type is
handed to the enclosing synthesis, and a term whose type is a sort or a
proposition refuses the first one it was handed. It fires before the ledger
could count an occurrence in a type as a use. So no type contains a linear
local, and facts about a token are stated about its indices. An implicit
binder of linear type is never forced, since forcing reads types: implicit
projection gives it no hole, and it is `NonForcedImplicitParam`.

A selector of a linear struct is therefore rejected when another field is
linear (`LinearUnused` naming that field), when its field's type names an
earlier field, since its result type applies that field's selector to the
struct value (`LinearInType`), and when its field is a proof, since its body is
then a proof that consumes the struct value (`LinearInType`). The failure is
the selector's own; the family and its other selectors are still published.

Until a kind other than `Kind.unr` has been built no type is linear, since a
type's kind is a kind that was built, and every linearity rule returns at once.

## Inductives and matching

An inductive declaration is installed only after checking:

- that the family result is a sort;
- universe bounds for every constructor field, and elementwise argument bounds
  for every ordinary parameter and index of each Type family;
- kind and scope bounds: the family's declared kind, which is never derived,
  contains every constructor field's kind, `Prop` families included; and every
  family, whatever its kind, names each of its lifetime parameters in its
  scope, so that a lifetime a forced implicit reads off an instance is counted
  in the instance's sort. The declared scope may mention only parameters, so
  it is exactly the union of the lifetime parameters. Only a parameter binds a
  lifetime and no atom is open at a declaration, so every field's, parameter's
  and index's type's scope lies within it, and none is checked;
- that every constructor result is the declared family with uniform
  parameters and well-typed indices;
- strict positivity of recursive occurrences;
- nested positivity only through parameters that the referenced inductive
  block certifies as positive.

A family instance's sort is the declared result sort under the instance's
arguments, never something read off the arguments' values, so it commutes with
substitution. A family at a kind variable is therefore linear exactly at the
instances whose kind argument is. A field of a sibling or of the family itself
is read by that declared sort, so the bounds need no fixed point. A variable in
the declared sort can only be a parameter, since no index binds a sort
parameter.

Atomic mutual-inductive blocks are available through the surface `mutual { ... }`
form. Every family in a block has the same parameter telescope, so every
family's scope is the union of the same lifetime parameters. Its level and kind
are its own: each family is checked against its own declared sort, and a
sibling's field is read by the sibling's. Where siblings hold each other, the
field bounds force compatible sorts. All provisional family heads are visible while
constructors are checked, but the block publishes only after every family
succeeds. Positivity and recursion metadata are computed for the whole block.

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
- the motive, which the match writes as its `returning` clause, is a type;
- every branch has the instantiated motive.

A branch's fields enter fresh, at the scrutinee type's own parameter arguments.
Parameters are uniform, so they need no equation: refinement relates the
scrutinee to the constructor applied to those fields, and the constructor's
result indices to the scrutinee type's. An omitted constructor is valid
only when its result is apart from the exact scrutinee type. A stuck equation
keeps the constructor reachable and provides no refinement; the fields keep
their types at the scrutinee's parameters.

A match's last case may be a wildcard, `| _ => e`. Before any case is checked,
the checker expands it into one case for each constructor the written cases do
not name and a missing case would be reported for: when the scrutinee is in
constructor form, its own constructor; otherwise every constructor whose result
is not apart from the scrutinee type. Each expanded case is the case written
out at the wildcard: every field bound to a fresh anonymous local, located at
the wildcard, and a fresh copy of `e` for its body, with fresh node identities
and fresh locals for everything `e` binds, so no two cases share a closure, a
stuck match or a `scope` atom ([Value identity](#value-identity)). Its
refinement, its ledger (an unused linear field is `LinearUnused` at the
wildcard) and the termination check of a recursive call in `e` are that case's.
A wildcard that stands for no constructor is `RedundantCase`, located at it. A
failure while checking an expanded case names the constructor it was expanded
for; the ledger of a local bound outside the match runs on the whole match
afterwards, and reports a use in `e` without it. The residual is the expansion,
listing every case, written or expanded, in constructor declaration order, so
it converts with the match written out in full in that order; evaluation,
conversion and the ledger never meet a wildcard.

A match may name its equation, `match h : e`. The scrutinee's type `T` must be
unrestricted, else `LinearInType` at the scrutinee, since the equation is a
proposition about it, and its family must have no indices, else
`MatchEquationIndexed` at `h`; both are checked once, at the match. Each case,
an expanded one included, binds `h` after its fields, as a proof of
`Eq(T, e′, C(p̄, x̄))`: `e′` is the checked scrutinee and `x̄` the case's
fields, both under the case's refinement, and `C(p̄, x̄)` is the constructor
value refinement unifies the scrutinee with, at `T`. Without indices it has type
`T` in every case, so the equation is well typed without refinement. `h`'s type
is confined at its binder as a field's is; it is unrestricted, so the ledger
does not track it. Nothing is rewritten by it: the motive and the other locals
are as they would be without it. `Eq` is the validated equality family of the
trusted prelude (see [Equality](#equality)), so the hypothesis is true whenever
the case runs. A case no run reaches has an unprovable `h`, as it may already
have impossible fields. The residual keeps `h`, and a wildcard's fresh copies
of its body rename the equation of a match inside it, as every local it binds.

Evaluation reduces a match only when the scrutinee exposes a justified
constructor view. Otherwise it retains a blocked match with the dependencies
that could make reevaluation productive, whose type is the motive evaluated in
the match's environment. A match that takes a case, by a constructor view or a
structure-eta view, binds its equation, if it names one, to deferred evidence of
`Eq(T, v, C(p̄, v̄))`, `v` the scrutinee's value and `v̄` the fields as bound;
since `v` is that view, its canonical proof is `Eq.refl(v)`. A blocked match
binds nothing. Comparing two blocked matches case by case binds each one's
equation in the same way, at the fresh fields.

## Proofs and elimination

Proof irrelevance is definitional:

```text
p : P, q : Q, P and Q propositions
-----------------------------------
p ≡ q  iff  P ≡ Q
```

Operational behavior must be congruent with that equality. A proof's canonical
outer representation is chosen from its exact proposition:

1. A declaration-certified, one-constructor recovery plan may reconstruct a
   constructor after every field is recovered and the constructor result is
   definitionally equal to the exact proposition.
2. A Pi proposition becomes a synthetic proof eta-lambda. Applying it produces
   the canonical proof of the instantiated codomain; the checked source proof
   body does not run. A large Pi into a proposition is proof-valued too, so a
   level-polymorphic lemma such as `Eq.symm` publishes as this eta-lambda and
   its body never runs.
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
on a proof in constructor form, which exact constructor-result validation
admits. A non-reconstructible proof leaves a data-valued match blocked. This
separation prevents constrained indexed propositions from manufacturing data.

`ProofReconstruction` alone reads a family's recovery plan and its
constructors' field sources, so a proof is reconstructed, and evidence
discharged (see [Evidence arguments](#evidence-arguments)), by one reader.

Proof constructor identity and fields provide no injectivity, apartness, or
termination evidence. Recursive proof fields are exposed one layer at a time,
so canonicalization never builds an infinite proof value eagerly.

## Evidence arguments

A binder's mode is explicit, implicit or evidence, and it is part of its
function type's identity: conversion compares modes binder for binder, and a
Pi's key mixes them in. An evidence binder `[h: P]` stands in a definition's,
lambda's, function type's or constructor's telescope; a family's parameters
and indices have none, and neither has a builtin's own binder group
(`BuiltinEvidence`), since a builtin reads its arguments as values. Its type
must be a proposition, else `NotAProposition`. It is not explicit: it is not
among the arguments an application writes, and it is never a root of implicit
projection.

Checking an application walks its binder group as for implicits (see
[Universes and function types](#universes-and-function-types)). In the final
pass, which binds every binder in telescope order, an evidence binder's type is
evaluated once, in the Pi's environment with every earlier argument bound, to
the proposition `P′`. Then:

- if the application supplies its evidence, `f(x)[p1, …]`, it supplies one
  proof per evidence binder, else `ArityMismatch`; each proof was synthesized
  where it stands, as an argument is, and its type must be convertible with
  `P′`;
- otherwise `P′` is discharged, by rule 1 or else by rule 2, below. Anything
  neither discharges, a `P′` that is not a family instance included, is
  `EvidenceNotDischarged`, located at the application. It shows the
  proposition discharge failed at, as evaluated, and, when rule 2 reached it,
  the path of evidence fields to it from `P′`, each step `Family.field`, depth
  first in field order.

**Rule 1.** `P′` is an instance of an inductive family whose constructors are
declared; they are tried in declaration order, and the first that fits is the
proof. A constructor fits when each of its fields, a proof field included,
occurs as one of the arguments of its result type, so that its value is read
off `P′` at that position and has the field's type there, and when its result
type at `P′`'s parameters and those fields is convertible with `P′`. The proof
is that constructor applied to them, canonicalized as every proof is.

**Rule 2.** `P′` is an instance `F(ā)` of an evidence-eligible family, and no
constructor fits rule 1. A family is evidence-eligible when it is declared in
`Prop` , has one
constructor and no indices, no field type of its constructor mentions a family
of its inductive block, and every field is an evidence field; eligibility is
recorded when the family is checked. Each field's type, in order, is evaluated
in the constructor's telescope with the parameters bound to `ā` and the earlier
fields to their proofs, and discharged in turn, by either rule. The proof is the
constructor applied to those proofs, canonicalized. The arguments `ā` may be
anything: open, stuck, or holding functions.

**The depth bound.** Discharge counts the rule-2 steps on its current path,
from `P′` to the proposition being discharged. A proposition that a rule-2 step
at depth greater than `N = 1024` would discharge is not discharged: the
application is `EvidenceNotDischarged`, reporting the path and the bound. The
bound is a constant of the language, not a flag, so whether a program checks
does not depend on how it is run.

Where each field occurs is compiled once, when the family is checked, for a
family whose instances may be propositions; proof reconstruction reads the same
sources (see [Proofs and elimination](#proofs-and-elimination)). The binder is
bound to the proof, a supplied one as the canonical proof of `P′`, and the
application is evaluated with it. The residual keeps neither a supplied proof
nor a discharged one.

Rule 1 is sound because it adds no proof that the object theory lacks: every
field is a value `P′` already holds, checked against its field type, and the
constructor's result type is convertible with `P′` by definitional equality
alone, so the constructor applied to `P′`'s own parameters and those values is a
well-typed proof of `P′`, one the program could have written there. It invents
no field: a field its result type does not determine, or determines only inside
an argument, makes the constructor unfit. Proof reconstruction fabricates proof
fields unchecked, which rule 1 never does, so a rule that accepted whatever
reconstructs would accept `And(False, False)`. It consults no hypothesis beyond
what `P′` holds, which it may copy into a field, and chooses nothing that proof
irrelevance would not make unobservable. Rule 2 is sound by induction on its
steps: each field's proof is a proof of that field's type at `ā` and the earlier
proofs, so the constructor applied to them is a well-typed proof of `F(ā)`, the
one the program would write as `F.mk(…)[p1, …]`. It chooses nothing, since the
family has one constructor, and recurses only into evidence fields, never
guessing a data field. Under either rule a sealed family's constructor is
applied only where the application's module may name it (see
[Sealing](#sealing)), since elsewhere it would build a value its module never
built; under rule 2 that holds at every step. A family of an inductive block
still being checked has no constructors to discharge with.

Discharge is local: it reads the callee's type and the application's other
arguments, never the type the application is expected to have, so checking
stays synthesis followed by equality. It terminates:

- each rule-2 step evaluates one field's proposition, and evaluation of checked
  terms is total (see [Termination](#termination));
- an eligible family's constructor has finitely many fields, so each step has
  finitely many successors;
- no path has more than `N` rule-2 steps, so the tree of steps is finite
  (König's lemma);
- at each node rule 1 evaluates, for each constructor, each parameter's and
  field's type and its result type, and compares by conversion, which
  terminates.

Nothing here orders terms, so nothing restricts rule 2's arguments. Condition 2
of eligibility is not needed for termination either; it makes a family nested
in its own field, which could only ever reach the bound, not eligible, so
`inductive Loop : Prop | mk [h: Loop]` is refused at once. The bound limits
nesting, not work: evaluation may duplicate a proposition, so a tree of depth
`d` may have exponentially many leaves in `d`. Each step is host recursion, so
a path of `N` steps needs a few megabytes of the checking thread's stack. Its
time includes the decision procedures a proposition calls.

Evaluation erases evidence. A checked application carries only its explicit
arguments, and evaluating it gives each evidence binder deferred evidence: the
canonical proof of the binder's type, evaluated in the Pi's environment with
every earlier argument bound, computed only when forced. Applying a head forces
none of it: a lambda binds it unforced in its body's environment, and any other
head, an axiom's say, stores it unforced among the arguments of the
application it builds. A match's named equation is bound to it too, in the
environment of the case taken. Those are where deferred evidence stands, and they
force it where it is read: the environment where the local is looked up or a
value closes over it, and the application where its arguments themselves are
read, as a use of them does. Anything else that reaches deferred evidence is a
kernel bug. A match or a destructuring binds a constructor's fields as stored,
so the local, not the match, forces an evidence field where it is looked up,
and materializing an environment keeps it unforced; implicit projection, when a
program runs, forces only the one argument or field it reads; and printing
shows no evidence argument or field. So a proposition is evaluated when a
program runs only if something looks at its proof, and then the proof is
exactly the canonical proof its proposition determines, as checking bound:
erasure changes when a proposition is evaluated, never what a value is.

An application's evidence arguments, at its head's evidence binders or its
constructor's evidence fields, are determined by the rest of it. Each is a
proof of its binder's proposition, its binder type evaluated in the head's
function type's environment with the arguments before it bound, whether
checking bound it or evaluation deferred it, and its dependencies are that
proposition's: a canonical proof's, a discharged proof's, whose fields are read
off the proposition or are proofs of propositions evaluated from it, and a
supplied one's, which checking binds as the canonical proof. So:

- its dependencies are among the application's others: evaluation introduces no
  free variable, so they
  are among those of the function type's environment, which the head's
  dependencies include with its type's, and of the arguments before it, the
  evidence among them by induction;
- two applications whose heads and other arguments are equal have equal
  evidence arguments: equal heads have equal types, so the propositions are
  equal, and proofs of equal propositions are equal (proof irrelevance). For
  the same reason, heads and other arguments that unify leave the evidence
  equations with nothing to link.

An application's dependency set, its key and its conversion therefore read only
its other arguments, and skip its evidence exactly: the set is the same,
conversion reaches the same verdict with the same links, and equal keys are
still convertible. A key mismatch is no longer made inconclusive by a proof
among the evidence, so an application with evidence may now be decided by key
where it was compared structurally. Materializing an application keeps its
evidence unforced, at the proposition materialized, and reapplying a head once
it is unblocked defers the evidence afresh at the head it then has, so that
head still determines it. So its dependencies, and the closedness a published
global is asserted to have, its key and its conversion force none of its
evidence, and printing a call reads only its explicit arguments. Evidence is told by
binder mode: a supplied, a discharged and a deferred proof are skipped alike.

**Evidence fields.** A constructor's evidence binder is an evidence field.
Constructing is applying, so a construction discharges an evidence field, or
takes a supplied proof, exactly as an application does its evidence argument,
and evaluation stores deferred evidence in the constructor application it
builds, evaluating no proposition. Its type is checked as any field type is
(universes, kinds, positivity), may mention the family's parameters and the
earlier fields, and forces no implicit. It is a stored proof field: a pattern
and a destructuring bind it in its place among the stored fields, a generated
selector returns it, and rule 1 treats it as any field. Structure eta
compares an eligible value's fields but its evidence fields, which the others
and the type determine, so two values that differ only in an evidence field are
equal, and comparing them forces none; at a structure whose fields are all
evidence, any two values are equal, as at a fieldless one. The native literal layouts have no
evidence field, since each field of theirs is data, so packing a constructor
application never sees deferred evidence.

## Structure eta and projections

Every one-constructor family records positional field metadata. A non-Prop
instance is structure-eta eligible exactly when the checked family has:

- one constructor;
- no indices;
- no recursive constructor field in its inductive block.

A sealed family is eligible like any other (see Sealing).

Eligibility depends on the checked family, not on whether the source used
`struct`. Prop instances use canonical proof representation and never structure
eta.

Eta is a rule, not a representation invariant. At an eligible type, a value is
definitionally equal to its constructor applied to its fields. A
constructor-headed value exposes stored fields; a neutral value exposes virtual
field projections. Conversion, match evaluation, destructuring, and
structural-subterm checking all use the same eta view; conversion leaves out
its evidence fields, which are proofs the other fields determine (see
[Evidence arguments](#evidence-arguments)).

A destructuring `let (x1, …, xn) := e` binds each local, transparently, to its
field of the eta view of `e`'s value, in checking and in evaluation alike. So
it has no motive, never blocks, and a destructured local is a structural
subterm of `e`'s value exactly as a one-branch match's field is. It is admitted
only at an eligible `Type` family instance. Data universe substitution never
changes a data family into a proposition. A nested pattern is
a destructuring into an anonymous local followed by a destructuring of that
local, so each level is checked alike.

There is no primitive projection value. A positional projection is the
ordinary one-branch match that returns the chosen field. Like every match, it
has a motive: a synthetic local bound to the field's type at the projected
value. Surface `struct` selectors are generated definitions containing those
matches, with the selector's declared result type as motive. Therefore a
projection from `Prop` is governed by the proof-elimination rules above.

## Sealing

A `sealed` family exports its head, parameters, indices and classifier, but
its constructors and selectors only to its module, the source file its
declaration was read from. Outside that module each of these is
`SealedConstructor`:

- a global reference to one of its constructors or selectors, applied or not,
  under any name that resolves to it;
- selecting one of its fields;
- a match whose scrutinee is an instance of it. A case's `.short` form resolves
  only against the scrutinee's family, so this covers it;
- a destructuring whose value is an instance of it, which is a match that
  names no constructor.

The names still resolve, so each such use reaches this diagnostic. A family's
seal names its module, which every parsed declaration has, and its
constructors and generated selectors take that one seal. No position is
exempt: a position's module is the source it was read from, and a position in
no source lies outside every module.

A native literal layout refuses a sealed family (see Trusted bootstrap and
native values), since a literal makes the family's values wherever it is
written.

Implicit projection reads a sealed constructor's field only when the telescope
it compiles is written in the family's module; elsewhere an implicit that only
that field would force is `NonForcedImplicitParam`. A path compiled inside the
module is followed wherever its definition is applied, and a reconstructed
implicit may be a sealed constructor application: neither is written by the
program that applies it.

Structure eta and proof reconstruction apply to a sealed family as to any
other. Only the trusted prelude declares axioms and builtins, and none of them
yields a value of a sealed family except by applying its constructors
(obligation T2, see
[Trusted bootstrap and native values](#trusted-bootstrap-and-native-values)),
so every value of a sealed family was built from its constructors: a neutral
of one is a parameter a caller supplied or a blocked computation. Eta and
reconstruction therefore open
nothing the module did not build. A match in the module opens a proof that a
module function returned, although the function's body never runs, since the
proof is reconstructed from its proposition.

Sealing restricts what a program may write, not what the checker knows.
Kinds, scopes, coverage, apartness and the conversion of values read the full
declaration in every module, and evaluation compares no module. One function
decides whether a position may use a sealed family's constructors; the checker
asks it at those name resolutions, match scrutinees and destructured values,
and before it discharges evidence with a constructor, and implicit projection
asks it before reading a constructor's field.

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
and values of axiomatized types are rejected as metrics.

While checking a recursive body, a raw recursive reference is valid only as
the head of a direct call whose metric decreases. It cannot escape into a
closure, constructor field, argument, return value, or blocked application.
Runtime recursion uses the already checked lambda and performs no further
decrease test.

Mutually recursive definition blocks are available through the surface
`mutual { ... }` form and are published atomically. Their members have
compatible lexicographic metric shapes, and every cross-component call must
decrease from the caller's current metric. Measure specifications are not
supported for recursive definition blocks.

## Evaluation depth

Evaluation is strict, and it takes no host stack for a term in tail position,
whose value is the value of the term being evaluated: a block's result after
its lets, a match's chosen branch, a scope's body, and a core lambda's body
where the lambda is applied, after the application's arguments. The evaluator
continues with that term in a loop instead of recursing into it. Native
bodies, proof eta-lambdas, constructor heads and neutral heads produce their
results directly. The loop changes no value, neutral or blocking set: it
removes host frames only, so evaluation that exhausted the stack may now
finish instead of reporting `EvaluationTooDeep`. Recursion outside tail
position is bounded by the host stack, whose exhaustion is that diagnostic
(see [Trust boundary](#trust-boundary)).

## Axioms and quotients

Every definition is transparent: it reduces during checking and evaluation.
Only the trusted prelude introduces names that do not compute, its axioms and
builtins, so a closed value of an inductive type reduces to a constructor
unless one of them blocks it. Axioms do break closed canonicity: such a value
may remain a symbolic or blocked application instead of reducing to a
constructor. Kernel code must therefore never assume that every closed
inductive value is constructor-headed, nor that an open one is while checking.

Only a trusted prelude declares axioms. An `axiom` in any other module is
`UntrustedAxiom`, reported at the declaration before its type is checked. A
program that needs an assumption declares it in a custom prelude
(`--prelude`), such as a copy of the bundled one with the axiom added;
selecting it explicitly extends the trusted base. An axiom may introduce an
arbitrary symbolic inhabitant. It is typechecked, but its consistency is the
prelude's responsibility (obligation T1). Proof axioms still canonicalize
according to their exact proposition; data axioms remain symbolic.

No rule on an axiom's type could make program axioms safe. An axiom can state
`False`, from which every value follows, a token or an equation between
lifetimes included. Even a consistent one can break an abstraction: an axiom
over a linear type consumes a token without its module, one at a sealed family
yields a value its module never built, and an equation between two instances
of a family at different lifetimes is irrefutable, since no two lifetimes are
apart, yet refinement along it links a lifetime variable and lets a token leave
its scope. So these are obligations of the trusted bootstrap, T1 to T4 (see
[Trusted bootstrap and native values](#trusted-bootstrap-and-native-values)),
and sealing, linearity and confinement hold unconditionally, relative to an
audited prelude that keeps them.

The bundled quotient interface is the fixed non-inductive primitive surface:

- `Quot` is an axiomatically declared type former;
- `Quot.mk`, `Quot.lift`, and `Quot.ind` are prelude-only builtins;
- `Quot.sound` is an axiom identifying related representatives.

`Quot` is an axiom whose type ends in a sort, a type former: its scope, the
union of the scopes of `A`'s and `r`'s types, is written by hand as part of the
trusted bootstrap, and checked to name `S`, `Sr` and `Sq`. The builtins
locate their arguments in their declared types by binder name, so the prelude
may add binders, such as lifetime variables, without moving them.

`Quot.mk` is not a no-confusion constructor. Quotient equality is intentionally
coarser than representative structure, so quotient values supply neither
constructor injectivity nor apartness. `Quot.lift` reduces on `Quot.mk` only
through its registered builtin equation; `Quot.ind` provides the Prop-valued
eliminator.

## Trusted bootstrap and native values

Only a trusted prelude may publish builtin declarations or native literal
layouts, or declare an axiom. Ordinary modules cannot gain native semantics by
declaring a reserved name.

That privilege is the whole of a prelude's trust. Its axioms, builtins, native
operations and native literal layouts are its trusted surface. Every other
prelude declaration is checked exactly as one in any module, so a prelude may
declare a linear, kind-polymorphic or sealed family as any module may. The
trusted surface is not checked, so a trusted prelude, bundled or given with
`--prelude`, keeps these obligations, which are audited:

- **T1 Consistency.** The axioms are consistent with the kernel's rules.
- **T2 Sealing.** No axiom or builtin yields a value of a sealed family except
  by applying that family's constructors. Structure eta and proof
  reconstruction apply to sealed families because of this (see
  [Sealing](#sealing)).
- **T3 Linearity.** A builtin uses each argument whose type is linear, or at a
  kind variable, exactly once on every path. No axiom takes or yields such a
  value, since an axiom has no body to account for it.
- **T4 Lifetimes.** No axiom makes two distinct lifetimes, or two instances of
  a family at distinct lifetime arguments, provably equal. No two lifetimes are
  apart, so such an equation is consistent, yet refinement along it links a
  lifetime variable and lets a token leave its scope.
- **T5 Native equations.** Each native operation's declared body agrees with
  its host equation (see [Natural numbers](#natural-numbers)).

T1 subsumes nothing: a consistent axiom can still break T2 to T4.

What the kernel can check about a prelude, it checks. Only a trusted prelude
declares axioms and builtins (`UntrustedAxiom`, `ReservedKernelName`), and only
its declarations receive native operations and native literal layouts: a
module that declares `Nat.add` gets an ordinary definition. A native literal
layout refuses a sealed family. No prelude declaration's type names an atom, since
`LifetimeEscapes` refuses any global whose type does.

A test keeps a golden inventory of the bundled prelude's trusted surface: every
axiom and builtin with its declared type, every native operation, every native
literal layout, and every sealed family. A change to any of them changes the
golden file, and is reviewed against the obligations. The bundled prelude's
axioms are `Quot` and `Quot.sound`, its builtins `Quot.mk`, `Quot.lift` and
`Quot.ind`, its native operations the Nat ones listed below, and its one native
literal layout `Nat`'s. It declares no sealed family.

### Natural numbers

At the end of prelude loading, a declaration named `Nat` is accepted for
literal syntax only if it is exactly an unsealed Type-valued unary inductive
with the no-confusion constructors:

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
the host equation is obligation T5. Application never consults a global name
registry, so later same-named source cannot acquire the equation.

Subtraction truncates at zero. Division by zero returns zero, modulus by zero
returns the dividend, and `pow(a, 0)` returns one. `pow` and nonzero
`shiftLeft` reject exponents or counts above `2^24`; sufficiently large
`shiftRight` returns zero without allocating an enormous intermediate value.

Applied to anything but two literals, an operation runs its declared body only
when every literal argument is at most the unfolding limit, `2^8`. A body
unfolds one layer per unit of its recursion argument, and the kernel does not
know which argument that is, so the limit bounds each literal argument.
Otherwise the application is a neutral headed by the operation itself. It is
blocked on what its non-literal arguments are blocked on, and rigid when they
are not blocked; it reruns when they are solved, and uses the host equation
once its arguments are literals. Two such neutrals are equal when they apply
the same operation to convertible arguments. Conversion therefore never
unfolds an application on a literal above the limit: `Nat.add(x, 2000)` is not
definitionally `Nat.succ(Nat.add(x, 1999))`. This loses definitional equations
and adds none, so it can only reject a program that relied on one. Small
offsets such as `Nat.add(n, 1)` still unfold. The limit stays below the depth
at which the host stack overflows: checking `Nat.mul(n, 512)` already exhausts
a 1MB stack.

The bundled prelude defines and accelerates `add`, `sub`, `mul`, `pow`, `beq`,
`ble`, and `blt`. Other table entries become available only if the selected
trusted prelude declares their exact validated definitions.

### Strings

String literals require an optional validated bootstrap layout:

- a Type-valued `Char`;
- `List(Char)` with exact `nil` and `cons` constructors;
- an eta-eligible one-field `String` with constructor `String.mk` storing
  `List(Char)`;
- a closed checked `Char.ofNat : Nat -> Char`;
- none of `Char`, `List` and `String` sealed.

The kernel trusts the exact `Char.ofNat` identity to map Unicode scalar values
injectively. A string evaluates to `String.mk` containing a packed scalar list.
The outer `String` remains constructor-headed, preserving structure eta. List
matching decodes one `nil` or `cons` layer at a time. Two packed lists compare
as their decodings do: where their scalars agree the decoded characters are the
same, where they differ the characters `Char.ofNat` gives are compared, and a
list that ends first is `nil` against `cons`. So two distinct literals are
apart when one ends first or a character where they differ is apart, as it is
when `Char.ofNat` builds a constructor around its scalar. The bundled prelude
does not currently install this layout.

### Equality

At the end of prelude loading, the prelude's declaration named `Eq` is
validated as the equality family: an unsealed

```text
Eq {u: Level}{S: Lifetime}(A: Type { level = u, scope = S }) indices (x: A)(y: A) : Prop { scope = S }
Eq.refl (x: A) : Eq(A, x, x)
```

with its binders in one group. A match's named equation is stated with it, and
with nothing else: a module's own `Eq` is not consulted. Where there is no
validated `Eq`, because the prelude declares none, declares another, or is
still loading, so that its own declarations are being checked, a named
equation is `MatchEquationUnavailable`, with the reason; nothing else about the
prelude changes. The family is checked, not trusted, so it adds no obligation.

## Value identity

Fast equality keys may prove definitional equality, so every value component
used to build a key must be semantically identifying. A Pi, lambda, match or
`scope` node carries an identity of its own. Whoever makes a node allocates it
a fresh one: the elaborator for each node it elaborates, the inductive checks
for a family's and a constructor's type, and the kernel for a node it
fabricates, such as a structure-eta projection or a proof's eta-lambda.
Whoever rebuilds a node keeps its identity, as the checker's residual does, so
a term checked and later evaluated keeps it. Two nodes therefore share an
identity only when one rebuilds the other. A span only locates a node, so two
nodes written at one span are still two. Syntax the elaborator duplicates is
as many nodes: a selector's result type, its field's type as written under
`let`s binding the earlier fields it mentions, is elaborated once as its
header's codomain and once as its match's motive. A wildcard's expansion
copies its body afresh for each case, every node in it with a fresh identity
(`CoreAst.freshCopy`). Captured values, in binding
order, are part of closure identity, and a Pi's key counts its binders, so a
Pi that drops leading binders its remainder does not depend on keeps its
node's identity. Packed keys include the codec, canonical payload, and packed
type.

A value's key, its dependency set, and whether a mismatch of its key is
conclusive are computed when it is built, from its own components and its
children's, which were computed when they were built. So none is computed by a
walk, and publishing a global, materializing and deciding an equation by key
cost the same however deep their values. A key over host data rather than
values, a packed literal's payload or a kind's or lifetime's variable set, is
hashed by a loop when first read: a packed list's tail is built for each layer
decoded, and hashing each as it is built would make decoding quadratic. An
application's key mixes its head, its arguments less its evidence ones (see
[Evidence arguments](#evidence-arguments)), their count, and a constructor
application's type.

A key only accelerates conversion. Equal keys must be convertible, and a key
mismatch that conversion treats as conclusive must be unconvertible. The
key-coherence assertion (`-Draccoon.keyAssertions`, on by default and off for
benchmarking) runs the conversion rules beneath every equation a key decides
and fails loudly on disagreement. Within one outermost check each pair of
values is checked once, so the check costs one structural pass however much
its values share. It runs on a work stack of its own: an equation a key decides
while the check runs is given the key's verdict at once, as with no check
running, and its own check is pushed there, so each step decomposes one layer
and no check uses host stack for depth. Only atoms whose key is their identity are
exempt: variables (by id), constants and constructor heads (by name), and
levels (by normal form). Kinds and lifetimes key by their normal forms too, an
atom by its id, which its `scope` term's node identity determines, but
their conversion rule compares the normal forms itself, so the assertion checks
their keys. A sort's key mixes in its level, kind and scope, and a Pi's key its
closure kind, closure scope, mentioned scope and binder modes, explicitly
rather than through its node and captures.
The kernel singletons `Level`, `Kind`, `Lifetime`, their classifier and `Large`
are equal only to themselves, which object identity decides before any key is
read.

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
   zero-index singleton families, sealed or not.
8. Recursive calls are accepted only from genuine structural descent.
9. Axiom and quotient values are allowed to remain closed neutrals.
10. Native equations and literal layouts are installed only by a selected
    trusted prelude and remain attached to validated values, not global names.
11. A value key never decides an equation the conversion rules would decide
    differently.
12. Whether a sort is `Prop` or a type is a proposition has one definition.
13. A term's type never depends on where it stands: checking is synthesis
    followed by definitional equality with the expected type.
14. Sorts, levels, kinds and lifetimes are built only by the kernel's own sort
    former and forms; no global, builtin or prelude declaration names one.
15. Every checked term has a type, except where the checker's position rules
    admit otherwise: a sort parameter as the type of a binder at a site that
    may bind it, an expression of a sort parameter where one is expected, a
    large reference at an application head, and a large type as a
    declaration's type.
16. Kinds and lifetimes exist only in normal form, so their structural
    equality is definitional equality; no two of them are apart.
17. Proposition classification is fixed when a type is formed; substituting
    data levels cannot change it. Proof-valued closures are unrestricted.
18. A family's kind and scope are declared, never derived. An instance's sort
    is the declared sort under its arguments, and its declared kind and scope
    contain whatever a value of it holds or carries in its type; its scope names
    every lifetime parameter. Each family of a mutual block is checked against
    its own declared sort, and a sibling is read by its declared sort.
19. A function type's closure and mentioned scope are part of its identity
    and its sort; the mentioned scope is what its binder types' and codomain's
    captures contribute, by the rule a lambda's captures follow. A lambda's
    closure is written or derived from its captures' types and the lifetimes
    they hold alone, never from where the lambda stands, and its residual
    carries a derived field as those captures.
20. An atom is opened only by a `scope` term and is determined by that term's
    node identity, in checking and evaluation alike. It is never refinable and
    never abstracted, and no type the checker synthesizes, checks against or
    binds has a sort whose scope names it outside its `scope`; evaluation never
    checks this. A value, a type's included, holds an atom its type's sort
    does not name only inside a blocked computation or a proof.
21. A type is linear exactly when its kind is not `Kind.unr`, and one function
    decides it. Every local bound at a linear type by a lambda, a definition's
    parameters, a `let` or a pattern, `_` included, is used exactly once on
    every path through its binder's checked extent, and no global has a linear
    type.
22. No term whose type is a sort or a proposition contains a subterm of linear
    type, and no implicit binder of linear type is forced.
23. Outside a sealed family's module, no checked term names its constructors
    or selectors, matches on a value of it, forces an implicit through its
    constructors' fields, or discharges evidence with its constructors. Sealing
    never changes what conversion, coverage, apartness, structure eta or proof
    reconstruction decide.
24. Only a trusted prelude declares axioms, builtins, native operations and
    native literal layouts. That trusted surface keeps the audited obligations
    T1 to T5; every other prelude declaration is checked as one in any module.
25. An evidence argument is either supplied and convertible with its
    proposition evaluated at the application, or discharged by a constructor
    applied to fields read off that proposition, whose result type is
    convertible with it; discharge invents no field, and reads no expected type
    and no hypothesis beyond what the proposition holds. Evaluation binds the canonical proof of the same
    proposition, and evaluates the proposition only when that proof is looked
    at. An application's dependencies, key and conversion skip its evidence
    arguments, which its head and other arguments determine.
26. A value's dependencies, key and key conclusiveness are computed when it is
    built, from its children's; no walk over a value computes them.
27. An implicit is projected only through a value's type, sorts, function
    types' closures and independent domains, codomains and results, a proof's
    proposition, no-confusion constructor fields and the arguments of a
    family's application or of a type former's single-group application,
    never through a blocked computation's arguments. A type former names each
    of its lifetime parameters in its declared scope.
