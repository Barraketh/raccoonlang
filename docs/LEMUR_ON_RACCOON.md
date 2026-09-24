# Lifetimes, linear types and scopes

This document specifies three additions to Raccoon: lifetimes, a prelude type
whose values are sets of atoms, carried as a bound on every sort; one `scope`
construct that opens a fresh atom; and linear and sealed inductive families.
Each section states the syntax, the rules, and the diagnostic each rule
raises; section 9 collects the diagnostics. Where this document is silent on
a case, the implementation stops and reports the gap rather than choosing.

## 1. Syntax

```text
Sort         ::= Sort(u) | Sort(u) @[S, ..., S]    -- each S a term of type Lifetime; the bound
                                                    --   is their union; Sort(u) means Sort(u) @[]
               | Type [@[S, ..., S]] | Prop [@[S, ..., S]]   -- at Level.one and Level.zero
Binder       ::= (x: C) | {x: C}                    -- explicit or implicit
               | (lin x: C) | {lin x: C}            -- the marker of §3.5; C a sort, or a
                                                    --   function type whose codomain is a sort
Function     ::= [lin] [@[S, ..., S]] Group         -- Group: one binder group as today, as in
                                                    --   (x: A)(y: B) -> C, (x: A) -> (y: B) -> C
                                                    --   or A -> B -> C; an omitted bound is @[]
Lambda       ::= fun Binder ... : B => e              -- closure kind derived (§3.4)
Term         ::= ... | scope l => e
Decl         ::= [sealed] [linear] inductive D (params) indices (indices) : Sort(u) [@[S, ..., S]]
               | [sealed] [linear] struct   D (params) indices (indices) : Sort(u) [@[S, ..., S]]
```

`lin` before a function type is its closure kind; a lambda has no keyword,
and its kind is derived or taken from the arrow it is checked against (§3.4).
`lin` inside a binder is the marker of §3.5; it may stand on a binder of a
function type, a lambda, a definition or a family parameter, and never on a
constructor field or an index. `@[` and `]` are tokens; a bound is written
`@[S, ..., S]`, a bracketed comma list of terms of type `Lifetime` whose union
it denotes, with `@[]` the empty bound, in the same spelling after a sort and
before a function type's binders. The closing bracket ends the bound, so
nothing after it is ever read as an argument to it. `lin` and a bound prefix
a whole group and are a parse error before a later domain of the same unparenthesized chain; a
nested group is parenthesized, `A -> (lin B -> C)`. There is no other literal
syntax for a lifetime: in term position a lifetime is `Lifetime.empty`, a
local, or `Lifetime.union(e, e)`. In this document `{}` and `{l, m}` are prose
for the sets a bound denotes. `scope l => e` extends as far to the right as a
lambda body does. `_` binds an anonymous local, in a match pattern as
elsewhere.

## 2. Lifetimes and bounds

**2.1 The `Lifetime` type.** `Lifetime` is a first-class native type, as
`Level` is. The bundled prelude declares `Lifetime : Type`,
`Lifetime.empty : Lifetime` and `Lifetime.union : Lifetime -> Lifetime ->
Lifetime`. It has no constructors: a `match` on a `Lifetime` value is
`NonInductiveMatch`, as for `Level`. An atom is opened only by `scope` (§4.1).
A `Lifetime` value is unrestricted and may be stored, returned and passed like
any value.

**2.2 Normal forms.** The native normal form of a `Lifetime` value is the set
of its atoms together with the set of neutral `Lifetime` values it unions in:
`union(empty, x) = x`, `union` is associative, commutative and idempotent,
and two lifetimes are definitionally equal when their normal forms are equal
sets. `S ⊆ S'` holds when every atom and every neutral of `S` is one of `S'`.
No two lifetimes are ever apart, so refinement never prunes a branch on a
lifetime equation (§6.2), and an equation between two lifetimes is never
refutable, which is why no axiom may mention `Lifetime` (§7.3).

**2.3 Sorts.** `Sort(u) @[S]` is the sort of types at level `u` whose values
depend on at most the atoms in `S`; `S` is a term of type `Lifetime`.
`Sort(u) @[S] : Sort(Level.succ(u))`, `Type @[S]` is `Sort(Level.one) @[S]`
and `Prop @[S]` is `Sort(Level.zero) @[S]`. Levels are as today; the bound is
a second component beside the level and the two never interact. A type's sort
carries its bound, given by §2.4, and the type checks against `Sort(u) @[S]`
exactly when that bound is `S` (§2.6).

**2.4 Bound of a type.** `bound(T)`, the bound component of `T`'s sort, is
given by `T`'s shape; a neutral value carries its type, so the last row reads
it off:

| `T` | sort of `T` |
|---|---|
| `Sort(u) @[S]` | `Sort(Level.succ(u)) @[]` |
| `[lin] @[S] (x1: A1) ... (xn: An) -> B` | `Sort(imax as today) @[S ∪ bound(B)]`, less every neutral that mentions a binder of the group and no other local or atom; the domains contribute nothing |
| a family instance `D(p*, i*)` | `Sort(u) @[S]`, the declared classifier of §5.1 under `p*` and `i*`, and nothing else |
| any other neutral type | the bound its type states: a type variable `A: Sort(u) @[S]`, or `F(e*)` for a local `F`, states `S` under the arguments; an `opaque def` or `axiom` application and a blocked `match` state the bound of the declared result or motive |

`Level`, `Lifetime` and every builtin type are at `{}`. "Less" removes the
neutrals whose only locals are binders of the group, whatever the binders'
types: `(l: Lifetime) -> Lease(l) -> A` has bound `bound(A)`, and so does
`(p: Lifetime × Nat) -> Lease(p.fst) -> A`. A bound naming such a neutral
inside a union is read after that removal. A neutral that mentions a binder
`xi` of the group and also another local or an atom,
`(b: Bool) -> Lease(g(b, m))`, can be neither kept, since it names `xi`
outside its group, nor removed, since its value may be `m`; the function type
is `LifetimeEscapes(xi)`. A neutral that mentions no binder is kept.

A family instance's bound is its declaration's under the arguments and is not
read off the arguments' values. It therefore commutes with substitution: a
generic `T(q)` for a neutral `q: Lifetime × Nat` and its instance `T((l, 0))`
are at the same declared bound under their arguments, and a family whose
values are confined to a lifetime its arguments carry says so in its
declaration (§5.1). A family declaration has no removal: its declared bound
may mention only its parameters and indices.

**2.5 Conversion is exact.** Two types are definitionally equal when their
normal forms are: same former, equal parts, equal levels, equal closure kinds,
equal markers on binders, equal bounds as sets. `ValueKey` includes bounds,
closure kinds and markers, and keys an atom by the identity of the `scope`
term that opened it (§4.1).

**2.6 Bounds are exact.** Checking a term against an expected type requires
the synthesized type to equal the expected one, bounds included; a bound that
differs at any position is `TypeMismatch`. Bounds are not cumulative, for the
reason universes are not: an implicit is re-derived from its argument's own
type whenever an application is evaluated, so a value whose type stood at a
larger bound than its own would make evaluation derive a different bound
variable, or a different type, than checking did, and a generic definition
could then return a scoped value at an unscoped type.

Inclusion is tested in exactly two places, both where something is formed
against a bound and takes that bound as its own: a lambda checked against a
function type (§4.3), and a family's declaration against its fields (§5.1).
Either failure is `BoundExceeded`. A function value `f` is lifted to an arrow
at a larger closure bound by `fun (x: A): B => f(x)` checked against that
arrow, which §4.3 admits whenever `f`'s bound is within the arrow's. A type
has no such lift; a position that must accept types at several bounds takes a
bound variable (§2.7).

**2.7 Bound polymorphism.** A binder `{S: Lifetime}` is a bound variable, as
`{u: Level}` is a level variable, and is forced like any implicit: through a
family parameter or index of a later explicit argument, or, as a level is
forced through `Sort(u)`, through the bound of a sort or the closure bound of
a function type that projection reaches. Those are two projection steps beside
the existing ones, from a sort to its bound and from a function type to its
closure bound. Each recovers a bound variable only when the bound at that
position is exactly that variable, as `LevelOffset` recovers a level only
from a single atom, so `{A: Type @[S, m]}` does not force `S`. A bound
variable is solved where it forces: to `bound(A)` for a binder
`{A: Type @[S]}` and to the argument's closure bound for `(f: @[S] A -> B)`.
Every other occurrence must then equal that solution. Since bounds are exact
(§2.6), the solution is canonical, never chosen among alternatives, and
evaluation re-derives the same one. A bound variable no argument reaches is
`NonForcedImplicitParam`.

Every polymorphic prelude declaration carries a bound variable beside each
type parameter and for the sort in each type-family parameter's codomain, as
`motive: A -> Sort(v) @[Sm]` in `Eq.subst`, and every higher-order one a
closure-bound variable per function-typed parameter; a definition that omits
them accepts only arguments at `{}`.

```raccoon
inductive List {S: Lifetime}(A: Type @[S]) : Type @[S]
 | nil : List(A)
 | cons (head: A) (tail: List(A)) : List(A)

inductive Eq {u: Level}{S: Lifetime}(A: Sort(u) @[S]) indices (x: A)(y: A) : Prop @[S]
 | refl (x: A) : Eq(A, x, x)
```

`List(Lease(l))` forces `S := {l}` and is `Type @[l]`; `List.nil(A)` forces
`S` through its explicit `A`. A second binder at the same variable,
`{S}{A: Type @[S]}{B: Type @[S]}`, requires `bound(B)` to equal `bound(A)`; a
family that holds both takes a variable for each and declares their union,
`Type @[S, T]`. A proposition obeys §5.1 like any family: `Eq` is at
`Prop @[S]` because `refl` holds an `A`, and `Eq(Lease(l), a, b)` is at
`Prop @[l]`. A closure that captures a proof of it can match the proof and
recover the lease, so the proof's type must count `l` in the closure's
capture bound (§4.3).

## 3. Linearity

**3.1 The root.** An inductive or struct family marked `linear` is linear by
fiat. Every value of such a family is used exactly once: introduced by its
constructors and consumed by `match`, and by nothing else. §5.1 says which
families must carry the marker and which may not.

**3.2 `linear(T)`.** Read off the type's shape, never off a family's fields.
The first row that applies decides:

| `T` | `linear(T)` |
|---|---|
| any `T : Prop` | no, whatever its shape, a `lin` function type into a proposition included |
| `lin ... -> B` | yes |
| `... -> B` without `lin` | no |
| `D(p*, i*)` | marked `linear`, or an argument at one of `D`'s `lin`-marked parameters may be linear, as §3.5 decides for a binder |
| `Sort(u) @[S]`, `Level`, `Lifetime` | no |
| a type variable, or `F(e*)` for a local `F` | yes if the binder is marked `lin`, else no |
| an `opaque def` or `axiom` application | no |
| a blocked `match` | yes if any reachable branch's body is linear |

An `opaque def` or `axiom` application converts only with itself, never with
its body, and no `match` opens its values, so nothing of its type is ever
consumed as a token. `Quot(A, r)` is such an application, and its unmarked `A`
already refuses a linear type (§3.5).

**3.3 The ledger.** Every local of linear type bound by a lambda, a
definition's parameters, a `let`, or a match pattern, `_` included, is used
exactly once within the extent of its binder, counted along each path through
that extent that takes one branch at every `match`. A lambda's body lies on
those paths at the lambda's position, so a closure that uses a captured linear
local uses it on every path through its body. A use is any occurrence.
No use on some path is `LinearUnused(x)`, which is also what a wildcard over
a linear field reports; a second use on some path is `LinearReused(x)`. A
match with no branch ends every path through it and so uses every linear
local live at it; no evaluation reaches it. Whether a local is tracked is
decided once, from its type as it reads at its binder; refinement in a branch
never changes it. Locals of unrestricted type are not tracked. Globals are
never tracked: a `def` or `opaque def` whose type is linear is
`LinearGlobal`, and an axiom is §7.3's.

Types and proofs hold no tokens: a term whose type is a sort or a
proposition, whether a type in a type position, a type computed as a value,
or a proof, may not contain a subterm of linear type (`LinearInType(e)`). A
type or a proof is never consumed as a token, so a token inside one would be
copied with it, or dropped without its module's consent, a proof never being
run. Consequently no type contains a linear local, and a linear implicit
binder is never forced, since forcing reads types. Facts about a token are
stated about its indices, which are unrestricted. A `decreases` clause is not
a use: it may name a linear parameter as the structural argument or measure
it.

**3.4 Closures.** A lambda's closure kind, unrestricted or linear, is derived
as its capture bound is (§4.3): in synthesis the lambda is linear exactly when
its body uses a linear local bound outside it, and checked against a function
type it takes that arrow's kind. Each such use counts as one use by the
lambda, and applying a linear closure consumes it. The body of an unrestricted
closure may run any number of times, so a use of an outer linear local inside
one is `LinearReused(x)`. A lambda in argument position takes its closure kind
from its parameter's type whenever that type is a function type, whatever
implicits it mentions, and takes that arrow's closure bound when the bound
mentions no implicit that this argument or a later one forces; otherwise its
closure bound is the derived one (§4.3). The argument is then verified
against its parameter like any other. Conversion compares closure kinds
exactly: an unrestricted function value is not accepted where a `lin`
function type is expected, and `fun (x: A): B => f(x)` checked against that
arrow is how one is lifted. The eta-adapter, which wraps a function value in a
lambda to fit an expected function type with fewer implicit binders, builds
an ordinary lambda for this section and §4.3: the lambda captures the wrapped
value, so a linear value is wrapped only at a `lin` arrow and the wrapper's
bound covers the value's. A definition's own function type is never `lin`: a
definition is a global, and its binder group is applied all at once, so no
partial application holds a linear parameter.

**3.5 Type variables and the marker.** A binder whose classifier is a sort,
or a function type whose codomain is a sort, may be marked `lin`. An unmarked
binder whose classifier is such a type as instantiated at the call, a
constructor field `(fst: A)` at `A := Type` included, may be instantiated only
at a type `T` with `linear(T)` no, else `LinearInstantiation`, decided when an
explicit argument or a forced implicit's solution is checked against the
instantiated classifier. An unmarked higher-kinded binder may be instantiated
at `F` only when `linear(F(x*))` is no for fresh type variables `x*` that
carry the markers of `F`'s own binders: inside the body, an application of `F`
passes a linear type only at a marked binder of `F`, which the marked fresh
variable stands for. A marked binder may be instantiated at any type, and a
local whose type is the marked variable, or an application of it, is tracked.
The marker is part of the function type's identity (§2.5): a function type
whose binder is marked and the same one unmarked are two types, and a
lambda's binder marker must agree with the arrow's (`TypeMismatch`).

There is no multiplicity polymorphism: a function over `{lin A}` consumes its
`A`-typed arguments in every instantiation, so a library function that must
serve both linear and unrestricted elements exists once, in the consuming
form, and a lambda passed to it takes the kind its parameter states (§3.4).
This is a deliberate cost; the intended linear families are tokens and leases,
not containers.

**3.6 Constructors and selectors.** A constructor application whose family
instance is linear is linear and is consumed by `match`, which releases the
fields to the ledger. A struct's selector is a `match`, so applying one to a
linear value consumes it as that `match` does. A struct generates the selector
of a field only when every other field's type is unrestricted with each
`lin`-marked parameter read as possibly linear, the opposite reading from
§5.1's: the selector is one definition for every instance, and would
otherwise drop a token at some of them. Structure eta remains a rule of
conversion alone and consumes nothing; a sealed family has none (§7.1). A
constructor's implicit family parameters are inferred or explicit exactly as
today.

## 4. Scopes

**4.1 Opening a lifetime.** `scope l => e : T` when `e : T` under
`l: Lifetime`; that `T` does not name the new atom, bound included, is §4.2's
check at the `scope`'s own position, where `l` is out of scope. This is the
only construct that introduces an atom. `scope` synthesizes when its body
does and checks by checking its body against the expected type. Checking and
evaluation alike bind `l` to a lifetime holding one atom unique to this
`scope` term, identified by the term's node identity; the body is checked
with `l` denoting that atom, not a neutral. Two `scope` terms are two atoms,
one term evaluated twice is one atom; the construct denotes the value of `e`
and is otherwise erased. An atom names a `scope` term, not an entry into it:
a recursive call re-enters the same atom, which confinement (§4.2) makes
harmless to the checker. An atom is not a local: it is never linked by
refinement (§6.2) and never abstracted. In printed output an atom is spelled
as its binder, and quoting writes it as its `scope` binder's local; a `scope`
term keeps its node identity through quoting and is never given a synthetic
one, which would open a different atom.

**4.2 Outside its scope an atom cannot be named in a type.** A type whose
value mentions an atom whose `scope` binder is not in the ambient context is
`LifetimeEscapes(l)`; a `scope` term encloses a position exactly when its
binder is in that position's context. The check is made on every type the
checker synthesizes for a term or checks a term against, on every argument or
reconstructed implicit at a binder whose classifier is a sort, and on the type
of every local at its binder; the dependency set a value carries answers it.
A `Lifetime` *value* is not checked: it may be returned from its scope, stored
and passed, and only forming a type from it outside the scope is refused.
Evaluation never makes this check: a value may carry an atom anywhere, and a
residual records nothing of the check, since it keeps the `scope` term and
re-evaluates it.

Confinement is by bound. A linear value whose type's bound contains `l`
cannot leave the scope and cannot be dropped, so it is consumed inside it;
§5.1's rule that a linear family names its `Lifetime` parameters in its bound
is an aid to that, not a second mechanism. A value computed under `l` whose
type neither mentions `l` nor is bounded by it may leave, and in particular a
closure that captures the `Lifetime` value `l` itself, such as
`fun (u: Unit): Lifetime => l`, has a type that says nothing about `l` and
may leave and be applied later, yielding the atom as an inert value.

**4.3 Capture bound.** A lambda's derived capture bound is the join, over
every local bound outside it that occurs in its body as the checker fills it,
occurrences in types and reconstructed implicits included, of `bound(type of
the local)`. Checked against a function type, it must be a subset of that
type's bound (§2.4), the closure bound `S` joined with the codomain's, else
`BoundExceeded`, and the lambda then takes `S` as its closure bound (§2.6); in
synthesis, and when `S` is an unsolved bound variable (§2.7), its closure
bound is the derived one.

**4.4 Lifetime binders elsewhere.** A binder of type `Lifetime` in a function
type, a lambda, a definition, a family or an implicit introduces no atom; it
abstracts over a lifetime some caller supplies, which may be `{}`. A resource
operation is an ordinary definition:

```raccoon
def withLease {S: Lifetime}{lin A: Type @[S]}{Sk: Lifetime}
    (k: lin @[Sk] (l: Lifetime) -> Lease(l) -> A): A :=
  scope l => k(l, Lease.mk(l))
```

`withLease` belongs to `Lease`'s module, since it applies the sealed
constructor (§7.1). `A` is bound outside `k`'s lifetime binder, so no value
confined to `l` can be returned; `S` lets the result be a type confined to an
enclosing scope, and `Sk` lets the callback capture values of such types. `A`
is marked so that a callback may return a token, and `k` is `lin` because
`withLease` applies it once; the one definition then serves callbacks and
results of both kinds (§3.5), and a `fun` passed for `k` takes its kind
(§3.4). `A` is forced through `k`'s result, which depends on none of `k`'s
binders, `S` through `A`'s classifier and `Sk` through `k`'s closure bound
(§2.7).

## 5. Declarations

**5.1 Families.** The family's classifier is `Sort(u) @[S]`, declared and
never derived; writing no bound declares `@[]`. `S` may mention only the
family's parameters and indices. For each constructor, `S` at that
constructor's result indices must contain the join of its fields' bounds, and
a family marked `linear` must also name every parameter and index of type
`Lifetime`; the join is computed for that check alone, which reports
`BoundExceeded` naming the field or parameter it omits. An instance is at
exactly `S` under its arguments (§2.4), so a family confined to a lifetime it
is indexed by says so in its bound. A lifetime that a parameter carries
inside another type, as `p: Lifetime × Nat` does, is the declaration's to
name, `@[p.fst]`; the checker verifies only the parameters and indices of
type `Lifetime`.

```raccoon
sealed inductive Lease (l: Lifetime) : Type @[l]          -- cannot leave scope l
 | mk : Lease(l)

sealed linear inductive Tok (l: Lifetime) : Type @[l]     -- @[l] is required: Tok is linear
 | mk : Tok(l)

inductive Holder {S: Lifetime}(A: Type @[S]) : Type @[S]  -- the field's bound must be declared
 | mk (held: A) : Holder(A)
```

A caller may instantiate `l` at `Lifetime.empty`; `Tok(Lifetime.empty)` is
then a linear value confined to no scope, which `Tok`'s module mints only if
it chooses to. A capability must be sealed to confine anything: a lifetime
value may leave its scope (§4.2), and an unsealed `Lease.mk` applied to it
where it is a neutral forges a lease for a scope that has closed.

Linearity is declared, as the bound is. Reading every `lin`-marked parameter
as unrestricted, a family some constructor of which has a field of linear type
must be marked `linear`, else `UnmarkedLinearField` naming the field; the
check reads each field's declared type once, and a sibling in a `mutual` block
by its marker, so no fixed point is computed. A family whose fields are linear
only through a marked parameter needs no marker and is linear at the instances
§3.2 names, which may be conservative when the parameter occurs only where it
holds no value, such as a function domain. The `linear` marker on a family
whose sort may be `Prop`, `Prop` itself or `Sort(u)` at a level not known to
be positive, is `LinearProp`: proofs are unrestricted. A parameter binder
whose classifier is a sort may carry the `lin` marker of §3.5,
`(lin A: Type @[S])`; the marker is part of the family's identity and is
exported by sealing (§7.1). Strict positivity, uniform parameters, `mutual`
blocks and structs are unchanged.

## 6. Matching

**6.1 Consumption.** Matching a scrutinee of linear type consumes it once and
releases the constructor's fields to the ledger, each at the branch's extent;
a wildcard binds an anonymous local, so one over a linear field is
`LinearUnused` (§3.3). Coverage, `returning`, the default motive and the
`Prop` elimination restriction are unchanged; each branch is checked against
the motive under the branch's equations.

**6.2 Refinement over `Lifetime` indices.** Index equations between
`Lifetime` values are ordinary index equations over the native normal form,
under the rule levels already follow: a neutral `Lifetime` local alone on one
side, not occurring in the other, is linked to the other side, the later-bound
to the earlier-bound when both are locals; an atom is not a local and is never
linked; every other equation, a union on both sides included, is stuck, and
none is apart (§2.2).

## 7. Sealing

**7.1 Sealed families.** A family marked `sealed` exports its head,
parameters, indices, classifier and markers, and not its constructors or its
selectors. A module is a `.rac` file. Outside the declaring file, a term that
applies one of its constructors, matches on a value of it, selects a field, or
names a constructor by `.short` form, is `SealedConstructor`. The constructor
names still resolve, so that every such use reaches this diagnostic and not an
unbound-name error; outside the file they are otherwise invisible. A term the
checker reconstructs, an implicit argument or a motive, may name a sealed
constructor and is exempt, but forcing an implicit through a sealed
constructor's field compiles only inside the declaring file; elsewhere the
implicit is `NonForcedImplicitParam`, since reconstructing it would read the
field. A sealed family is never structure-eta eligible: eta would let a
`match` in its module open, as a constructor application, a neutral of it that
the module never built, such as an axiom's result or a blocked computation.

**7.2 What the checker knows.** Sealing restricts what a program may write,
not what the checker knows. `linear`, `bound`, coverage, apartness and the
conversion of values are computed from the full declaration in every module,
with no eta for a sealed family (§7.1). An `opaque def` is the sealed form of
a definition and is unchanged: its body is checked and does not unfold after
publication, in any module. `bound` of its application is the bound of its
declared result (§2.4), and `linear` of a type-valued application is no
(§3.2).

**7.3 Axioms.** Outside the trusted prelude, an `axiom` whose type contains,
in its value, a type `T` with `linear(T)` yes, a `lin` marker or closure
kind, or `Lifetime`, which any bound other than `@[]` mentions, is
`AxiomMintsToken`. An axiom's result is a neutral, so without this rule an
axiom could consume a token without its module,
`axiom eat {lin A: Type}(x: A): Unit`, including one held by a family `W`
whose field is a token; or, since no two lifetimes are apart (§2.2), state
the consistent `axiom lifeEq (a: Lifetime)(b: Lifetime): Eq(Lifetime, a, b)`,
along which a `match` carries a `Tok(l)` out of its scope as
`Tok(Lifetime.empty)`. Sealing needs nothing more: an axiom may still yield a
neutral of a sealed family, but no `match` opens it (§7.1), so every
constructor-headed value of a sealed family was built in its module. The
bundled prelude declares no linear or sealed family, marks no parameter
`lin`, and puts every declaration at bound `@[]` or at a bound variable; a
library that needs a container of tokens declares its own.

## 8. Interactions

- **`Prop`.** Proofs are unrestricted and proof irrelevance is unchanged. A
  proof holds no token (§3.3). A proposition carries a bound like any family
  (§2.7), may mention a lifetime, and §4.2 applies to it.
- **Levels.** Level polymorphism and `imax` are unchanged; a bound rides
  beside the level, is forced the same way (§2.7), and is never affected by
  level arithmetic.
- **Implicit reconstruction.** A recovered `Lifetime` argument is subject to
  §4.2 wherever it enters a type.
- **Residuals.** A checked residual carries every filled closure kind, bound
  and marker, a lambda argument's included (§3.4). Implicit arguments stay out
  of residuals and are re-derived from the arguments' types when a residual is
  evaluated, as today; exact bounds (§2.6) are what make that derivation agree
  with checking.
- **Runtime.** The interpreter makes none of the checks of `scope`, sealing
  and linearity. It binds a scope's `l` to its atom and represents a
  `Lifetime` value as a set of atoms keyed as in §2.5, since a program may
  store, union and return one. Its `Lifetime.union` and the checker's normal
  form of §2.2 are one implementation. An atom identifies a `scope` term, not
  an entry into it (§4.1), so nothing at run time may key a resource by atom.

## 9. Diagnostics

```text
LinearUnused, LinearReused, LinearInType, LinearInstantiation,
UnmarkedLinearField, LinearGlobal, LinearProp,
LifetimeEscapes, BoundExceeded, SealedConstructor, AxiomMintsToken
```

`TypeMismatch`, `NonForcedImplicitParam` and `NonInductiveMatch` are the
existing diagnostics and gain the cases named above. Every rule above is a
test obligation: one program the rule admits and the smallest mutation
reaching its named diagnostic and no earlier one.
