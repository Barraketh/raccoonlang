# Lifetimes, linear types and scopes

This document specifies three additions to Raccoon. A sort gains two
parameters beside its level: a kind, which says whether each value of its
types is used exactly once, and a scope, the set of atoms its types' values may
depend on. Levels, kinds and lifetimes are second-class: they parameterize
sorts, families and definitions, but they are not types, and no program
computes with them. One `scope` construct opens a fresh atom. And a family may
be sealed to its module. Each section states the syntax, the rules, and the
diagnostic each rule raises; section 9 collects the diagnostics. Where this
document is silent on a case, the implementation stops and reports the gap
rather than choosing.

## 1. Syntax

```text
Sort      ::= Sort { Field, ..., Field }         -- level required
            | Type [{ Field, ..., Field }]       -- level is Level.one
            | Prop [{ Field, ..., Field }]       -- level is Level.zero
Field     ::= level = e | kind = e | scope = e   -- e a level, kind or lifetime expression (§2.2)
Closure   ::= { Field, ..., Field }              -- kind and scope only
Function  ::= [Closure] Group                    -- Group: one binder group as today, as in
                                                 --   (x: A)(y: B) -> C, (x: A) -> (y: B) -> C
                                                 --   or A -> B -> C
Lambda    ::= fun [Closure] Binder ... : B => e  -- an omitted closure field is derived (§4.3)
Term      ::= ... | scope l => e
            | match e returning T with Case ...  -- returning required (§8)
Decl      ::= [sealed] inductive D (params) indices (indices) : Sort
            | [sealed] struct   D (params) indices (indices) : Sort
```

`Sort`, `Type` and `Prop` are the sort formers. `Sort` is not a function, and
`Sort(u)` is not a term. A sort's parameters are supplied by name, in any
order: `level`, `kind` and `scope`. An omitted `kind` is `Kind.unr` and an
omitted `scope` is `Lifetime.empty`. That is what the shorter spelling means,
not something inferred. `Type` and `Prop` fix the level, so `level` in their
field list is a parse error, as it is in a closure. A field list is nonempty,
and an unknown or repeated field is a parse error. So `Type` is
`Sort { level = Level.one, kind = Kind.unr, scope = Lifetime.empty }`, and
every program written without fields keeps its meaning.

A field's value is a level, kind or lifetime expression (§2.2), elaborated with
that parameter's namespace open: `level = succ(u)`, `kind = lin`,
`scope = union(a, b)`. A name in a field resolves to a local first, then to one
of the field's forms, and only then by ordinary resolution. So inside
`namespace Nat`, `level = succ(u)` still means `Level.succ(u)`. In this document
`{}` and `{l, m}` are prose for the sets a lifetime denotes.

A closure is the field list of a function type or a lambda, and supplies its
closure kind and closure scope. A closure prefixes a whole group, so it is a
parse error before a later domain of the same unparenthesized chain; a nested
group is parenthesized, as in `A -> ({ kind = lin } B -> C)`. The token after
the first name distinguishes a closure `{ name = ...` from an implicit binder
`{ name: ...`.

An omitted closure, or an omitted field of one, is derived from what the
expression captures (§4.3). A function type captures nothing, so on a function
type an omitted field is `Kind.unr` or `Lifetime.empty`. On a lambda it is the
join over what the lambda captures.

A lambda's type is determined by the lambda alone: its binders, its result,
and its closure, written or derived. Where the lambda stands never changes it.
`fun (u: Unit): Nat => 0` captures nothing and has type `Unit -> Nat`
everywhere, so checking it against `{ scope = l } Unit -> Nat` is
`TypeMismatch`. Writing `fun { scope = l } (u: Unit): Nat => 0` gives it that
type (§4.3).

`scope` is a keyword at the start of a term and a field name inside a field
list. `scope l => e` extends as far to the right as a lambda body does. `_`
binds an anonymous local in a match pattern, in `let _ := e`, and wherever else
a local is bound.

## 2. Sorts

**2.1 Sorts.** `Sort { level = u, kind = k, scope = S }` is the sort of types at
level `u` whose values are used as kind `k` says (§3.1) and depend on at most
the atoms in `S` (§4).
`Sort { level = u, kind = k, scope = S } : Sort { level = Level.succ(u), scope = S }`.
A type is an unrestricted value, and it carries at most the atoms its values
may depend on (§2.4). A type that names an atom is confined both by §4.2 and by
its sort's scope. Levels are as today, except that they are
second-class (§2.2). The three parameters never interact, except that a sort of
a kind other than `Kind.unr` has a level that is never zero (§2.3). A type's
sort is given by §2.4, and the type checks against a sort exactly when all
three parameters are equal (§2.6).

**2.2 Sort parameters.** `Level`, `Kind` and `Lifetime` are the sort
parameters. The kernel owns them and their operations; the prelude declares
none of them. They are second-class: none is a type, because no sort contains
it, so any position that requires a type rejects them with `NotAType`. That
rules out, among others:
- types built from them, such as `List(Lifetime)` or `Eq(Level, a, b)`;
- data holding them, such as a constructor field `(l: Lifetime)`;
- functions or definitions that return one;
- a `let` that binds one.

A variable of a sort parameter is bound only at the positions below. A binder
anywhere else is `NotAType`, because there its type must be a type.

| Binder | `Level` | `Kind` | `Lifetime` |
|---|---|---|---|
| a definition's, opaque definition's or axiom's header | yes | yes (not an axiom's, §7.3) | yes (not an axiom's, §7.3) |
| a family parameter | yes | yes | yes |
| a family index, a constructor field, a `let` | no | no | no |
| a function type or lambda binder | no | no | yes |
| `scope l =>` | – | – | yes |

A header is the binders written before a declaration's `:`. A header binder
may be explicit or a forced implicit, as today. A function type written after
the `:` is a function type like any other. So
`axiom f : {u: Level} -> Sort { level = u } -> Nat` is `NotAType`, and is written
`axiom f {u: Level}(A: Sort { level = u }): Nat`.

The asymmetry has a reason:
- A level binder changes the universe of everything after it. So a function type
  that binds a level is *large* (§2.4): no sort contains it. Only a
  declaration's own type can bind a level, whether the declaration is a
  definition, family head, constructor or axiom. So a large type is never the
  type of anything a local can hold, and a level-polymorphic declaration is used
  only applied. For example, `let f := id` is `NotAType`, because `f`'s type
  would have to be in a sort.
- A kind or lifetime binder changes no level: neither parameter is a type, so
  neither contributes one. §2.4 also removes a lifetime binder from the scope of
  the function type that binds it. So `(l: Lifetime) -> Lease(l) -> A` is an
  ordinary small type, a callback may abstract over a lifetime, and a
  declaration's type that binds only kinds and lifetimes is small, as
  `withLease`'s is (§4.4).

An expression of a sort parameter is exactly one of these:
- a level: a level variable, `Level.zero`, `Level.one`, `Level.succ(e)`,
  `Level.max(e, e)` or `Level.imax(e, e)`;
- a kind: a kind variable, `Kind.unr`, `Kind.lin` or `Kind.join(e, e)`;
- a lifetime: a lifetime variable, `Lifetime.empty` or `Lifetime.union(e, e)`.
  A `scope` binder's variable denotes its atom (§4.1).

The operations are forms of the language, not functions: none can be passed,
partially applied, or named without its arguments. An expression may stand only
in a parameter position:
- as the argument at a binder of its sort parameter;
- as a sort field or a closure field.

Anywhere else, such as a `match` scrutinee, a block's result, or an argument at
an ordinary binder, it is `NotAType`. Conversely, a term of another type at a
parameter position, such as `Lease(Nat.zero)` or `Sort { level = Nat.zero }`,
is `TypeMismatch`, as any ill-typed argument is.

**2.3 Normal forms.** A sort parameter expression is normalized at birth, and
its only neutrals are variables, so no expression is ever stuck.
- **Levels.** A level's normal form is as today.
- **Lifetimes.** A lifetime's normal form is the set of its atoms and lifetime
  variables. `union(empty, x) = x`, and `union` is associative, commutative and
  idempotent. Two lifetimes are definitionally equal when their sets are equal,
  and `S'` contains `S` when every element of `S` is one of `S'`.
- **Kinds.** A kind's normal form is either `Kind.lin`, or a set of kind
  variables, with the empty set being `Kind.unr`. `join` unions the sets, and
  `lin` absorbs: `join(unr, k) = k` and `join(lin, k) = lin`. Two kinds are
  definitionally equal when their normal forms are equal, and `k'` contains `k`
  when `k'` is `Kind.lin`, or when `k` is a set of variables each of which is
  one of `k'`.

No two lifetimes, and no two kinds, are ever apart, so refinement never prunes a
branch on a lifetime or kind equation (§6.2). For the same reason such an
equation is never refutable, which is why no axiom may bind a lifetime or a kind
(§7.3).

A sort of a kind other than `Kind.unr` must have a level that is never zero,
else `LinearProp`, because proofs are unrestricted. So each of these is
`LinearProp`:
- `Prop { kind = lin }`;
- `Sort { level = u, kind = k }` for a level variable `u` and a kind variable
  `k`;
- a `{ kind = lin }` function type into a proposition.

A kind-polymorphic sort is written `Type { kind = k }` or
`Sort { level = succ(u), kind = k }`.

**2.4 Sort of a type.** `kind(T)` and `scope(T)` are the kind and scope of
`T`'s sort, which `T`'s shape gives. A neutral value carries its type, so the
last row reads the sort off that type:

| `T` | sort of `T` |
|---|---|
| `Sort { level = u, kind = k, scope = S }` | `Sort { level = succ(u), scope = S }` |
| `{ kind = k, scope = S } (x1: A1) ... (xn: An) -> B`, binding no level | `Sort { level = imax as today, kind = k, scope = union(S, scope(A1), ..., scope(An), scope(B)) }`, less the group's own lifetime variables; a kind or lifetime binder contributes no level and no scope, and only the closure contributes to the kind |
| a function type binding a level | `Large` |
| a family instance `D(p*, i*)` | the declared classifier of §5.1 under `p*`, and nothing else |
| any other neutral type | the sort its type states: a type variable `A: Type { kind = k, scope = S }`, or `F(e*)` for a local `F`, states it under the arguments; an `opaque def` or `axiom` application and a blocked `match` state the sort of the declared result or motive |

`Large` is internal to the kernel. A program cannot write it or bind a variable
of it, and it is not a sort, so a large type fits no position that requires a
type. `Large` classifies itself. That is harmless, because Girard's paradox
needs something that quantifies over the universe, and nothing can quantify
over `Large`. Since only a declaration's own type is ever large (§2.2), no
hierarchy above `Large` is needed. A large function type whose codomain is a
proposition is proof-valued, as a small one is. Each of its instances is a
proposition. So a level-polymorphic lemma such as `Eq.symm` is published and
applied as a proof, as today, and its body never runs.

A type's scope counts every atom a value of it can hand over. A value can hand
over an atom in three ways: by holding it, by producing it, or by carrying it
in its type. A value can be read off a type, and a forced implicit is exactly
such a readout. Checking and evaluation compute it by following a projection
path through a later argument's type (§2.7), and no caller supplies it. So for a
function type:
- the closure scope counts what the function holds;
- the codomain's scope counts what calling it produces;
- the domains' scopes count what can be read off its type.

This is how a universe level takes `imax` over the domains and the codomain.

A type is itself a value, a struct whose readable fields are its components:
- a family instance's arguments;
- a function type's domains, codomain and closure.

A type's level, kind and scope are fields of its own type, its sort. For
`a: P(h)`, `h` is read off `a`'s type, and the level off that type's sort. A
type's scope as a value therefore counts its components, as a struct's scope
counts its fields. The rules above guarantee that a type in
`Sort { …, scope = S }` carries at most `S`:
- §5.1 for a family instance;
- this row for a function type;
- exact instantiation for a type variable.

So the sort of `Sort { …, scope = S }` is at scope `S` (first row). A type's
kind says how the value itself may be used. So a function type's kind is
its closure kind alone: an unrestricted function may return a linear value it
creates, and a linear function may return an unrestricted value.

"Less" removes the group's own lifetime variables, because the caller supplies
them: `(l: Lifetime) -> Lease(l) -> A` has scope `scope(A)`. Every other element,
an atom or an outer variable, is kept. A lifetime has no other neutrals (§2.3),
so nothing else needs deciding.

A family instance's sort is its declaration's classifier under its arguments
(§5.1), not something read off the arguments' values, so it commutes with
substitution. The declaration's scope already counts every value that can be
read off an instance, because §5.1 requires it to contain the scope of each
parameter's and index's type. A family declaration has no removal, since its
declared scope may mention only its parameters.

**2.5 Conversion is exact.** Conversion compares the new parts by equality: two
sorts are equal when their levels, kinds and scopes are, and two function types
need, beyond today's rules, equal closure kinds and closure scopes, with kinds
and scopes compared as normal forms (§2.3). `ValueKey` includes kinds, scopes
and closures. It keys an atom by the identity of the `scope` term that opened
it (§4.1).

**2.6 Sorts are exact.** Checking a term against an expected type requires the
synthesized type to equal the expected one, sorts and closures included. A
kind or scope that differs at any position is `TypeMismatch`. Kinds and scopes
are not cumulative, for the same reason universes are not. An implicit is
re-derived from its argument's own type whenever an application is evaluated.
Suppose a value's type could stand at a larger kind or scope than its own.
Evaluation would then derive a different variable, or a different type, than
checking did, and a generic definition could return a scoped value at an
unscoped type, or a linear one at an unrestricted type.

Inclusion is tested in exactly two places. In both, something declares a sort
or closure, and what it contains must fit that declaration:
- a lambda's closure against what its body captures (§4.3);
- a family's declaration against its fields (§5.1).

A failure is `KindExceeded` for a kind and `ScopeExceeded` for a scope. To lift
a function value `f` to a larger closure, write
`fun { kind = k, scope = S } (x: A): B => f(x)` at that closure. §4.3 admits it
whenever `k` and `S` contain the kind and scope of `f`'s type (§2.4). A type has
no such lift. A position that must accept types at several kinds or scopes
takes a variable (§2.7).

**2.7 Kind and scope polymorphism.** A binder `{k: Kind}` or `{S: Lifetime}` is
a kind or lifetime variable, as `{u: Level}` is a level variable, and is forced
like any implicit. It is forced through a family parameter in a later explicit
argument's type, or through a sort field or closure field that projection
reaches. A sort's three fields and a function type's two closure fields are
projection positions, as a sort's level is today. The level position recovers
as today; the others recover a variable only when the field there is exactly
that variable, as `LevelOffset` recovers a level only from a single atom. So
`{A: Type { scope = union(S, m) }}` does not force `S`.

A variable is solved where it forces:
- to `scope(A)` for a binder `{A: Type { scope = S }}`;
- to `kind(A)` for `{A: Type { kind = k }}`;
- to the argument's closure scope for `(f: { scope = S } A -> B)`, and to its
  closure kind likewise.

Every other occurrence must then equal that solution. Since sorts are exact
(§2.6), the solution is canonical, never chosen among alternatives, and
evaluation re-derives the same one. A variable no argument reaches is
`NonForcedImplicitParam`.

Every polymorphic prelude declaration carries a lifetime variable:
- beside each type parameter, `Prop`-valued ones included;
- for the sort in each type-family parameter's codomain, as
  `motive: A -> Sort { level = v, scope = Sm }` does in `Eq.subst`.

Every higher-order prelude declaration also carries a lifetime variable for each
function-typed parameter's closure scope. A definition that omits them accepts
only arguments at `Lifetime.empty`.

A family's function-typed field is different: a closure-scope variable of its
own could not be forced, because nothing in an instance's type mentions it. So
such a field takes the family's own lifetime variable as its closure scope, as
in `BEq {S: Lifetime}(A: Type { scope = S })` with
`mk (beq: { scope = S } A -> A -> Bool)`. The closure may then hold what the
family's values may already depend on, and adds nothing to the family's scope.
A function type that a prelude definition returns as a type, such as `Not(a)`,
follows the same rule.

```raccoon
inductive List {S: Lifetime}(A: Type { scope = S }) : Type { scope = S }
 | nil : List(A)
 | cons (head: A) (tail: List(A)) : List(A)

inductive Eq {u: Level}{S: Lifetime}(A: Sort { level = u, scope = S })
    indices (x: A)(y: A) : Prop { scope = S }
 | refl (x: A) : Eq(A, x, x)
```

`List(Lease(l))` forces `S := {l}` and is `Type { scope = l }`. `List.nil(A)`
forces `S` through its explicit `A`. A second binder at the same variable, as
in `{S: Lifetime}{A: Type { scope = S }}{B: Type { scope = S }}`, requires
`scope(B)` to equal `scope(A)`. A family that holds both takes a variable for
each and declares their union, `Type { scope = union(S, T) }`.

A proposition obeys §5.1 like any family. `Eq` is at `Prop { scope = S }`
because `refl` holds an `A`, and `Eq(Lease(l), a, b)` is at
`Prop { scope = l }`. A closure that captures a proof of it can match the proof
and recover the lease, so the proof's type must count `l` in the closure's
scope (§4.3).

## 3. Linearity

**3.1 Linear types.** A type `T` is linear when `kind(T)` is not `Kind.unr`:
either `Kind.lin`, or a kind involving a variable, which some instantiation
makes `lin`. Every value of a linear type, a *token*, is used exactly once
(§3.2). Linearity is read off the sort, as the scope is (§2.4), and never off
a family's fields:
- a family instance is linear when its declared kind under its arguments is
  (§5.1);
- a function type is linear when its closure kind is;
- a type variable, or any other neutral, is linear when the sort its type
  states is.

Sorts and propositions are never linear (§2.3, §2.4). Linearity starts at a
family declared at a kind other than `Kind.unr`. Its values are introduced by
its constructors and consumed by `match` (§6.1), and by nothing else.

This covers every shape a type can take. `F: Type -> Type`,
`F: Type -> (Type -> Type)`, and a binder whose codomain only computes to
`Type` all return types at the kind their own type states, which is
`Kind.unr`. Instantiating any of them at a function that returns a linear type
is therefore `TypeMismatch`.

**3.2 The ledger.** A local of linear type is used exactly once within the
extent of its binder, whether a lambda, a definition's parameters, a `let` or
a match pattern binds it, `_` included. Uses are counted along each path
through that extent that takes one branch at every `match`. A lambda's body
lies on those paths at the lambda's position, so a closure that uses a
captured linear local must use it on every path through its body. A use is any
occurrence.

No use on some path is `LinearUnused(x)`, which is also what a wildcard over a
linear field reports. A second use on some path is `LinearReused(x)`. A match
with no branch ends every path through it and so uses every linear local live
at it; no evaluation reaches it.

Whether a local is tracked is decided once, from its type as it reads at its
binder. Refinement in a branch never changes that for a local bound outside the
branch. A pattern field's binder is its pattern, so its type reads as the branch
refines it. A local whose type's kind
involves a variable is tracked, since its binder's extent must be valid when
the variable is `lin`. Locals of unrestricted type are not tracked. Globals are
never tracked: a `def` or `opaque def` whose type is linear is `LinearGlobal`,
and an axiom is §7.3's.

Types and proofs hold no tokens. A term whose type is a sort or a proposition
may not contain a subterm of linear type (`LinearInType(e)`, where `e` is that
subterm). This applies to a type in a type position, a type computed as a
value, and a proof alike. It also applies to a lambda inside one that consumes
its own linear parameter. Such a function is named by a definition and referred
to by name instead. A type
or a proof is never consumed as a token. A token inside one would be copied
with it, or dropped without its module's consent, since a proof is never run.
Consequences:
- No type contains a linear local.
- An implicit binder of linear type is never forced, since forcing reads
  types, so it is `NonForcedImplicitParam`.
- Facts about a token are stated about its indices, which are unrestricted.

A `decreases` clause is not a use: it may name a linear parameter as the
structural argument or measure it.

**3.3 Closures.** A function type's closure kind says how its values are
applied. A closure of kind `Kind.unr` may be applied any number of times. A
linear closure is tracked like any linear value, and applying it is its use.

A lambda's closure kind is written, or derived from its captures (§4.3): a
derived kind is the join of the captures' kinds, and a written kind must
contain it, else `KindExceeded`. So a lambda whose body uses an outer linear
local is linear, and writing it at `Kind.unr` is `KindExceeded`, because an
unrestricted closure's body may run any number of times. Each use of an outer
local inside a lambda counts as one use, by the lambda, at the lambda's
position (§3.2).

A lambda is synthesized like any term, in every position. Checked against an
expected type, including a parameter's, it must equal that type, closure
included (§2.6). An implicit may therefore be forced through a lambda
argument's closure, as through any argument's type (§2.7).

A definition captures nothing, so its function type's closure is `Kind.unr` and
`Lifetime.empty`. A definition is a global (§3.2), and its binder group is
applied all at once, so no partial application holds a linear parameter.

**3.4 Kind polymorphism.** Sorts are exact, so each binder accepts exactly one
kind:
- `{A: Type}` accepts only unrestricted types;
- `{A: Type { kind = lin }}` accepts only linear ones;
- a position that accepts both takes a kind variable,
  `{k: Kind}{A: Type { kind = k }}`.

A local whose type is at `k` is tracked (§3.2). So a kind-polymorphic
definition consumes its `A`-typed arguments in every instantiation: it is the
consuming form, and one definition serves linear and unrestricted
instantiations alike. The same holds for a function-typed parameter at a
kind variable, `(f: { kind = kf } A -> B)`: a lambda of either kind may be
passed, and the definition applies `f` once. A definition that must drop or
copy its `A`-typed arguments exists only at `Kind.unr`. This is a deliberate
cost: the intended linear families are tokens, not containers, and the prelude
has no kind variables (§7.3).

**3.5 Constructors and selectors.** A constructor application whose family
instance is linear is itself linear. It is consumed by `match`, which releases
the fields to the ledger. A struct's selector is a `match`, so applying one to
a linear value consumes it as that `match` does.

A struct's selectors are ordinary definitions. They are generated as today, but
with a `returning` clause (§8), and checked like any other definition. A
selector's `match` binds every field and returns one. So the ledger rejects the
selector when another field's type is linear, a kind variable included, with
`LinearUnused` naming that field. A selector of a linear struct whose field's
type mentions an earlier field is also rejected. Its generated result type
names that earlier field's selector applied to the struct value, so the result
type contains a token, which is `LinearInType` (§3.2). So is a selector of a
linear struct's proof field: its body is a proof that consumes the struct
value. Either way that selector's declaration fails, reported at its field, and
the family itself is still published. This is what happens today when a
selector of a struct in `Prop` would eliminate it into data. A family with such
a field is declared with `inductive` and matched on directly, or given
hand-written selectors where they are
admissible.

Structure eta is unchanged and is never a use; a sealed family has none
(§7.1). A constructor's implicit family parameters are inferred or explicit
exactly as today.

## 4. Scopes

**4.1 Opening a lifetime.** `scope l => e : T` when `e : T` under
`l: Lifetime`. The requirement that `T` not name the new atom, its sort
included, is §4.2's check at the `scope`'s own position, where `l` is out of
scope. This is the only construct that introduces an atom. `scope` synthesizes
when its body does, and checks by checking its body against the expected type.

Checking and evaluation alike bind `l` to a lifetime holding one atom unique to
this `scope` term, identified by the term's node identity. The body is checked
with `l` denoting that atom, not a neutral. Two `scope` terms are two atoms,
and one term evaluated twice is one atom. The construct denotes the value of
`e` and is otherwise erased.

An atom names a `scope` term, not an entry into it. A recursive call re-enters
the same atom, which confinement (§4.2) makes harmless to the checker. An atom
is not a local: it is never linked by refinement (§6.2) and never abstracted.
Printed output spells an atom as its binder. A residual keeps the `scope` term
with its node identity and never gives it a synthetic one, which would open a
different atom.

**4.2 Outside its scope an atom cannot be named in a type.** A type whose value
mentions an atom whose `scope` binder is not in the ambient context is
`LifetimeEscapes(l)`. A `scope` term encloses a position exactly when its
binder is in that position's context. The check is made:
- on every type the checker synthesizes for a term or checks a term against;
- on every argument or reconstructed implicit at a binder whose classifier is
  a sort;
- on the type of every local at its binder.

The dependency set a value carries answers it. Evaluation never makes this
check, and a residual records nothing of it, since the residual keeps the
`scope` term and re-evaluates it.

This check is the whole of an atom's confinement. A lifetime is not a value
(§2.2), so an atom can leave its scope only inside a type, which this check
refuses. A linear value whose type's scope contains `l` can neither leave the
scope nor be dropped, so it is consumed inside it. §5.1's rule that a linear
family names its lifetime parameters in its scope is an aid to that, not a
second mechanism.

A value computed under `l` whose type neither mentions `l` nor is scoped by it
may leave, even when its code names `l`. For example, a closure
`fun (u: Unit): Nat => e` whose body names `l` but captures nothing scoped has
type `Unit -> Nat`. A lifetime is not a capability. What confines a capability
is that only its module can make one (§5.1).

**4.3 Captures and derived closures.** A lambda's captures are the locals bound
outside it that its body mentions, in terms and in types written in the body.
The lambda's own binder types and result type are not its body: they are part
of its type, which §4.2 checks. A variable of a sort parameter is not a value,
so it contributes nothing (§2.2).

An implicit that the checker reconstructs in the body is not a capture. It is
read off the type of some argument (§2.4), and that type's scope already counts
it. If the argument mentions a capture, the capture's type counts it. If it
mentions the lambda's own parameter, the lambda's domains count it.

Let `K` be the join of `kind(type of the local)` over the captures, and `C` the
join of `scope(type of the local)`. A lambda's closure is what it captures:
- An omitted closure kind is `K`, and an omitted closure scope is `C`.
- A written closure kind must contain `K`, else `KindExceeded`.
- A written closure scope must contain `C`, else `ScopeExceeded`.

The domains and the codomain play no part in the closure. They enter the
lambda's type's scope separately (§2.4). Derivation and check alike read only
the lambda and the types of its captures, never where the lambda stands.

**4.4 Lifetime binders elsewhere.** A binder of type `Lifetime`, explicit or
implicit, in a function type, a lambda, a definition or a family introduces no
atom. It abstracts over a lifetime that some caller supplies, which may be
`{}`. A resource operation is an ordinary definition:

```raccoon
def withLease {k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}{kf: Kind}{Sf: Lifetime}
    (f: { kind = kf, scope = Sf } (l: Lifetime) -> Lease(l) -> A): A :=
  scope l => f(l, Lease.mk(l))

-- callers, where t: Tok(m) and g: Lease(m) are locals
withLease(fun (l: Lifetime)(h: Lease(l)): Nat => 0)
withLease(fun (l: Lifetime)(h: Lease(l)): Tok(m) => t)
withLease(fun (l: Lifetime)(h: Lease(l)): Nat => useLease(g))
```

`withLease` belongs to `Lease`'s module, since it applies the sealed
constructor (§7.1). Each part of the signature has a job:
- `A` is bound outside `f`'s lifetime binder, so no value confined to `l` can be
  returned.
- `S` lets the result be confined to an enclosing scope.
- `k` lets the result be a token or an unrestricted value.
- `kf` and `Sf` let the callback be of either kind and capture values of any
  scope. `withLease` applies `f` exactly once, which is valid at either kind
  (§3.4).

The one definition then serves callbacks and results of both kinds, and no
caller writes a closure (§4.3):
- The first lambda captures nothing, so `kf := Kind.unr` and `Sf := {}`.
- The second captures the token `t: Tok(m)`, so `kf := Kind.lin` and
  `Sf := {m}`.
- The third captures the lease `g: Lease(m)`, so `kf := Kind.unr` and
  `Sf := {m}`.

`A` is forced through `f`'s result, which depends on none of `f`'s binders.
`k` and `S` are forced through `A`'s sort, and `kf` and `Sf` through `f`'s
closure (§2.7).

## 5. Declarations

**5.1 Families.** A family's classifier is a sort. Its kind and scope are
declared, written or omitted, and never derived. The scope may mention only the
family's parameters. For each constructor:
- the declared kind must contain the join of its fields' kinds, else
  `KindExceeded` naming the field;
- the declared scope must contain the join of its fields' scopes, else
  `ScopeExceeded` naming the field.

The declared scope must also contain the scope of every parameter's and
index's type, else `ScopeExceeded` naming it. A value that can be read off an
instance's type is one its values can hand over (§2.4). So
`P {l: Lifetime}(h: Lease(l))` must declare `scope = l`. A type parameter counts
too, because a type carries up to its sort's scope (§2.4). So
`Phantom {S: Lifetime}(A: Type { scope = S })` must declare `scope = S` even
though it holds no `A`.

A family whose declared kind is not `Kind.unr` must also name every lifetime
parameter in its scope, else `ScopeExceeded` naming it. These joins are
computed for the declaration check alone. An instance is at
exactly the declared sort under its arguments (§2.4). So a family confined to
a lifetime, or linear in a kind, that it is parameterized by says so in its
classifier.

```raccoon
sealed inductive Lease (l: Lifetime) : Type { scope = l }            -- cannot leave scope l
 | mk : Lease(l)

sealed inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }  -- scope = l is required: Tok is linear
 | mk : Tok(l)

inductive Holder {k: Kind}{S: Lifetime}(A: Type { kind = k, scope = S })
    : Type { kind = k, scope = S }                                   -- declared, never derived
 | mk (held: A) : Holder(A)
```

A caller may instantiate `l` at `Lifetime.empty`. A value of
`Tok(Lifetime.empty)` is then linear and confined to no scope, and `Tok`'s
module mints one only if it chooses to. A capability must be sealed to confine
anything. With an unsealed `Lease.mk`, any code that names `l` could make a
`Lease(l)`, including code that runs after the scope closes, such as the
closure in §4.2.

Linearity is declared, as the scope is. A family whose fields are linear only
through a kind variable is declared at that variable, as `Holder` is. That
makes it linear at exactly the instances whose argument is linear. A field
type in which the parameter holds no value, such as `A -> Nat`, is at its own
kind, its closure kind (§2.4). So it adds nothing to the family's kind, though
its scope still counts `A`'s. A sibling in a
`mutual` block is read by its declared classifier, so no fixed point is
computed. Strict positivity, uniform parameters, `mutual` blocks and structs
are unchanged.

## 6. Matching

**6.1 Consumption.** Matching a scrutinee of linear type consumes it once. It
releases the constructor's fields to the ledger, each at the branch's extent.
A wildcard binds an anonymous local, so one over a linear field is
`LinearUnused` (§3.2). Every `match` writes its motive with `returning` (§8).
Coverage and the `Prop` elimination restriction are unchanged. Each branch is
checked against the motive under the branch's equations.

**6.2 Lifetime and kind equations.** Lifetimes and kinds are never indices
(§2.2). Refinement still meets an equation between two of them when it compares
two instances of a family at different lifetime or kind arguments. Matching a
proof of `Eq(Type, Wrap(l), Wrap(m))`, for a family `Wrap (l: Lifetime) : Type`,
is one such case. The equation is solved over the normal forms of §2.3, as
level and variable equations are today:
- A refinable variable alone on one side, not occurring in the other, is linked
  to the other side. When both sides are refinable variables, the later-bound is
  linked to the earlier-bound.
- An atom is not a variable and is never linked.
- Every other equation, a join or union on both sides included, is stuck.

None is apart (§2.3).

## 7. Sealing

**7.1 Sealed families.** A family marked `sealed` exports its head, parameters,
indices and classifier, but not its constructors or its selectors. A module is
a `.rac` file. Outside the declaring file, each of the following is
`SealedConstructor`:
- a term that names one of its constructors, applied or not;
- a match on a value of it;
- selecting one of its fields;
- naming one of its constructors by `.short` form.

The constructor names still resolve, so that every such use reaches this
diagnostic and not an unbound-name error. Beyond that, they have no effect
outside the file. An implicit argument the checker reconstructs may name a
sealed constructor and is exempt. But forcing an implicit through a sealed
constructor's field compiles only inside the declaring file.
Elsewhere the implicit is `NonForcedImplicitParam`, since reconstructing it
would read the field.

A sealed family is never structure-eta eligible. Eta would let a `match` in its
module open a neutral of it as a constructor application, even though the
module never built it; an axiom's result or a blocked computation are such
neutrals.

**7.2 What the checker knows.** Sealing restricts what a program may write, not
what the checker knows. Kinds, scopes, coverage, apartness and the conversion
of values are computed from the full declaration in every module, with no eta
for a sealed family (§7.1). An `opaque def` is unchanged: its body is checked,
and it does not unfold after publication, in any module. Its application's
sort is the sort of its declared result (§2.4).

**7.3 Axioms.** Outside the trusted prelude, an `axiom` is `AxiomMintsToken`
when its type, in its value, contains any of these:
- a binder of a kind or lifetime;
- a kind or lifetime expression other than `Kind.unr` and `Lifetime.empty`,
  sort and closure fields included;
- a linear type;
- a sealed family declared in another module.

An axiom's result is a neutral. Without this rule an axiom could consume a
token without its module, as `axiom eat {A: Type { kind = lin }}(x: A): Unit`
would. That includes a token held by a family `W` whose field is a token.

An axiom could also state an equation no program can refute. Take a fieldless
`Wrap (l: Lifetime) : Type`. No two lifetimes are apart (§2.3), so
`axiom wrapEq (a: Lifetime)(b: Lifetime): Eq(Type, Wrap(a), Wrap(b))` is
consistent. Yet a match along `wrapEq(a, Lifetime.empty)` links the variable `a`
to `Lifetime.empty` (§6.2). A generic definition can then return its `Tok(a)` as
a `Tok(Lifetime.empty)`, and a caller that instantiates `a` at a scope's atom
carries the token out of that scope. An equation between kinds would likewise
retype a value across kinds.

The last bullet protects sealing. A data value of a sealed family is safe from
an axiom: the axiom's result is a neutral, and since a sealed family has no eta
(§7.1), no `match` opens it. A proof is different. Proof irrelevance
reconstructs a proof as its proposition's constructor when the proposition
determines the constructor's fields, and an axiom's proof is no exception.
Take a sealed `Permit (l: Lifetime) : Prop | mk`, and the axiom
`axiom forge : Permit(Lifetime.empty)`. The module's own `match` would take
`forge` for a permit the module had made, and could mint a token from it. With
the bullet, every value of a sealed family that a `match` opens was made in its
module.

The bundled prelude:
- declares no family, closure or sort at a kind other than `Kind.unr`, and no
  kind variable;
- puts every declaration at scope `Lifetime.empty`, or at a lifetime variable
  or a union of lifetime variables.

A library that needs a container of tokens declares its own.

## 8. Interactions

- **`Prop`.** Proofs are unrestricted, since a proposition's sort is at
  `Kind.unr` (§2.3). Proof irrelevance is unchanged, and a proof holds no
  token (§3.2). A proposition has a scope like any family (§5.1), may mention
  a lifetime, and §4.2 applies to it.
- **Levels.** Levels become second-class (§2.2), which changes existing
  Raccoon in four ways:
  - A level variable is bound only by a declaration header or a family
    parameter, so no function type or lambda binds one.
  - A level-polymorphic declaration's type is large (§2.4), so the declaration
    is used only applied.
  - `Level` is no longer a type.
  - `Level.succ`, `Level.max` and `Level.imax` are forms of the language, not
    prelude builtins.

  Today's kernel gives a function type that binds a level a universe that
  mentions that binder; `Large` replaces it.

  Level arithmetic, `imax` and forcing are otherwise unchanged. A sort's kind
  and scope ride beside the level, are forced the same way (§2.7), and interact
  with it only through `LinearProp` (§2.3).
- **Implicit reconstruction.** A recovered `Lifetime` argument is subject to
  §4.2 wherever it enters a type.
- **The eta-adapter is removed.** Today a function name or lambda checked against
  an expected function type with fewer implicit binders is wrapped in a lambda
  that fits it, so `def monoId : Peano -> Peano := polyId` checks. That types an
  expression by where it stands, and it is the one way a level-polymorphic
  declaration becomes a value without being applied (§2.2). It is removed.
  Such a program writes the lambda itself:
  `def monoId : Peano -> Peano := fun (x: Peano): Peano => polyId(x)`.
- **Every `match` writes `returning`.** Today a `match` without `returning`
  gets its motive from one of two places:
  - from the syntax of its expected type, when that is a written declared type;
  - with no expected type, from the scrutinee's own type.

  The first types the match by where it stands. There is no local
  alternative: a stuck match needs its motive as syntax in its residual, a
  branch's synthesized type is a value, and evaluation never infers. So
  `returning` is required on every `match`, and both rules are removed. Struct
  selectors are generated with their field's type as `returning`.

  With the eta-adapter gone too, no check reads the syntax of its expected
  type: every check synthesizes and compares for equality. Adding value
  quoting later would allow a local rule that lets a match whose branches share
  one non-dependent type omit `returning`. That would only relax this rule, so
  no program written under it would break.
- **Residuals.** A residual carries a lambda's closure fields: written ones as
  written, and derived ones as the kind and lifetime expressions that §4.3
  derived. Those name only variables and atoms in the lambda's scope (§2.3),
  with an atom written as its `scope` binder. Evaluation re-evaluates them in
  the lambda's environment. Because sorts commute with substitution (§2.4),
  that agrees with deriving them again. Implicit arguments stay out of
  residuals and are re-derived from the arguments' types when a residual is
  evaluated, as today. Exact sorts (§2.6) are what make that derivation agree
  with checking.
- **Runtime.** The interpreter makes none of the checks of `scope`, sealing
  and linearity.
  - Lifetimes and kinds are never program data (§2.2). At run time they occur
    only inside types, where implicit re-derivation reads them, and as
    arguments at their own binders.
  - The interpreter binds a scope's `l` to its atom. It shares the checker's
    normal forms (§2.3), as one implementation.

## 9. Diagnostics

```text
LinearUnused, LinearReused, LinearInType, LinearGlobal, LinearProp,
LifetimeEscapes, KindExceeded, ScopeExceeded, SealedConstructor, AxiomMintsToken
```

`TypeMismatch`, `NotAType` and `NonForcedImplicitParam` are existing
diagnostics and gain the cases named above. These field-list errors are parse
errors:
- an unknown, repeated or misplaced field;
- an empty field list;
- a missing `level` in `Sort`;
- a closure before a later domain;
- a `match` without `returning`.

Every rule above is a test obligation: one program the rule admits, and the
smallest mutation that reaches its named diagnostic and no earlier one.
