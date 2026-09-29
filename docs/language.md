# Raccoon language reference

This document describes the source language accepted by the current parser and
checker. It is a reference for implemented behavior, not a roadmap.

## Programs and declarations

A `.rac` file contains imports, declarations, and optionally one final
expression. Imports must come first. Only the entry file may have a final
expression; imported files are declaration modules.

```raccoon
import Data.Nat

def twice (f: Nat -> Nat)(x: Nat): Nat := f(f(x))

{ twice(Nat.succ, 0) }
```

The declaration forms are:

```text
def name (parameters): Result := term
opaque def name (parameters): Result := term
axiom name (parameters): Result
inductive Family (parameters) indices (indices): Sort
struct Family (parameters) indices (indices): Sort
mutual { declarations }
namespace Path { declarations }
open Path
```

A `mutual` block is atomic and must contain either only function definitions or
only inductive or structure declarations. Function bodies can refer to every
peer, and constructors can refer to every family head. Mutual function members
must be ordinary transparent definitions with a function parameter list, a
`decreases` annotation, and no builtin or opaque body. For example:

```raccoon
mutual {
  def even (n: Nat): Bool decreases structural(n) := {
    match n returning Bool with
    | Nat.zero => Bool.true
    | Nat.succ k => odd(k)
  }
  def odd (n: Nat): Bool decreases structural(n) := {
    match n returning Bool with
    | Nat.zero => Bool.false
    | Nat.succ k => even(k)
  }
}
```

Mutually recursive inductives use the same block form. Their declarations must
share the common parameter telescope required by the kernel; sibling family
heads are available in constructor fields and results:

```raccoon
mutual {
  inductive Even : Type
   | zero : Even
   | succ (odd: Odd) : Even

  inductive Odd : Type
   | succ (even: Even) : Odd
}
```

A transparent `def` reduces during checking and evaluation. An `opaque def`
has a checked body but does not unfold after publication. An `axiom` has the
declared type and no body. At proof types, both forms still obey canonical proof
representation and proof irrelevance.

`:= builtin` is reserved for declarations in the trusted prelude. Ordinary
programs cannot acquire builtin behavior.

## Checking and execution

The supported embedding pipeline is staged:

```text
surface program -> elaborated program -> checked program -> result
```

Elaboration resolves names and lowers surface syntax. Checking typechecks and
publishes declarations while computing the final body value. Execution accepts
only the resulting checked artifact; there is no second unchecked evaluation
pass. Core-AST evaluation helpers and trusted-prelude construction are internal
implementation operations; public prelude loaders only select a prelude for the
staged pipeline.

Identifiers begin with a letter and continue with letters, digits, or `_`.
`_` may be used for an anonymous binder or ignored pattern field.

## Universes

Types are terms. `Sort`, `Type` and `Prop` are the sort formers, and they are
keywords:

```text
Sort { level = e, kind = k, scope = S }   -- the sort at level e, kind k, scope S
Type { kind = k, scope = S }              -- level is Level.one
Prop { kind = k, scope = S }              -- level is Level.zero
```

A sort has three parameters, supplied by name in any order: its `level`, its
`kind`, which says how the values of its types may be used, and its `scope`, a
lifetime: the set of lifetime variables its types' values may depend on.
`Sort` is not a function, so `Sort(u)` does not parse, and `Sort` requires its
`level`. An omitted `kind` is `Kind.unr` and an omitted `scope` is
`Lifetime.empty`; that is what the shorter spelling means. So `Type` is
`Sort { level = Level.one, kind = Kind.unr, scope = Lifetime.empty }`. A field
list is nonempty, and an unknown or repeated field is a parse error. `Type` and
`Prop` fix the level, so a `level` field on either is a parse error too.

`Level`, `Kind` and `Lifetime` are the sort parameters. An expression of one is
a variable or one of its forms:

```text
Level.zero  Level.one  Level.succ(e)  Level.max(e, e)  Level.imax(e, e)
Kind.unr  Kind.lin  Kind.join(e, e)
Lifetime.empty  Lifetime.union(e, e)
```

The forms belong to the language, not to the prelude: they are not functions,
and `Level.succ` or `Lifetime.union` without its arguments names nothing. A
name in a sort field resolves to a local first, then to one of that field's
forms unqualified, and only then as usual. So `level = succ(u)` means
`Level.succ(u)`, even inside `namespace Nat`, and `kind = lin` and
`scope = union(a, b)` mean `Kind.lin` and `Lifetime.union(a, b)`:

```raccoon
def id {u: Level}{A: Sort { level = u }}(x: A): A := x

inductive Box (u: Level)(A: Sort { level = u }) : Sort { level = u }
 | mk (value: A) : Box(u, A)

def keep {k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}(x: A): A := x
```

Kinds and lifetimes are normalized as they are built. A lifetime is a set:
`union` is associative, commutative and idempotent, with `Lifetime.empty` as its
identity. A kind is `Kind.lin` or a set of kind variables, the empty set being
`Kind.unr`: `join` unites the sets, and `Kind.lin` absorbs. Two kinds or two
lifetimes are equal exactly when their normal forms are.

The sort parameters are second-class: they parameterize sorts, families and
declarations, but none is a type, since no sort contains it. A position that
requires a type rejects them with `NotAType`, so there is no `List(Level)`, no
`Eq(Lifetime, a, b)`, no constructor field or `let` holding one, and no
function returning one.

A variable of a sort parameter is bound only at these binders; anywhere else a
binder's type must be a type:

| Binder | `Level` | `Kind` | `Lifetime` |
|---|---|---|---|
| a definition's, opaque definition's or axiom's header | yes | yes | yes |
| a family parameter | yes | yes | yes |
| a family index, a constructor field | no | no | no |
| a function type or lambda binder | no | no | yes |

A header is the binders written before a declaration's `:`. A function type
written after the `:` is an ordinary function type, so
`axiom f : {u: Level} -> Sort { level = u } -> Nat` is `NotAType` and is written
`axiom f {u: Level}(A: Sort { level = u }): Nat`.

An expression of a sort parameter stands only at a parameter position: a
sort's field, or the argument at a binder of that parameter, as in
`Box(Level.one, Nat)`. Anywhere else, such as a `match` scrutinee, a block's
result or an argument at an ordinary binder, it is `NotAType`. A term of
another type at a parameter position, such as `Sort { level = Nat.zero }` or
`Type { scope = Kind.lin }`, is `TypeMismatch`.

A function type that binds a level is *large*: no sort contains it, so a large
type fits no position that requires a type. Only a declaration's own type can
be large, so a level-polymorphic declaration is used only applied. Naming one
anywhere but as the head of an application is `NotAType`: `let f := id` is
rejected, and `fun (x: Nat): Nat => id(x)` is written instead. A large function
type whose result is a proposition is still a proposition, so a
level-polymorphic lemma such as `Eq.symm` is a proof like any other. A kind or
lifetime binder does not make a type large.

A sort's type is the sort one level up at the same scope and at `Kind.unr`:
`Sort { level = u, kind = k, scope = S } : Sort { level = succ(u), scope = S }`.
A function type's sort is at its closure kind (see
[Closures](#closures)). Its level is computed as below, and its scope unites
its closure scope and its binder types' scopes with its result's, less the
lifetimes the function type binds itself, since the caller supplies them. So
for a family `Lease (l: Lifetime) : Type { scope = l }`, `Lease(m) -> Nat` is at
`Type { scope = m }`, and `(l: Lifetime) -> Lease(l) -> Nat` is at `Type`. A
kind or lifetime binder contributes neither a level nor a scope.

A sort whose kind is not `Kind.unr` must have a level that is never zero, else
`LinearProp`, since proofs are unrestricted. So `Prop { kind = lin }`,
`Sort { level = u, kind = k }` and a `{ kind = lin }` function type into a
proposition are rejected, and a kind-polymorphic sort is written
`Type { kind = k }` or `Sort { level = succ(u), kind = k }`.

Universes are not cumulative, and neither are kinds and scopes. A value in
`Sort { level = u }` does not automatically fit a position expecting a larger
sort, and a type at `Type { scope = S }` does not fit a position expecting
`Type`. Sorts must be definitionally equal, level, kind and scope alike, where
types are compared.

A binder `{k: Kind}` or `{S: Lifetime}` is forced like any implicit: through a
family parameter in a later explicit argument's type, or through a sort's
field or a function type's closure field, which recovers a variable only when
the field is exactly that variable. So
`{S: Lifetime}{A: Type { scope = S }}(x: A)` forces `S`, and so does
`{S: Lifetime}(f: { scope = S } A -> B)`, while
`{A: Type { scope = union(S, m) }}` does not.

`Prop` is impredicative: a dependent function whose result is a proposition is
itself a proposition regardless of the parameter universes. The sort `Prop` is
not itself a proposition; it has type `Type`.

## Functions and binder groups

Explicit parameters use parentheses. Lambdas include an explicit result type:

```raccoon
def apply (f: Nat -> Nat)(x: Nat): Nat := f(x)

def identity : (A: Type) -> A -> A :=
  fun (A: Type)(x: A): A => x
```

An unparenthesized arrow chain forms one binder group:

```text
A -> B -> C              two arguments, called as f(a, b)
(a: A) -> (b: B) -> C    two arguments, called as f(a, b)
A -> (B -> C)            one argument returning a function, called as f(a)(b)
```

Grouping is part of the type. The two-argument and nested one-argument forms
are not convertible. Every application supplies exactly the explicit
arguments of the function's current binder group.

### Implicit parameters

Implicit parameters use braces:

```raccoon
def id {A: Type}(x: A): A := x

{ id(Nat.zero) }
```

Call sites never write implicit arguments. Every implicit must be recoverable
from the type of a later explicit argument. The checker records that structural
projection and reconstructs the implicit both while checking and while
evaluating residual terms. An implicit binder that is not forced is rejected.

Implicit and explicit binders may be interleaved. Reconstruction must still
come from a later explicit argument, and call sites supply all explicit
arguments in their source order.

A term's type never depends on where it stands. Checking a term against an
expected type synthesizes the term's own type and requires the two to be
definitionally equal. So a polymorphic function named without arguments keeps
its implicit binders, and does not fit a function type without them. Write the
lambda instead:

```raccoon
def polyId {A: Type}(x: A): A := x

def natId : Nat -> Nat := fun (x: Nat): Nat => polyId(x)
```

Inductive family parameters are erased from constructor values. At a
constructor call, a family parameter is inferred when later stored fields
force it; otherwise it becomes an explicit constructor argument. Implicits
written directly on a constructor must still be forced.

### Closures

A function type or lambda may carry a closure, a field list with a `kind` and
a `scope`, that says how its values may be applied and what they hold:

```raccoon
inductive Lease (l: Lifetime) : Type { scope = l }
 | mk : Lease(l)

def use {l: Lifetime}(h: Lease(l)): Nat := 0

def apply {kf: Kind}{S: Lifetime}(f: { kind = kf, scope = S } Unit -> Nat): Nat := f(Unit.unit)

def delay (l: Lifetime)(h: Lease(l)): { scope = l } Unit -> Nat :=
  fun (u: Unit): Nat => use(h)
```

A closure prefixes a whole binder group: the first one of an unparenthesized
chain, or a parenthesized one, as in `A -> ({ kind = lin } B -> C)`. Before a
later domain of the same chain it is a parse error, and so is a `level` field,
an empty list, or an unknown or repeated field. The token after the first name
tells a closure `{ kind = ...` from an implicit binder `{ kind: ...`. A closure
is part of the function type, compared exactly like the rest of it, and a
function type is at its closure's kind and counts its closure's scope.

A function type captures nothing, so an omitted closure field of one is
`Kind.unr` or `Lifetime.empty`, and a definition's own type is always at those.
A lambda's closure is written after `fun`, and each omitted field is derived
from what the lambda captures: the locals bound outside it that its body
mentions. Its binder types and result type are not its body. The derived kind
joins the captures' types' kinds, and the derived scope unites their scopes; a
variable of `Kind` or `Lifetime` contributes nothing. So `delay`'s lambda,
which captures `h: Lease(l)`, has type `{ scope = l } Unit -> Nat`, and a
lambda that captures nothing has an unrestricted, empty closure wherever it
stands: checking `fun (u: Unit): Nat => 0` against `{ scope = l } Unit -> Nat`
is a `TypeMismatch`. A written closure field must contain what the captures
derive, else `KindExceeded` or `ScopeExceeded`. That is also how a function
value is lifted to a larger closure:
`fun { kind = k, scope = S } (x: A): B => f(x)`.

## Terms and local blocks

Function application uses parentheses and comma-separated arguments:

```raccoon
f(x, y)
```

A block contains ordered `let` or `open` statements followed by one result
term:

```raccoon
{
  let x := Nat.succ(Nat.zero)
  let y: Nat := Nat.succ(x)
  Nat.add(x, y)
}
```

A type annotation on `let` must equal the value's own type. Local bindings may
shadow earlier names.

Natural-number literals are arbitrary non-negative integers. They require the
active prelude to provide the validated unary `Nat` layout used by the bundled
prelude. String literal syntax uses JSON-style escapes and Unicode scalar
values, but it is available only when the active trusted prelude provides the
validated `String`, `List Char`, and `Char.ofNat` layout. The bundled prelude
does not currently provide that string layout.

## Inductive families

Parameters before `indices` are uniform across every constructor result.
Binders after `indices` are indices and may vary between constructors.

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (pred: Nat) : Nat

inductive Vec {u: Level}(A: Sort { level = u }) indices (n: Nat)
    : Sort { level = max(one, u) }
 | nil : Vec(A, Nat.zero)
 | cons (n: Nat)(tail: Vec(A, n))(head: A) : Vec(A, Nat.succ(n))
```

Constructors are global declarations inside the family namespace, such as
`Nat.zero` and `Vec.cons`. A constructor result must be an application of its
own family using all parameters uniformly. The checker validates:

- the family and constructor universes, kinds and scopes;
- constructor result shape and parameter uniformity;
- strict positivity, including occurrences nested through parameters already
  certified as positive;
- the parameter/index split used by matching and reconstruction.

A family's sort is declared, level, kind and scope alike, and never derived
from its constructors. An instance `D(p*, i*)` is at exactly the declared sort
with the arguments substituted for the parameters. The declaration must
account for everything a value of the family can hand over:

- the declared kind contains each constructor field's kind, else
  `KindExceeded` naming the field. A family whose fields are linear only
  through a kind variable is declared at that variable;
- the declared scope contains each constructor field's scope, else
  `ScopeExceeded` naming the field;
- the declared scope contains the scope of each parameter's and index's type,
  else `ScopeExceeded` naming it, since that value can be read off an
  instance's type. A type parameter counts at its sort's scope, and a `Level`,
  `Kind` or `Lifetime` parameter counts nothing;
- a family at a kind other than `Kind.unr` names each of its lifetime
  parameters in its scope, else `ScopeExceeded` naming it.

```raccoon
inductive Lease (l: Lifetime) : Type { scope = l }
 | mk : Lease(l)

inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
 | mk : Tok(l)

inductive Holder {k: Kind}{S: Lifetime}(A: Type { kind = k, scope = S })
    : Type { kind = k, scope = S }
 | mk (held: A) : Holder(A)

inductive Phantom {S: Lifetime}(A: Type { scope = S }) : Type { scope = S }
 | mk : Phantom(A)
```

`Holder(Tok(m))` is at `Type { kind = lin, scope = m }` and `Holder(Nat)` at
`Type`. `Phantom` holds no `A`, but `A` can be read off its type, so it
declares `A`'s scope. A field of function type is at its own kind, `Kind.unr`
for an arrow, and at its scope, which counts its domains' and result's scopes.
A proposition obeys the same rules, so a family in `Prop` holds no linear
field. A sibling in a `mutual` block is read by its declared sort.

Constructor pattern fields correspond to stored constructor fields. Erased
family parameters are not pattern fields.

A `mutual` block may contain several inductive families or structures. The
families are checked and published atomically; all sibling family heads are
available while constructor fields and results are elaborated. They must share
the same common parameter telescope and sort, level, kind and scope alike, as
required by the trusted Core block. Generated structure selectors are declared
immediately after the family block.

## Pattern matching

```raccoon
def pred (n: Nat): Nat := {
  match n returning Nat with
  | Nat.zero => Nat.zero
  | Nat.succ p => p
}
```

Matches are checked for missing, duplicate, and unreachable cases. An indexed
constructor that cannot produce the scrutinee's exact family instance may be
omitted. Reachable constructor equations refine indices and branch-local
types.

Use `.constructor` to select a constructor by short name from the scrutinee's
family:

```raccoon
match n returning Nat with
| .zero => Nat.zero
| .succ p => p
```

### Result types and `returning`

A match result type is its motive, which every match writes with
`returning`:

```raccoon
match xs returning Vec(A, n) with
| Vec.nil => Vec.nil(A)
| Vec.cons k tail head => xs
```

A match without `returning` is a parse error, and a motive that is not a type
is `NotAType`. Each branch is checked against the motive under the branch's
refinements. The match's type is the motive, evaluated where the match stands,
whether or not the match reduces.

Elimination from `Prop` is restricted. A Prop-valued result is always allowed.
A data-valued result is allowed only for an empty reachable constructor set or
when the exact proposition determines every constructor field. See
[Proofs and elimination](kernel.md#proofs-and-elimination).

## Recursive definitions

A recursive function must carry a `decreases` clause:

```raccoon
def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
  match b returning Nat with
  | Nat.zero => a
  | Nat.succ p => add(Nat.succ(a), p)
}
```

Three specifications are available:

- `decreases structural(x)` requires the recursive call's `x` argument to be
  a strict constructor subterm of the current one;
- `decreases lexicographic(x, y, ...)` accepts a decrease in the first changed
  component after a definitionally equal prefix;
- `decreases measure(term)` evaluates an inductive-valued measure and requires
  it to become a strict structural subterm.

`measure` is useful when the recursive arguments are rebuilt rather than
passed directly as constructor fields. The same measure expression is
evaluated for the current call and for each recursive call:

```raccoon
struct Cursor {u: Level}(A: Sort { level = u }) : Sort { level = u }
 | mk (remaining: List(A)) : Cursor(A)

def countRemaining {u: Level}{A: Sort { level = u }}(cursor: Cursor(A)): Nat decreases measure(cursor.remaining) := {
  match cursor.remaining returning Nat with
  | List.nil => 0
  | List.cons _ tail =>
      Nat.succ(countRemaining(Cursor.mk(tail)))
}
```

The new `Cursor` is not itself a subterm of the old one, but its `remaining`
list is a strict subterm of the old list. A measure is not an arbitrary
well-founded relation or an inequality proved by the program: after evaluation,
the checker must be able to observe strict constructor-field descent. Packed
`Nat` measures use numeric `<`, corresponding to repeated predecessor descent.

Metrics must have genuine inductive data types. Proofs, axiomatic types, and
quotients cannot supply structural termination evidence.

The recursive name may occur only as the head of a direct recursive call while
checking the body. It cannot be stored, returned, passed to another function,
or hidden inside another value. A recursive call must supply the exact current
binder group.

A `mutual` block exposes mutually recursive definitions whose members have
compatible lexicographic metrics. Every member must carry `decreases
structural(...)` or `decreases lexicographic(...)`; measure specifications are
supported only for singly recursive definitions. Mutual groups are checked and
published atomically, and cross-member calls obey the caller's metric.

## Structs and projections

`struct` is syntax for a one-constructor inductive plus named selector
definitions:

```raccoon
struct Pair (A: Type)(B: Type) : Type
 | mk (fst: A)(snd: B) : Pair(A, B)

def first {A: Type}{B: Type}(p: Pair(A, B)): A := p.fst
```

A struct declaration has exactly one constructor. Every named stored field
gets a selector in the family namespace, so `p.fst` and `Pair.fst(p)` are the
same ordinary function application. A selector is a match on its argument that
returns the field, with the field's type as its `returning` clause. An `_`
field remains stored but gets no selector.

Structure eta is based on the checked family shape, not the `struct` keyword.
Any non-Prop family instance is eta-eligible when it has exactly one
constructor, no indices, and no recursive constructor field. A plain
`inductive` can therefore receive eta without receiving named selectors.
Indexed or recursive singleton families still have positional metadata used by
generated selectors, but they do not receive eta.

For a Prop-valued instance, proof representation and elimination rules replace
data structure eta. A selector out of a proposition is an ordinary match and
must obey the same elimination restriction as any other match.

## Namespaces and names

Namespaces prefix canonical declaration names:

```raccoon
namespace Data {
  inductive Tree : Type
   | leaf : Tree
   | node (left: Tree)(right: Tree) : Tree
}
```

This declares `Data.Tree`, `Data.Tree.leaf`, and `Data.Tree.node`.
Constructors always live under their family head.

Dotted names resolve their first segment as follows:

1. a local binding;
2. the current namespace, from most specific to the root;
3. aliases in the current open scope.

If the first segment is local, the remaining path is projection syntax. Once a
global first segment is selected, resolution continues inside that object and
does not backtrack to another open. Prefix a path with `_root_.` to bypass
locals, the current namespace, and opens.

`open` takes a snapshot of a namespace's existing children:

```raccoon
open Nat
open Nat.{zero, succ}
open Nat.{zero as z, succ as s}
open Nat.{*, -succ, succ as nsucc}
open _root_.Nat
```

`open Nat` means `open Nat.{*}`. Renamed aliases may be used as prefixes when
the opened object has children. Conflicting aliases in one open scope are
rejected. Opens are lexically scoped by namespaces, command blocks, and term
blocks; declarations retain their canonical names.

## Imports

```raccoon
import Lib.Data.Nat
```

The import searches each configured source root for `Lib/Data/Nat.rac`.
Dependencies load before the importing module, duplicate imports are emitted
once, and import cycles are rejected. Imported declarations keep their
canonical names and are not opened automatically.

`Init.Prelude` is loaded automatically by the normal CLI. An explicit
`import Init.Prelude` is accepted as a no-op with the bundled or custom
prelude configuration.

## Bundled prelude

The bundled prelude defines the ordinary logical and data vocabulary used by
the examples and tests, including:

- `Eq`, `False`, `True`, `And`, `Or`, `Iff`, and `Not`;
- `Empty`, `Unit`, `Bool`, `Nat`, `Option`, `Sum`, `List`, `Prod`, and `Sigma`;
- `Decidable`, `Subtype`, `Exists`, `Nonempty`, and common boolean and natural
  operations;
- `Quot` with `Quot.mk`, `Quot.sound`, `Quot.lift`, and `Quot.ind`.

The prelude source is authoritative for its exact API:
`src/main/resources/Init/Prelude.rac`.
