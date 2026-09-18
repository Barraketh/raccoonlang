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
namespace Path { declarations }
open Path
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

Types are terms. The primitive universe values are:

```text
Prop       = Sort(Level.zero)
Type       = Sort(Level.one)
```

`Level` is a first-class type. The bundled prelude provides `Sort`,
`Level.succ`, `Level.max`, and `Level.imax`:

```raccoon
def id {u: Level}{A: Sort(u)}(x: A): A := x

inductive Box (u: Level)(A: Sort(u)) : Sort(u)
 | mk (value: A) : Box(u, A)
```

Universes are not cumulative. A value in `Sort(u)` does not automatically fit
a position expecting a larger sort. Universe expressions must be
definitionally equal where types are compared.

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

Inductive family parameters are erased from constructor values. At a
constructor call, a family parameter is inferred when later stored fields
force it; otherwise it becomes an explicit constructor argument. Implicits
written directly on a constructor must still be forced.

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

A type annotation on `let` supplies an expected type to its value. Local
bindings may shadow earlier names.

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

inductive Vec {u: Level}(A: Sort(u)) indices (n: Nat)
    : Sort(Level.max(Level.one, u))
 | nil : Vec(A, Nat.zero)
 | cons (n: Nat)(tail: Vec(A, n))(head: A) : Vec(A, Nat.succ(n))
```

Constructors are global declarations inside the family namespace, such as
`Nat.zero` and `Vec.cons`. A constructor result must be an application of its
own family using all parameters uniformly. The checker validates:

- the family and constructor universes;
- constructor result shape and parameter uniformity;
- strict positivity, including occurrences nested through parameters already
  certified as positive;
- the parameter/index split used by matching and reconstruction.

Constructor pattern fields correspond to stored constructor fields. Erased
family parameters are not pattern fields.

The source language declares one inductive family at a time. The trusted Core
AST also has atomic mutual-inductive blocks, but the current parser has no
surface syntax for them.

## Pattern matching

```raccoon
def pred (n: Nat): Nat := {
  match n with
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
match n with
| .zero => Nat.zero
| .succ p => p
```

### Result types and `returning`

A match result type is its motive. Write it explicitly when needed:

```raccoon
match xs returning Vec(A, n) with
| Vec.nil => Vec.nil(A)
| Vec.cons k tail head => xs
```

Without `returning`, the checker uses syntax for the expected type when one is
available, including a definition or lambda result type, an annotated `let`,
or a surrounding block result. With no syntactic expected type, the result
defaults to the scrutinee's type.

If neither rule expresses the intended result, `returning` is required. This
commonly occurs in a match nested inside another branch: the outer branch has
an expected semantic value but no reusable type syntax.

Elimination from `Prop` is restricted. A Prop-valued result is always allowed.
A data-valued result is allowed only for an empty reachable constructor set or
when the exact proposition determines every constructor field. See
[Proofs and elimination](kernel.md#proofs-and-elimination).

## Recursive definitions

A recursive function must carry a `decreases` clause:

```raccoon
def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
  match b with
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
struct Cursor {u: Level}(A: Sort(u)) : Sort(u)
 | mk (remaining: List(A)) : Cursor(A)

def countRemaining {u: Level}{A: Sort(u)}(cursor: Cursor(A)): Nat decreases measure(cursor.remaining) := {
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

The surface language exposes singly recursive definitions. The trusted Core
AST additionally supports mutually recursive definition blocks whose members
have compatible lexicographic metrics. Measure expressions are currently
supported only for singly recursive definitions.

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
same ordinary function application. An `_` field remains stored but gets no
selector.

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
