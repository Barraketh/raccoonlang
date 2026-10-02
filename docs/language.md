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
axiom name (parameters): Result
[sealed] inductive Family (parameters) indices (indices): Type-or-Prop
[sealed] struct Family (parameters) indices (indices): Type-or-Prop
mutual { declarations }
namespace Path { declarations }
open Path
```

A `mutual` block is atomic and must contain either only function definitions or
only inductive or structure declarations. Function bodies can refer to every
peer, and constructors can refer to every family head. Mutual function members
must be definitions with a function parameter list, a `decreases` annotation,
and no builtin body. For example:

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

Every `def` is transparent: it reduces during checking and evaluation. An
`axiom` has the declared type and no body, so it does not compute. At proof
types, both forms obey canonical proof representation and proof irrelevance.

Only the trusted prelude declares axioms. An `axiom` in any other module is
`UntrustedAxiom`, whatever its type:

```raccoon
axiom excludedMiddle (P: Prop): Or(P, Not(P))       // UntrustedAxiom
axiom eat {A: Type { kind = lin }}(x: A): Unit      // UntrustedAxiom
```

No rule on an axiom's type could keep it from breaking sealing, linearity or
lifetimes: an axiom can state `False`, from which every value follows, and even
a consistent one could consume a token without its module or equate two
lifetimes. A program that needs an assumption declares it in a custom prelude
instead, a copy of the bundled `Init/Prelude.rac` with the axiom added, and
runs with `--prelude <file>`. That makes the extension of the trusted base
explicit, and the prelude's axioms and builtins keep the obligations of the
[trusted bootstrap](kernel.md#trusted-bootstrap-and-native-values). Its other
declarations are checked as in any module. The bundled prelude's axioms are
`Quot` and `Quot.sound`.

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

Evaluation is strict: an application evaluates its function and arguments,
all but its evidence arguments, which are deferred, before the function's body.
A term in tail position, whose value is the value of the term around it, reuses
the current evaluation frame: a block's result, a match's chosen branch, a
scope's body, and a function's body where the function is applied. Other Core
calls use reusable frames too, so non-tail source recursion no longer consumes
one host stack frame per call. Branching on a `Bool` with `match` keeps a
recursive call in tail position; passing it to a function such as `Bool.and`
does not, since the argument is evaluated first and its result must be retained.

Checking, execution-plan construction and semantic helpers can still recurse on the host stack, so a program
may need more of it than a thread has. `Execution.onStack` runs a computation on a
thread of a chosen stack size; the CLI runs its whole pipeline on one of
`--stack` bytes, 256MB by default. A stack overflow while a declaration is
checked is the diagnostic `EvaluationTooDeep`, located at that declaration, and
one while the program's body is checked and evaluated is `EvaluationTooDeep` at
the body. Nothing inside a declaration or the body catches an overflow.
Checking then stops, reporting the diagnostics found before it: an overflow can
unwind past the restoration of the checker's state, thread-local and
process-wide, so nothing after it is checked. The CLI ends there. A caller that
checks another program afterwards does so on state the overflow may have left
inconsistent; running each check on a thread of its own discards the
thread-local part of it, not the rest. An overflow while parsing or elaborating
is not a diagnostic.

Identifiers begin with a letter and continue with letters, digits, or `_`.
`//` starts a comment that runs to the end of the line. `_` binds an anonymous
local wherever a local is bound: a binder, a pattern field, `let _ := e` or
`scope _ => e`. No name refers to it.

Line breaks separate imports, declarations, the statements of a block, the
cases of a match and the constructors of an inductive. Wherever a line break
separates two items, any number of blank lines and comment-only lines may stand
in its place. A case or constructor starts on a new line and ends its last line,
where only a comment may follow it, so a match's cases never share a line with
its header or with each other.

## Universes

Types are terms. `Type` and `Prop` are the sort formers and are keywords:

```text
Type { level = e, kind = k, scope = S }   // data at level e
Prop { scope = S }                       // propositions
```

Every field is optional. `Type` defaults to level `Level.zero`, kind
`Kind.unr` and scope `Lifetime.empty`; `Prop` defaults to the empty scope.
Propositions have no level or kind, and their proofs are unrestricted.
A field list must be nonempty and may name each permitted field only once.
`Sort` syntax and `Level.imax` have been removed.

`Level`, `Kind` and `Lifetime` are the sort parameters. An expression of one is
a variable or one of its forms:

```text
Level.zero  Level.one  Level.succ(e)  Level.max(e, e)
Kind.unr  Kind.lin  Kind.join(e, e)
Lifetime.empty  Lifetime.union(e, e)
```

The forms belong to the language, not to the prelude: they are not functions,
and `Level.succ` or `Lifetime.union` written without its arguments is an
`ArityMismatch`, as a partial application of one is. A name in a sort or
closure field resolves to a local first, then to one of that field's forms
unqualified, and only then as usual. So `level = succ(u)` means
`Level.succ(u)`, even inside `namespace Nat` or in the body of a recursive
`def succ`, and `kind = lin` and `scope = union(a, b)` mean `Kind.lin` and
`Lifetime.union(a, b)`:

```raccoon
def id {u: Level}{A: Type { level = u}}(x: A): A := x

inductive Box (u: Level)(A: Type { level = u}) : Type { level = u}
 | mk (value: A) : Box(u, A)

def keep {k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}(x: A): A := x
```

Kinds and lifetimes are normalized as they are built. A lifetime is a set of
atoms and lifetime variables:
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
| a definition's or axiom's header | yes | yes | yes |
| a family parameter | yes | yes | yes |
| a family index, a constructor field | no | no | no |
| a function type or lambda binder | no | no | yes |
| `scope l =>` | – | – | yes |

A header is the binders written before a declaration's `:`. A function type
written after the `:` is an ordinary function type, so
`def f : {u: Level} -> Type { level = u} -> Nat := …` is `NotAType` and is
written `def f {u: Level}(A: Type { level = u}): Nat := …`.

An expression of a sort parameter stands only at a parameter position: a
sort's field, or the argument at a binder of that parameter, as in
`Box(Level.zero, Nat)`. Anywhere else, such as a `match` scrutinee, a block's
result or an argument at an ordinary binder, it is `NotAType`. A term of
another type at a parameter position, such as `Type { level = Nat.zero}` or
`Type { scope = Kind.lin }`, is `TypeMismatch`.

A function type that binds a level is *large*: no sort contains it, so a large
type fits no position that requires a type. Only a declaration's own type can
be large, so a level-polymorphic declaration is used only applied. Naming one
anywhere but as the head of an application is `NotAType`: `let f := id` is
rejected, and `fun (x: Nat): Nat => id(x)` is written instead. As the base of
a selection `id.f`, it names nothing, as any base whose type is not a family
instance does, and `id.f` is `NotFound`. A large function
type whose result is a proposition is still a proposition, so a
level-polymorphic lemma such as `Eq.symm` is a proof like any other. A kind or
lifetime binder does not make a type large.

A sort's type is the sort one level up at the same scope and at `Kind.unr`:
`Type { level = u, kind = k, scope = S } : Type { level = succ(u), scope = S }`.
A function type's sort is at its closure kind (see
[Closures](#closures)). Its level is computed as below, and its scope unites
its closure scope and its binder types' scopes with its result's, less the
lifetimes the function type binds itself, since the caller supplies them. So
for a family `Lease (l: Lifetime) : Type { scope = l }`, `Lease(m) -> Nat` is at
`Type { scope = m }`, and `(l: Lifetime) -> Lease(l) -> Nat` is at `Type`. A
kind or lifetime binder contributes neither a level nor a scope.

Data sorts permit linear and polymorphic kinds at every data level.
A function type into a proposition must have closure kind `Kind.unr`.

Universes are not cumulative, and neither are kinds and scopes. A value in
`Type { level = u}` does not automatically fit a position expecting a larger
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

Explicit parameters use parentheses. A lambda binds at least one parameter and
writes its result type:

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
The projection reads sorts, function types' closures and the parts of a
function type that do not depend on its own binders, a proof's proposition, a
constructor's stored fields, and the arguments of a family or of a prelude type
former such as `Quot`. It never reads the arguments of a blocked application,
another axiom's or a stuck builtin's: with `axiom f (l: Lifetime): Nat` in the
trusted prelude, `def g {l: Lifetime}(t: Box(f(l))): Nat` is rejected. Nor does
it read through a parameter's application, whose head is a local.

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

### Evidence arguments

An evidence binder `[h: P]` declares a parameter whose argument is a proof of
the proposition `P`. A call does not write it: the checker discharges it by
evaluating `P` where the call stands.

```raccoon
def pred (n: Nat)[h: Eq(Bool, Nat.blt(0, n), Bool.true)]: Nat := Nat.sub(n, 1)

{ pred(5) }
```

An evidence binder stands in a definition's, a lambda's, a function type's or
a constructor's telescope, before, after or between explicit and implicit
binders; a constructor's is an evidence field (see
[Evidence fields](#evidence-fields)). A family's parameters and indices are
never evidence, which is a parse error. `P` must be a proposition, a type whose
sort is `Prop`, else `NotAProposition`, and it may mention only earlier
binders.

At a call that writes no bracket group, each evidence binder's type is
evaluated, with every earlier argument known, to a proposition `P′`. `P′` is
discharged when it is an instance of an inductive family in `Prop` with a
constructor whose fields its result type determines: each field is itself one of
the arguments of the constructor's result type, so its value is read off `P′`
at that position, and the constructor applied to those values has a result type
convertible with `P′`. The constructors are tried in declaration order, and the
proof is the first that fits; a fieldless constructor is one with nothing to
read. Failing that, `P′` is discharged through its evidence fields when its
family is evidence-eligible (see [Evidence fields](#evidence-fields)).
Otherwise the call is `EvidenceNotDischarged`, reported at the call and
showing the proposition that failed.

So `Eq(A, l, r)` is discharged exactly when `l` and `r` evaluate to convertible
values: `Eq.refl`'s field `x` is read off `Eq(A, x, x)` as `l`, and
`Eq(A, l, l)` must be convertible with `Eq(A, l, r)`. `True` is discharged by
`True.intro`. `False`, `Eq(Bool, Nat.blt(0, 0), Bool.true)`, `And(True, True)`,
`Or(…)` and `Exists(…)` are not: a field that the result type does not
determine, or determines only inside an argument, as `m` in `Succ(Nat.succ(m))`,
would have to be invented. A proposition that stays neutral, as in generic code
that knows no concrete argument, is not discharged, but an instance whose sides
convert is: `Eq(Nat, n, n)` is discharged for any `n`. A sealed family's
constructors discharge evidence only in its module, and a family whose block is
still being checked has no constructors yet to discharge with.

A call may instead supply every evidence argument, in a bracket group that
follows its explicit arguments with no space, one proof per evidence binder in
order:

```raccoon
def three (n: Nat)[h: Eq(Nat, n, 3)]: Nat := n

def g (n: Nat)[h: Eq(Nat, n, 3)]: Nat := three(n)[h]
```

This is how generic code forwards a proof it has. Each supplied proof is checked
against its evaluated proposition, a `TypeMismatch` otherwise, and a group of
another length is an `ArityMismatch`. An empty group, and a group that follows
anything but an application's arguments, `f[h]` or `f(a)[h][k]`, are parse
errors. A group is written after the arguments, `f(x)[h]`, in a type as in a
term, and the result may be applied again, `f(x)[h](y)`.

Discharge reads only the callee's type and the call's arguments, never the type
the call is expected to have, and it searches for nothing: no proof in scope is
consulted.

An evidence binder is not explicit. It does not count among the arguments a
call writes, so a definition whose only parameters are evidence is called as
`g()`, in a type as in a term, and `g` alone is the function. It forces no
implicit, supplied or not, so `def f {n: Nat}[h: Eq(Nat, n, 3)]: Nat := n` is
`NonForcedImplicitParam`, as is an implicit proposition that no explicit
argument forces, whose message points to an evidence binder instead.

The binder's mode is part of a function type's identity: `[h: P] -> A` and
`(h: P) -> A` are different types, a lambda `fun [h: P]: A => …` has the first,
and a function type prints its binders as written.

Proofs are erased when a program runs. A call binds its callee's evidence
parameters to erased proofs without evaluating their propositions, whatever the
callee is: a function, or an axiom whose application stores its arguments
unevaluated. So a decision procedure in a proposition runs when a call
is checked, once per call, and not when the call runs. Whatever reads an erased
proof evaluates its proposition then, and sees the proof checking bound: a
match on the parameter, a use of it as an explicit argument, and anything that
uses a stored application's arguments themselves. Comparing, keying and
publishing an application skip its evidence, which its other arguments
determine, and printing shows none.

#### Evidence fields

A constructor's evidence binder is an evidence field, a stored proof that its
value satisfies a proposition over the family's parameters and the earlier
fields:

```raccoon
struct Fin (n: Nat) : Type
 | mk (i: Nat)[h: Nat.lt(i, n)] : Fin(n)

def last : Fin(5) := Fin.mk(5, 4)

def value (x: Fin(5)): Nat := x.i
```

Constructing is applying, so a construction discharges its evidence fields, or
takes them in a bracket group, as a call does its evidence arguments:
`Fin.mk(5, 3)` discharges `Nat.lt(3, 5)`, `Fin.mk(2, 3)` is
`EvidenceNotDischarged`, and generic code forwards a proof, `Fin.mk(n, i)[h]`.
`Fin`'s parameter `n` occurs only in the evidence field's proposition, which
forces nothing, so it is an explicit argument of `Fin.mk`. Implicits written on
a constructor must still be forced by its explicit fields. An evidence field's
type is checked as any field type is, universes and positivity included.

An evidence field is stored like any proof field. A pattern binds it in its
place, `| Fin.mk i h => …`, a destructuring too, `let (i, h) := x`, and a
selector returns it, `x.h`. Proofs being irrelevant, two values that differ
only in an evidence field are equal. When a program runs, a construction stores
an erased proof and evaluates no proposition; printing a value leaves its
evidence fields out, `Fin.mk(4)`.

A proposition whose family is **evidence-eligible** is discharged through its
evidence fields when no constructor's fields are read off it. A family is
eligible when it is declared in `Prop` itself, has one constructor and no
indices, no field type mentions a family of its own block, and every field is an
evidence field:

```raccoon
struct Both (a: Prop)(b: Prop) : Prop
 | mk [x: a][y: b] : Both(a, b)

struct GemmShape (m: Nat)(n: Nat) : Prop
 | mk [mOk: Eq(Bool, Nat.ble(m, 256), Bool.true)][nOk: Eq(Nat, n, 128)] : GemmShape(m, n)

def gemm (m: Nat)(n: Nat)[shape: GemmShape(m, n)]: Nat := Nat.mul(m, n)

{ gemm(256, 128) }
```

Each field's proposition, in order, is evaluated with the family's arguments
and the earlier fields' proofs, and discharged in turn, by either route; the
proof is the constructor applied to those proofs. The arguments may be
anything, functions included:

```raccoon
struct App (f: Nat -> Prop)(n: Nat) : Prop
 | mk [a: f(n)] : App(f, n)

def isFour (n: Nat): Prop := Eq(Nat, n, 4)
```

`App(isFour, 4)` is discharged when `isFour(4)` is. A field that fails is
reported with the path to it, depth first in field order: `gemm(128, 100)`
fails at `GemmShape.nOk: Eq(Nat, 100, 128)`. A family of several constructors
is not recursed into, nor one whose field mentions it, so
`inductive Loop : Prop | mk [h: Loop]` is refused at once. A sealed family is
discharged through its fields only in its module.

Discharge takes at most 1024 such steps on any path from a call's proposition:
one nested deeper, as a chain `Wrap(Wrap(…))` of 1025 built by a recursive
definition, is `EvidenceNotDischarged`, reporting the bound. The bound is part
of the language, so whether a program checks does not depend on how it runs.

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
function type is at its closure's kind and counts its closure's scope. A
function type also belongs to the scopes of what its parameter types and result
type capture, by the rule below for a lambda's captures, other than its own
lifetime parameters: they are code, which runs each time the type is
instantiated. Those scopes are part of the function type, so
`(x: Nat) -> Box(7)` and `(x: Nat) -> Box(use(Lease.mk(l)))` are different
types, though `use` returns 7.

A written function type has no body to derive a closure from, so an omitted
closure field of one is the least, `Kind.unr` or `Lifetime.empty`, and a
definition's own type is always at those. What its code captures is its
mentioned scope above, not its closure.
A lambda's closure is written after `fun`, and each omitted field is derived
from what the lambda captures: the locals bound outside it that its body
mentions, in terms and in types written in the body. Its binder types and
result type are not its body. The derived kind joins the captures' types'
kinds, and the derived scope unites their scopes. A variable of `Lifetime` is a
capture too, which contributes the lifetime it holds: a lambda belongs to every
lifetime its code names, whether a `scope`'s name or a lifetime parameter from
outside the lambda. The lambda's own lifetime parameters are not captures,
since its caller supplies them, and a variable of `Kind` or `Level` contributes
nothing. So `delay`'s lambda, which captures `h: Lease(l)`, has type
`{ scope = l } Unit -> Nat`, as does `fun (u: Unit): Nat => use(Lease.mk(l))`
in `delay`'s body, and a lambda that captures nothing has an unrestricted,
empty closure wherever it stands: checking `fun (u: Unit): Nat => 0` against
`{ scope = l } Unit -> Nat` is a `TypeMismatch`. A written closure field must
contain what the captures derive, else `KindExceeded` or `ScopeExceeded`. That
is also how a function value is lifted to a larger closure:
`fun { kind = k, scope = S } (x: A): B => f(x)`.

A lambda's binder types and result type are its function type's code, so what
they capture belongs to that type, and a parameter's function type written
without the capture does not match it. A callback passed to a combinator keeps
scoped locals in its body: `fun (u: Unit): Nat => use(h)` fits a parameter
`{ scope = S } Unit -> Nat`, while
`fun (u: Unit): Box(use(h)) => Box.mk(7)` fits no parameter `Unit -> Box(7)`,
though `use` returns 7.

## Terms and local blocks

Function application uses parentheses and comma-separated arguments:

```raccoon
f(x, y)
```

The arguments follow the function with no space. `f (x, y)` is a parse error,
since on the same line `(` would otherwise begin a [pair](#pair-expressions) or
a parenthesized term as the next item. A bracket group that supplies a call's
[evidence](#evidence-arguments), `f(x)[h]`, follows the arguments the same way.

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

### Destructuring

`let (a, b) := e` takes apart a value of a one-constructor family without
naming its constructor:

```raccoon
def swap (p: Prod(Nat, Bool)): Prod(Bool, Nat) := {
  let (n, b) := p
  Prod.mk(b, n)
}
```

A pattern is a name, `_`, or two or more patterns in parentheses, separated by
commas; `let (x) := e` is a parse error. A pattern stands only in a block's
`let`, never in a binder, a lambda or a `match` case.

The value is checked as a `let`'s is, against the annotation when one is
written. Its type must be an instance of a structure-eta eligible family (see
[Structs and projections](#structs-and-projections)): one constructor, no
indices, no recursive constructor field, and outside `Prop`. A type a
transparent definition computes to such an instance is one; a type variable, a
function type, and a blocked type are not. Otherwise the
destructuring is `NotDestructurable`, naming the type. An instance of a data family, such as `Prod(A, B)` at levels `u` and `v`,
remains outside `Prop` under every level instantiation.

The components match the constructor's stored fields in order, and erased
family parameters are not fields. A pattern with another number of components
is `ArityMismatch`. There is no flattening: a nested value is taken apart by a
nested pattern, `(e, (a, b))`, which means `let (e, t) := x` followed by
`let (a, b) := t` for a fresh anonymous `t`, so every rule applies at each
level. A name occurs once in a pattern, at any depth, else `AlreadyDefined`, as
in a match case. Names may shadow earlier locals, the scrutinee's included:
`let (e, x) := op(e, y)` is the common form.

Each name, or `_`, binds a local for the rest of the block, transparently, to
its field of the value's eta view: a constructor-headed value's stored field,
or a neutral value's field projection. So a field whose type names an earlier
field has that type at the scrutinee, and a type about a destructured name is
a statement about the scrutinee: after `let (a, b) := p`, `Eq.refl(p)` proves
`Eq(Prod(Nat, Nat), Prod.mk(a, b), p)`. The destructuring's type is the rest of
the block's. Evaluation binds the names the same way, so a destructuring never
blocks, and a destructured name is a structural subterm of the scrutinee, as a
match's field is.

A destructuring is a match on its value. The value is a use of every local it
mentions, so destructuring a linear value consumes it. Each name is tracked by
its field's type: a linear field bound to `_`, or not used on some path, is
`LinearUnused`, and one used twice is `LinearReused`. Outside a sealed family's
module, destructuring a value of it is `SealedConstructor`.

### Pair expressions

A term `(a, b)` is the active prelude's `Pair.mk(a, b)`, and a destructuring
takes it apart:

```raccoon
def swap {k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}(a: A)(n: Nat): Pair(Nat, A) := {
  let (x, y) := (a, n)
  (y, x)
}
```

`Pair.mk` is looked up from the root among the active prelude's declarations,
so no local, namespace, `open` or declaration of the program named `Pair` or
`mk` changes what a pair expression means. A program cannot redeclare a
prelude's `Pair.mk`; where the active prelude declares none, a pair expression
is `NotFound`, even in a program that declares its own `Pair.mk`, which is
applied only by name. A prelude's own pair expression names the `Pair.mk` it
has declared before it. Otherwise a pair is checked as that application, so
its type comes from its components: `Pair.mk` forces its implicits from their
types, `(1, Bool.true)` is a `Pair(Nat, Bool)`, and a pair with a linear
component is linear. Each component is a use of the locals it mentions.

A pair expression has exactly two components; `(a, b, c)` is a parse error, and
`(a, (b, c))` is written instead. `(e)` is `e`, and `((a, b))` is a pair. A
pair is a value that trailers apply to as to any other: `(a, b).f` selects and
`(f, g)(x)` applies it.

An argument of an application is a term, in a type as anywhere, so a type may
hold a pair expression as an argument: `Eq(Pair(Nat, Nat), p, (1, 2))`. There
is no pair type syntax: a type is written `Pair(A, B)`. Where a type stands, as
a binder's type, a declared or annotated type, a `returning` motive, or a
function type's domain or result, `(` begins a parenthesized type or a binder
group, and a pair there, as in `(p: (Nat, Nat))`, is a parse error. In a term
position `(Nat, Bool)` is a pair of types, a value of `Pair(Type, Type)`.

### Scopes

`scope l => e` opens a scope named `l`, binds `l` to the lifetime naming it,
and denotes the value of `e`. Its type is `e`'s type. The scope is open while
`e` runs and closed afterwards. A value belongs to a scope when its type
mentions it, and once the scope closes, nothing can hold, create or use a value
that belongs to it. `scope` is a keyword at
the start of a term, and a field name inside a field list; the body extends as
far to the right as a lambda body does:

```raccoon
inductive Lease (l: Lifetime) : Type { scope = l }
 | mk : Lease(l)

def use {l: Lifetime}(h: Lease(l)): Nat := 0

def ok : Nat := scope l => use(Lease.mk(l))
```

The scope is unique to the `scope` term: two `scope` terms open two scopes,
while running one term twice, a recursive call included, opens the same one.
Printed output spells a scope as its binder.

Outside its `scope` term, a scope cannot be named in a type. A type whose
sort's scope names a scope that does not enclose it is `LifetimeEscapes`. That
is checked on every type a term has or is checked against, on the type of every
local at its binder, and on every argument that is a type, which is confined
through its own sort. So `use(scope l => Lease.mk(l))` is rejected: the
`scope`'s own type `Lease(l)` is at `Type { scope = l }`, which names `l` where
it is no longer open. So is `def T : Type := scope l => Lease(l)`, whose body's
type is that sort.

What a value belongs to is read off its type's sort: data belongs to the scopes
its family's arguments name, a function to the scopes of what it captures and
of the lifetimes its code names, and a type to its own sort's scope. So
`scope l => fun (u: Unit): Nat => use(Lease.mk(l))` is rejected as well: the
lambda names `l`, so its type is `{ scope = l } Unit -> Nat`, which cannot
leave. Applied inside the scope it is accepted, and so is
`scope l => fun (u: Unit): Nat => 3`, which belongs to no scope. A computation
blocked on an axiom or a builtin, and a proof, may hold a scope's lifetime
without belonging to it, since neither runs, and no implicit reads it back out.

A scope's name is not a variable: matching never links it to another lifetime,
while a lifetime variable may be linked to it. Nothing checks a `scope` at run
time.

## Inductive families

Parameters before `indices` are uniform across every constructor result.
Binders after `indices` are indices and may vary between constructors.

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (pred: Nat) : Nat

inductive Vec {u: Level}(A: Type { level = u}) indices (n: Nat)
    : Type { level = u}
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
- the declared scope names exactly the family's lifetime parameters: it may
  mention only parameters, and must name each lifetime parameter, else
  `ScopeExceeded` naming it, since a forced implicit reads the lifetime off an
  instance's type. So `inductive Wrap (l: Lifetime) : Type` is rejected, and
  declares `Type { scope = l }` instead.

Only a parameter binds a lifetime, so each constructor field's scope, and the
scope of each parameter's and index's type, lies within the declared scope and
needs no check of its own. A type parameter counts at its sort's scope, which
names a lifetime parameter.

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
the same common parameter telescope, as required by the trusted Core block, but
each may be at its own sort: a `Type` family and a `Prop` family, or a linear
token and an unrestricted factory of them, may be siblings. Each family is
checked against its own declared sort, so siblings that hold each other are
bounded at each field. Generated structure selectors are declared
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

A match's last case may be the wildcard `| _ => e`, which stands for a case
for each reachable constructor the other cases do not name, binding its fields
anonymously:

```raccoon
def isZero (n: Nat): Bool := {
  match n returning Bool with
  | Nat.zero => Bool.true
  | _ => Bool.false
}
```

`e` is checked once for each constructor it stands for, under that case's own
refinement, as if the case were written out with `_` for each field; a
diagnostic in one of them names its constructor. A constructor apart from the
scrutinee's family instance needs no case, so the wildcard does not stand for
it. A wildcard that stands for no constructor is `RedundantCase`. A wildcard
anywhere but last, a second one, or one that binds fields is a parse error. A
nested match takes every case that follows it, so a match nested in a case
other than the last is written in braces. The wildcard covers whole
constructors: there are no nested patterns. Because `e` is checked once per
constructor, matching the same scrutinee again inside `e` needs, in each of
those checks, only the case for that constructor.

### Naming the equation

`match h : e returning M with …` names the match's equation `h`. In the case
for constructor `C` with fields `x̄`, `h` is a proof of
`Eq(T, e, C(p̄, x̄))`, where `T` is `e`'s type, `p̄` its parameters and `e` the
scrutinee as written. So a case knows what a computed value was computed from,
and can pass that fact on, for example as evidence:

```raccoon
def needs (n: Nat)(c: Nat)[fits: Nat.le(Nat.mul(8, Nat.succ(c)), n)]: Nat := c

def loadFrom (n: Nat)(c: Nat)(left: Nat): Nat decreases structural(left) := {
  match left returning Nat with
  | Nat.zero => 0
  | Nat.succ more => {
    match fits : Nat.ble(Nat.mul(8, Nat.succ(c)), n) returning Nat with
    | Bool.true => Nat.add(needs(n, c)[fits], loadFrom(n, Nat.succ(c), more))
    | Bool.false => 0
  }
}
```

`Nat.le(a, b)` is `Eq(Bool, Nat.ble(a, b), Bool.true)`, so in the `true` case
`fits` is the evidence `needs` asks for; without it the application is
`EvidenceNotDischarged`, since the test is stuck on `n`.

`h` is in scope in every case, after its fields, and nowhere else: not in the
scrutinee or the motive. It is a proof, so it may be used any number of times.
Nothing is rewritten by it: the motive and the other hypotheses keep mentioning
`e`, and a proof that needs `e` replaced uses `h` with `Eq.subst`. With a
wildcard, each case the wildcard stands for has its own `h`, at its own
constructor. The scrutinee's family must have no indices, else
`MatchEquationIndexed`, and its type must be unrestricted: a scrutinee of
linear type would put a token in a proposition, which is `LinearInType`. The
equation is stated with the prelude's `Eq`, which must be the equality family;
otherwise, and in the prelude's own declarations, a named equation is
`MatchEquationUnavailable`.

When the program runs, a case is taken only when the scrutinee's value `v` is
its constructor applied to its fields, so `h` is the canonical proof,
`Eq.refl(v)`; it is evaluated only if something looks at it. A residual match
keeps its equation and prints as `match h : e`.

### Result types and `returning`

A match result type is its motive, which every match writes with
`returning`:

```raccoon
match xs returning Vec(A, n) with
| Vec.nil => Vec.nil(A)
| Vec.cons k tail head => xs
```

The clause continues the match header, so it may start the next line, as an
arrow of a function type may. A match without `returning` is a parse error,
and a motive that is not a type is `NotAType`. Each branch is checked against
the motive under the branch's refinements. The match's type is the motive,
evaluated where the match stands, whether or not the match reduces.

Elimination from `Prop` is restricted. A Prop-valued result is always allowed.
A data-valued result is allowed only for an empty reachable constructor set or
when the exact proposition determines every constructor field. See
[Proofs and elimination](kernel.md#proofs-and-elimination).

## Linear types

A type is linear when its kind is not `Kind.unr`: a family declared at
`Kind.lin`, or at a kind variable its instance makes linear; a function type
whose closure kind is not `Kind.unr`; or a type variable whose sort's kind is
not. A kind variable counts, since some instantiation makes it `Kind.lin`.
Sorts and propositions are never linear. Values of a linear family are made by
its constructors and consumed by `match`.

Every local of linear type is used exactly once within its binder's extent,
whether a lambda's or definition's parameter, a `let` or a pattern field binds
it, `_` included. Uses are counted along each path that takes one branch at
every `match`, and any occurrence is a use:

```raccoon
inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
 | mk : Tok(l)

def eat {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with
 | Tok.mk => 0

def pick {l: Lifetime}(b: Bool)(t: Tok(l)): Nat := match b returning Nat with
 | Bool.true => eat(t)
 | Bool.false => Nat.succ(eat(t))
```

Leaving out `eat(t)` in one branch is `LinearUnused(t)`, reported at the
binder, and `Nat.add(eat(t), eat(t))` is `LinearReused(t)`, reported at the
second use. A path that reuses a local is reported as reused, even where
another path leaves it unused. Matching a linear value consumes it, and its
fields must each be used once in the branch, so `_` for a linear field is
`LinearUnused`. A [destructuring](#destructuring) consumes its value the same
way, and each local it binds is used once in the rest of the block. A match
with no branch ends every path through it and so uses every linear local still
unused there; nothing after it is on those paths. A `decreases` clause is not a
use. Applying a struct selector to a linear value consumes the value.

A lambda's body runs only when the lambda is applied, so it is not on the
paths around it, and a match with no branch inside it ends none of them. A use
of an outer local inside a lambda is one use, by the lambda, at the lambda's
position, and the lambda must use it exactly once on every path through its
body. A lambda that captures a linear local is itself
linear, its derived closure kind is `Kind.lin`, and writing it at `Kind.unr` is
`KindExceeded`. A value of a linear function type is used by applying it, so
it is applied exactly once.

Binders are exact about kinds: `{A: Type}` accepts only unrestricted types and
`{A: Type { kind = lin }}` only linear ones. A position that accepts both takes
a kind variable, and a local whose type is at that variable is tracked, so the
one definition consumes its argument in every instantiation:

```raccoon
def pass {k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}(x: A): A := x

def apply {kf: Kind}{Sf: Lifetime}(f: { kind = kf, scope = Sf } Unit -> Nat): Nat := f(Unit.unit)
```

`pass(3)` and `pass(t)` both check, as do `apply` of a lambda that captures a
token and of one that captures nothing. A definition that drops or copies its
argument exists only at `Kind.unr`.

A value outside every binder is never tracked, so a definition whose type is
linear is `LinearGlobal`, and so is a program whose
final `{ … }` result has a linear type: nothing would ever use it, so a client
could end the program holding a module's token. Axioms belong to the trusted
prelude. A definition's own function type is unrestricted, so a definition that
takes or returns tokens is an ordinary global.

Types and proofs hold no tokens. A term whose type is a sort or a proposition
may not contain a subterm of linear type, which is `LinearInType`, reported at
that subterm. That covers a binder type such as `Eq(Nat, eat(t), 0)`, a type
computed by a definition, a `returning` motive, and a proof: a definition
whose type is a proposition cannot consume a token, and so cannot take one. A lambda that
consumes its own linear parameter is refused inside a type too; name it by a
definition and refer to it by name instead. So no type mentions a linear local,
and an implicit binder of linear type is never forced, which is
`NonForcedImplicitParam`. Facts about a token are stated about its indices,
which are unrestricted:

```raccoon
inductive Coin (l: Lifetime) indices (n: Nat) : Type { kind = lin, scope = l }
 | mk (n: Nat) : Coin(l, n)

def spend {l: Lifetime}{n: Nat}(c: Coin(l, n))(p: Eq(Nat, n, 1)): Nat := match c returning Nat with
 | Coin.mk m => m
```

A struct selector binds every field and returns one, so a selector of a linear
struct is rejected when another field is linear (`LinearUnused`), when its
field's type names an earlier field, since its result type then applies that
field's selector to the struct value (`LinearInType`), and when its field is a
proof (`LinearInType`). The struct and its other selectors are still declared;
match on the constructor instead.

## Recursive definitions

A recursive function must carry a `decreases` clause:

```raccoon
def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
  match b returning Nat with
  | Nat.zero => a
  | Nat.succ p => add(Nat.succ(a), p)
}
```

The clause continues the definition's header, so it may start the line after
the result type, and its specification the line after `decreases`, in a
`mutual` group as anywhere:

```raccoon
def add (a: Nat)(b: Nat): Nat
    decreases structural(b) := {
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
struct Cursor {u: Level}(A: Type { level = u}) : Type { level = u}
 | mk (remaining: List(A)) : Cursor(A)

def countRemaining {u: Level}{A: Type { level = u}}(cursor: Cursor(A)): Nat decreases measure(cursor.remaining) := {
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
struct Couple (A: Type)(B: Type) : Type
 | mk (fst: A)(snd: B) : Couple(A, B)

def first {A: Type}{B: Type}(p: Couple(A, B)): A := p.fst
```

A struct declaration has exactly one constructor. Every named stored field
gets a selector in the family namespace, so `p.fst` and `Couple.fst(p)` are the
same ordinary function application. A selector is a match on its parameter
`self` that returns the field, with the field's type as its `returning` clause.
An `_` field remains stored but gets no selector.

Structure eta is based on the checked family shape, not the `struct` keyword.
Any non-Prop family instance is eta-eligible when it has exactly one
constructor, no indices, and no recursive constructor field, sealed or not. A plain
`inductive` can therefore receive eta without receiving named selectors.
Indexed or recursive singleton families still have positional metadata used by
generated selectors, but they do not receive eta.

A value of an eta-eligible family is also taken apart by its fields at once,
without naming its constructor, by a
[destructuring](#destructuring) `let (a, b) := p`, which binds each field of
its eta view.

For a Prop-valued instance, proof representation and elimination rules replace
data structure eta. A selector out of a proposition is an ordinary match and
must obey the same elimination restriction as any other match.

## Sealed families

A family declared `sealed inductive` or `sealed struct` keeps its constructors
and selectors to its module, the `.rac` file that declares it. Every other
module sees its head, parameters, indices and sort, and may use the module's
definitions, but outside the module each of these is `SealedConstructor`:

- naming one of its constructors, applied or not;
- selecting one of its fields, as `b.n` or `Box.n(b)`;
- matching on a value of it, with qualified or `.short` case heads;
- destructuring a value of it, `let (a, b) := v`.

The names still resolve, so such a use reports `SealedConstructor` rather than
an unknown name. A value of a sealed family is therefore made and taken apart
only by its module, which is what makes a capability confine anything:

```raccoon
// Lease.rac
sealed inductive Lease (l: Lifetime) : Type { scope = l }
 | mk : Lease(l)

def withLease {k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}{kf: Kind}{Sf: Lifetime}
    (f: { kind = kf, scope = Sf } (l: Lifetime) -> Lease(l) -> A): A :=
  scope l => f(l, Lease.mk(l))
```

Another module calls `withLease(fun (l: Lifetime)(h: Lease(l)): Nat => 0)`, but
`Lease.mk(l)` there is `SealedConstructor`. `withLease` serves every callback:
`A`, `k` and `S` are read off the callback's result type, and `kf` and `Sf` off
its closure, so a callback that captures a token is linear and one that
captures nothing is not. Since `A` is bound outside the callback's lifetime
binder, a callback cannot return anything whose type names `l`, such as the
lease itself: its result type depends on the binder, so `A` cannot be
reconstructed. `examples/leases` is a runnable module and client that use it.

An implicit parameter may be forced through a sealed constructor's field only
inside the family's module; elsewhere it is `NonForcedImplicitParam`. The
module's own definitions that force one that way can be applied anywhere, and
an implicit argument the checker reconstructs may be a sealed constructor
application.

Every value of a sealed family comes from its constructors, since only the
trusted prelude declares axioms and builtins, and none of them yields a value
of a sealed family except by applying its constructors (obligation T2 of the
[trusted bootstrap](kernel.md#trusted-bootstrap-and-native-values)). So
structure eta and proof reconstruction apply to a sealed family as to any
other, and open nothing its module did not build.

```raccoon
// Permit.rac
sealed inductive Permit (l: Lifetime) : Prop
 | mk : Permit(l)

sealed inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
 | mk : Tok(l)

def redeem {l: Lifetime}(p: Permit(l)): Tok(l) := match p returning Tok(l) with
 | .mk => Tok.mk(l)

def grant (n: Nat): Permit(Lifetime.empty) := Permit.mk(Lifetime.empty)
```

A proof function's body never runs, so `grant(0)` is the proof of
`Permit(Lifetime.empty)` reconstructed from its proposition, which is
`Permit.mk(Lifetime.empty)`. Any module may call `redeem(grant(0))`, and it
reduces to a token.

Sealing restricts what a program may write, not what the checker knows: kinds,
scopes, coverage, apartness and conversion use the full declaration in every
module.

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
2. in a sort or closure field, one of that field's forms;
3. in the body of a recursive definition or `mutual` group, a member of the
   group, when the whole path names it as it would name its global;
4. the current namespace, from most specific to the root;
5. aliases in the current open scope.

A definition's own name and its peers' are not locals, which is why a field's
forms win over them. If the first segment is local, the remaining path is
projection syntax. Once a global first segment is selected, resolution
continues inside that object and does not backtrack to another open. Where no
child matches, the rest of the path is projection syntax from the object's
declaration, or `NotFound` when the object is only a namespace. A
projection from anything whose type is not a family instance has no selector,
so it names nothing: `Nat.mod`, where `Nat` has no child `mod`, is `NotFound`
for `Nat.mod`, in a term as in a type. Prefix a path with `_root_.` to bypass
locals, a field's forms, the current namespace, and opens.

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
once, and import cycles are rejected. Each file is its own module, which is
what a sealed family's seal refers to. Imported declarations keep their
canonical names and are not opened automatically.

`Init.Prelude` is loaded automatically by the normal CLI. An explicit
`import Init.Prelude` is accepted as a no-op with the bundled or custom
prelude configuration.

## Bundled prelude

The bundled prelude defines the ordinary logical and data vocabulary used by
the examples and tests, including:

- `Eq`, `False`, `True`, `And`, `Or`, `Iff`, and `Not`;
- `Empty`, `Unit`, `Bool`, `Nat`, `Option`, `Sum`, `List`, `Prod`, and `Sigma`;
- `Pair`, a pair whose components may be linear or scoped: it holds values
  of types at any level above `Prop`, is at the join of their kinds and the
  union of their scopes, has no selectors, is written `(a, b)` (see
  [Pair expressions](#pair-expressions)), and is taken apart by `match` or a
  destructuring, while `Prod` stays the unrestricted pair with selectors;
- `Decidable`, `Subtype`, `Exists`, `Nonempty`, and common boolean and natural
  operations;
- `Quot` with `Quot.mk`, `Quot.sound`, `Quot.lift`, and `Quot.ind`.

Its polymorphic declarations are lifetime-polymorphic. Each takes a lifetime
variable beside each type parameter, `Prop`-valued ones included, one for the
sort of each type-family parameter's result, and one for each function-typed
parameter's closure scope. All of them are forced implicits, so no call site
writes them:

```text
inductive List {u: Level}{S: Lifetime}(A: Type { level = u, scope = S })
    : Type { level = u, scope = S }

def List.map {u: Level}{v: Level}{S: Lifetime}{T: Lifetime}{Sf: Lifetime}
    {A: Type { level = u, scope = S }}
    (xs: List(A))(B: Type { level = v, scope = T })(f: { scope = Sf } A -> B)
    : List(B)

def Eq.subst {u: Level}{S: Lifetime}{Sm: Lifetime}{Sc: Lifetime}
    {A: Type { level = u, scope = S }}{x: A}{y: A}
    (p: Eq(A, x, y))(v: Level)(motive: { scope = Sc } A -> Type { level = v, scope = Sm })
    (h: motive(x)): motive(y)
```

So for a family `W (l: Lifetime) : Type { scope = l }`, `List(W(l))` is at
`Type { scope = l }`, `Eq(W(l), a, b)` is at `Prop { scope = l }`, and a lambda
passed to `List.map` may capture a `W(l)`. A family declares the union of its
parameters' scopes, as `Prod` declares `scope = union(S, T)`. No global's type
names an atom, so every prelude declaration is at `Lifetime.empty`, a lifetime
variable, or a union of them.

A family's function-typed field cannot have a closure-scope variable of its
own, since nothing in an instance's type would force it. It takes the family's
own scope as its closure scope instead, as in
`BEq {u: Level}{S: Lifetime}(A: Type { level = u, scope = S })` with
`mk (beq: { scope = S } A -> A -> Bool)`: the closure may hold what the
family's values may already depend on, and adds nothing to the family's scope.
`Iff`, `DecidableEq`, `LE`, `LT` and `Subsingleton` do the same, and `LE.le` and
`LT.lt` return propositions at that scope too. `Not(a)` is a function type at
`a`'s scope, `{ scope = S } (h: a) -> False`. So `listBEq` can build a `BEq`
from a lambda that captures a `BEq(A)`. Proposition-target eliminators use
suffix `P`: `False.elimP` and `Eq.substP`; their data-target counterparts
range over `Type { level = u }`.

The prelude source is authoritative for its exact API:
`src/main/resources/Init/Prelude.rac`.
