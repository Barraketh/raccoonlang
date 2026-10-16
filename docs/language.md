# Raccoon language

## Programs and declarations

A file contains imports, declarations, and an optional final expression.
Definitions, axioms, inductive families, structs, namespaces, and mutual blocks
are supported:

```raccoon
def identity (A: Type)(x: A): A := x
axiom assumed : Prop

inductive Peano : Type
 | zero : Peano
 | succ (previous: Peano) : Peano

{ identity(Peano, Peano.zero) }
```

Every definition is transparent and reduces during checking and evaluation.
Axioms introduce explicit assumptions in any module and have no body.
`:= builtin` is reserved for the selected prelude's primitive quotient
declarations.

Checking collects independent errors in source order. Declarations that depend
on a failed declaration are skipped. The final expression is evaluated only
when checking succeeds. `--json` emits diagnostics as one JSON array.
Missing qualified names report the full spelling that was written. Function
and constructor arity errors name explicit parameters and, when known, family
parameters inferred from other arguments. `--stack <size>` optionally runs the
pipeline on a thread with that stack size; without the option, the JVM's normal
thread-stack default is unchanged. Stack exhaustion is reported as
`EvaluationTooDeep`.

## Universes

`Prop` is the universe of propositions and has type `Type`. Bare `Type` denotes
data universe zero, the same universe written `Type { level = Level.zero }`.
`Type { level = u }` denotes data universe `u` and has type
`Type { level = Level.succ(u) }`. `Type` fields range only over data
universes; `Prop` remains separate. Universe conversion is exact, with no
cumulativity.

`Level` is a second-class parameter admitted in declaration headers and family
parameters. `Level.zero`, `Level.one`, `Level.succ(u)`, and `Level.max(u, v)`
form level expressions. Inside a `Type` level field, the short names are
available. Every form requires its exact arity.

```raccoon
def id {u: Level}{A: Type { level = u }}(x: A): A := x
```

Level expressions are admitted in universe fields and arguments at level
parameters. They are not ordinary values that can be stored in an inductive
field or returned as program results.

## Functions and binder groups

All lambda parameters and result types are explicit in syntax:

```raccoon
fun (A: Type)(x: A): A => x
```

An arrow chain forms one argument group: `A -> B -> C` takes two arguments and
is applied as `f(a, b)`. Parentheses create a nested group:
`A -> (B -> C)` is applied as `f(a)(b)`. Grouping and implicitness are part of
a function type's identity.

Implicit binders use braces, as `{A: Type}`. They must be forced by the types
of later explicit arguments. A call supplies only explicit arguments; the
checker reconstructs implicits and then verifies all argument types. No
heuristic unification guesses omitted arguments.

Locals may be used, copied, captured, or discarded without resource annotations.
A function type consists of its dependent binders and result type.

## Terms and local blocks

Terms include names, applications, lambdas, function types, sorts, matches,
field selections, and local blocks:

```raccoon
{
  let n: Nat := 2
  let next := Nat.succ(n)
  Nat.add(next, n)
}
```

Numerals expand to ordinary applications of `Nat.zero` and `Nat.succ`. The
prelude's natural-number operations are recursive source definitions, so large
numerals and arithmetic can be expensive. String literals are not supported.

## Inductive families

Parameters precede `indices`; constructor fields follow each constructor's
name. Constructor results must use the family's uniform parameters.

```raccoon
inductive Vec {u: Level}(A: Type { level = u }) indices (n: Nat)
    : Type { level = max(one, u) }
 | nil : Vec(A, Nat.zero)
 | cons (n: Nat)(tail: Vec(A, n))(head: A) : Vec(A, Nat.succ(n))
```

Fields must be strictly positive and satisfy universe bounds. Parameters and
indices are checked elementwise by the universes of their types, including
through data-valued function types. For example, a family parameter
`F: Type -> Type` requires the family result to be at least
`Type { level = one }`, since `Type` itself lives in Type1. `mutual { ... }`
groups mutually dependent families with a shared parameter telescope. The whole
block succeeds or fails together, with positivity scans scoped to that block.

## Pattern matching

Every match writes its result type after `returning`:

```raccoon
def pred (n: Nat): Nat := match n returning Nat with
 | .zero => Nat.zero
 | .succ previous => previous
```

A branch may use a qualified constructor name or a short `.constructor` name.
It binds one variable per stored field; `_` discards a field. The checker
refines indices and requires all reachable cases. Matching a proposition
family at the scrutinee's root can refine its indices; that does not invert a
proposition family buried inside an equality index. When the checker proposes
that a case is impossible, it must check a contradiction in the original
environment; unsupported quotations or failed checks keep the case reachable.
A failed equality check alone does not prove a case impossible. Proof
irrelevance and controlled elimination from `Prop` follow the
[kernel rules](kernel.md#proofs-and-elimination).

## Recursive definitions

Recursion requires `decreases structural(argument)`,
`decreases lexicographic(first, second)`, or `decreases measure(term)`. The
clause may continue the header on a later line:

```raccoon
def size (n: Nat): Nat
    decreases structural(n) := match n returning Nat with
 | .zero => 0
 | .succ previous => Nat.succ(size(previous))
```

Calls must decrease structurally in the declared metric. Recursive functions
cannot be passed around as values while checking their own bodies. A
`mutual { ... }` group may contain recursively calling definitions; every
member requires a compatible decrease annotation. Tail calls in a branch's
final expression or a block's result run without growing the evaluator's call
stack.

Blank and comment-only lines may separate declarations, statements, cases, and
constructors. A nested match continues through blank lines until another case
or a block boundary ends it; braces make that boundary explicit when needed.

## Structs and projections

A `struct` has one constructor and generates selectors for its named fields:

```raccoon
struct Pair (A: Type)(B: Type) : Type
 | mk (first: A)(second: B) : Pair(A, B)
```

`p.first` resolves to `Pair.first(p)`. Selectors are ordinary functions
implemented by pattern matching. Eligible data structures have structure eta.
Constructors and selectors are accessible from importing modules.

## Namespaces and names

`namespace Name { ... }` qualifies declarations. `open Name` makes members
available locally; `open Name.{member, old as renamed, -excluded, *}` controls
aliases. Opens inside blocks affect subsequent statements in that block.
Locals take precedence over opened names. `_root_.Name.member` resolves an
absolute global name.

## Imports

`import A.B` loads `A/B.rac` from a source root. The entry file's directory is
the default root; repeat `--root <directory>` to add roots. Imported modules
contain declarations without a final program expression. Import cycles,
missing modules, and module parse errors produce diagnostics.

## Bundled prelude

The bundled `Init/Prelude.rac` supplies equality, propositions, booleans,
natural numbers, lists, options, sums, products, dependent pairs, subtypes,
decidability helpers, and quotients. Its definitions are polymorphic in universe
levels where applicable.

Use `--prelude <file>` to select a custom prelude or `--no-prelude` to start
with only the kernel's universe forms. A custom prelude is checked as ordinary
source and does not need any particular numeric or string layout.
