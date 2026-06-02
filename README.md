# Raccoon Lang

Raccoon is a small dependently typed language aimed to be a target for AI-assisted proof generation,
as well as a research platform for exploring language features to make formally-verified programming more ergonomic.

## Language design philosophy

- Fast typechecking / compilation
- Ergonomic, but not at the cost of typechecking speed
- Consistent
- Small kernel core, with a bias toward keeping some traditionally elaborator-side mechanisms explicit in the kernel
  when that simplifies the overall system. Current examples:
    - Universe level normalization and unification
    - Type-driven expression normalization (see `docs/normalizers.md`)
    - Type Patterns

## A motivating benchmark

The benchmark suite in [benchmarks](benchmarks/readme.md) includes a generated nested dependent `Vec.zip`
stress test. It builds a chain of inferred dependent vector zips and then consumes the final value, so elaboration
and typechecking must keep a large indexed-vector type live. The benchmark shape is

```text
z1 := zip(v, v)
z2 := zip(v, z1)
...
zN := zip(v, zN-1)
consume(zN)
```

Current results on my M1 laptop:

| nested zips | Raccoon JVM | Lean 4.31 nightly |
|------------:|------------:|------------------:|
|         800 |      0.465s |            2.872s |
|       1,600 |      0.558s |            9.915s |
|       3,200 |      0.692s |           41.274s |
|       6,400 |      0.889s | timed out at 180s |
|      51,200 |      3.435s |               N/A |

Note that at this point I have done 0 optimization - these performance wins are strictly algorithmic.

## Implemented today

- Inductive families with explicit params, indices, and erased constructor binders
    - Validates positivity, universes, constructor result shape, and uniform params
- Termination checking of recursive functions
- Dependent pattern matching
    - Branch refinement for indexed families / dependent pattern matching. Supports equality proofs.
    - Validates exhaustiveness checking: missing, duplicate, and unreachable branches
- Cumulative universes, first-class `Level`, `Sort(u)`, universe validation, and sort unification
    - `Prop` is `Sort(Level.zero)`; `Type` is `Sort(Level.one)`
    - Impredicative Prop with proof irrelevance and controlled large elimination
- Extensible definitional equality through type-driven expression normalization
- Namespaces, file imports, dotted names, and scoped `open`
- Type patterns
- Type classes with `def instance`, `let instance`, `[f: Foo]` instance binders, and explicit `derive[Foo]`
  search
- Structs / Projections
- Quotients
- JVM CLI plus Scala Native build

## A few concrete examples

### Inductives and Pattern Matching

Inductives can split family arguments into uniform params and non-uniform indices with `indices`, and their result
can live in an explicit universe. Constructors can bind erased arguments with `{...}` for params that should be
supplied but not stored as fields; indices are supplied by ordinary fields, fixed result expressions, or type-pattern
captures. This includes universe-polymorphic inductives whose fields and result type are parameterized by a `Level`.

Pattern matches are checked for exhaustiveness. Required constructors must be present, duplicate cases are rejected,
and constructors that are impossible at the scrutinee's family type can be omitted.

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

inductive Box (u: Level)(A: Sort(u)) : Sort(u)
 | mk {u: Level}{A: Sort(u)} (value: A) : Box(u, A)

inductive Vec (u: Level)(A: Sort(u)) indices (n: Nat) : Sort(Level.max(Level.one, u))
 | nil {u: Level}{A: Sort(u)} : Vec(u, A, Nat.zero)
 | cons {u: Level}{A: Sort(u)} (n: Nat)(xs: Vec(u, A, n))(x: A) : Vec(u, A, Nat.succ(n))

inductive NatShape indices (n: Nat) : Type
 | isZero : NatShape(Nat.zero)
 | isSucc (n: Nat) : NatShape(Nat.succ(n))

def pred (n: Nat): Nat := {
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ x => x
}

def zeroShapeOnly (shape: NatShape(Nat.zero)): Nat := {
  match shape returning Nat with
  | NatShape.isZero => Nat.zero
}
```

In `zeroShapeOnly`, the `NatShape.isSucc` branch is unreachable because the scrutinee has type
`NatShape(Nat.zero)`, so the match is still exhaustive without that constructor.

### Termination Checking

Recursive functions must say why recursive calls are smaller. A `structural` annotation names one inductive parameter,
and each recursive call must pass a strict constructor subterm in that position. A `lexicographic` annotation checks a
sequence of parameters: an earlier component may decrease, or an equal prefix can be followed by a later decrease. A
`measure` annotation checks that an evaluated inductive-valued measure gets structurally smaller.

The recursive function name is available only for direct recursive calls while checking the body. It cannot be stored in
a `let`, passed as an argument, returned, or hidden inside another value.

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

stable def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
  match b with
  | Nat.zero => a
  | Nat.succ x => add(Nat.succ(a), x)
}

def lex (a: Nat)(b: Nat): Nat decreases lexicographic(a, b) := {
  match a with
  | Nat.zero => {
    match b with
    | Nat.zero => Nat.zero
    | Nat.succ b0 => lex(Nat.zero, b0)
  }
  | Nat.succ a0 => lex(a0, b)
}
```

### Type patterns

An alternative to implicit parameters. A binder can contain captures in the type, and later parameters can reference
these captures. See example below. You declare a capture with a '$'[name] . When applying a function,
these patterns bind the incoming type like regular pattern matches in a language like Lean. A failure to match will
result in a typecheck failure. This feature allows us to greatly reduce the number of function params - zip would
otherwise have 7 params.

```raccoon
inductive Nat : Type
  | zero : Nat
  | succ (_: Nat) : Nat

inductive Vec (A: Sort($u)) indices (n: Nat) : Sort(Level.max(Level.one, u))
  | nil {A: Sort($u)}: Vec(A, Nat.zero)
  | cons {A: Sort($u)} (v: Vec(A, $n))(elem: A): Vec(A, Nat.succ(n))

inductive Pair (A: Sort($u1))(B: Sort($u2)): Sort(Level.max(u1, u2))
  | mk(a: $A in Sort($u1))(b: $B in Sort($u2)): Pair(A, B)

def zip(va: Vec($A, $n))(vb: Vec($B, n)): Vec(Pair(A, B), n) decreases measure(n) := {
  let ResType := Vec(Pair(A, B), n)
  match va returning ResType with
  | Vec.nil => Vec.nil(Pair(A, B))
  | Vec.cons va0 a => {
    match vb returning ResType with
    | Vec.cons vb0 b => Vec.cons(Pair(A, B), zip(va0, vb0), Pair.mk(a, b))
  }
}
```

### Structs and Projections

A struct is a special case of an inductive family with exactly one constructor and named fields. Structs are intended
for record-like data where fields are directly projectable by name.
Formation rules:

- Exactly one constructor.
- Params before `indices` must be returned uniformly by every constructor.
- Indices may be fixed by the constructor result or recovered from stored fields and type-pattern captures.
- May live in `Type`/`Sort(u)` or `Prop`; projections from `Prop` structs obey Prop elimination restrictions.
- All fields must be named (no anonymous `_` fields).

Projection syntax: `p.field` selects the named field from a value `p` of a struct family.

Example: simple non-dependent projections

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

struct Pair (A: Type)(B: Type) : Type
 | mk {A: Type}{B: Type} (fst: A)(snd: B) : Pair(A, B)

def first (p: Pair($A, $B)): A := p.fst
def second (p: Pair($A, $B)): B := p.snd
```

### Type Classes

An instance is an ordinary definition or local binding marked as an instance, and instance search runs only where a term
expression explicitly asks for it with `derive[Goal]`.

Bracket binders such as `[x: T]` are instance-marked binders. They are still ordinary positional arguments at call
sites, but the bound value is registered for local instance search while checking the binder's scope. This lets instance
functions declare searchable dependencies with type-pattern captures, and lets function bodies call `derive[...]`
against instance-marked parameters.

Search uses lexical priority and stops at the first successful candidate in a tier. Local instance bindings are
searched before globals, with newer local bindings tried first. If a local candidate succeeds, globals are not
considered. Globals are searched only when no local candidate succeeds. This means a local instance can intentionally
override a global one without creating ambiguity, and overlapping instances are resolved by search order rather than by
ambiguity detection.

```raccoon
struct DecEq (A: Type) : Type
 | mk {A: Type} (result: Bool) : DecEq(A)

inductive List (A: Type) : Type
 | nil : List(A)

def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)

def instance listEq [ea: DecEq($A)]: DecEq(List(A)) := DecEq.mk(List(A), Bool.true)

def useListEq [eqA: DecEq(List(Nat))]: DecEq(List(Nat)) := eqA

{
  useListEq(derive[DecEq(List(Nat))])
}
```

### Namespaces and Opens

Namespaces prefix declarations with dotted canonical names. Inductive constructors live under the inductive head, so
`Nat.zero` and `Data.Tree.leaf` are ordinary global names. `open` brings existing children of a namespace into the
current scope as a snapshot.

```raccoon
import Lib.Foo.Bar // import Lib/Foo/Bar.rac, making its definitions available

namespace Data {
  inductive Tree : Type
   | leaf : Tree
   | node (left: Tree)(right: Tree) : Tree
}

open Data.{Tree as DTree}

def example : Data.Tree :=
  DTree.node(DTree.leaf, DTree.leaf)
```

Dotted names resolve local-first: if the first segment is a local, the rest of the path is projection. Use `_root_` to
bypass locals, the current namespace, and opens. Opens support wildcard, selected, excluded, renamed, and root-qualified
forms such as `open Nat`, `open Nat.{zero, succ}`, `open Nat.{*, -succ, succ as nsucc}`, and `open _root_.Nat`.

Match case heads use normal global resolution. Prefix a case head with `.` to match by the constructor short name from
the scrutinee type: `| .zero => ...`.

See [docs/namespaces.md](docs/namespaces.md) for the exact resolution and open rules.

### Equality by computation with a normalizer

A normalizer rewrites a blocked expression into a different (equivalent) form. For example, the 'add_normalizer'
flattens all additions to a list, removes zeros and then sorts the list. Currently, for demonstration purposes, it
can be used without providing the relevant proofs, but in a full implementation it would require proofs of standard
monoid laws.

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

stable def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
  match b with
  | Nat.zero => a
  | Nat.succ x => add(Nat.succ(a), x)
}

def nat_add_normalizer : Normalizer := add_normalizer(Nat, Nat.zero, add)

def addComm (a: Nat)(b: Nat): Eq(Nat, add(a, b), add(b, a)) := {
  use nat_add_normalizer
  Eq.refl(add(a, b))
}
```

## Quickstart

To just try out the language, download the latest release (arm mac only at the moment), then run in your shell

```bash
raccoon /path/to/program.rac
```

Prebuilt macOS binaries are currently distributed unsigned, so macOS may warn on first launch.

To allow the binary:

1. Run it once from Terminal.
2. Open **System Settings → Privacy & Security**.
3. Click **Open Anyway** for the blocked binary.
4. Re-run the command.

## Developing / building from source

### Requirements

- Java 17+
- sbt 1.8+
- Xcode Command Line Tools for GraalVM native-image on macOS (`clang`, `libc++`)

### Run tests

```bash
sbt test
```

### Run a program on the JVM

```bash
sbt "run path/to/program.rac"
```

The CLI reads a `.rac` file, loads its imports, elaborates it, typechecks it, evaluates it, and pretty-prints the
resulting value when the program body produces one.

`Init/Prelude.rac` is bundled and loaded automatically before user code. An explicit `import Init.Prelude` is accepted
as a no-op for compatibility with source files that name their prelude dependency.

Prelude declarations can use `:= builtin` when their canonical name has a native implementation in the runtime builtin
registry.

```bash
sbt 'run --root examples examples/nats.rac'
```

`--root <dir>` can be repeated. `import Lib.Nat` searches source roots for `Lib/Nat.rac`. When no root is specified,
the entry file's directory is used.

### Build the native binary

```bash
./scripts/build-graal-native.sh
./target/graalvm/raccoon ./examples/nats.rac
```

The script builds the JVM classes with sbt, writes the runtime classpath to `target/graalvm/classpath.txt`, and then
runs GraalVM `native-image`.

## Next Planned Features

- Mutually-recursive inductives
- Full Prelude quotient API surface
