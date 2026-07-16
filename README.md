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
    - Explicit implicit-parameter insertion in checked terms

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

- Inductive families with explicit params, indices, and erased family witnesses
    - Validates positivity, universes, constructor result shape, and uniform params
- Termination checking of recursive functions
- Dependent pattern matching
    - Branch refinement for indexed families / dependent pattern matching. Supports equality proofs.
    - Validates exhaustiveness checking: missing, duplicate, and unreachable branches
- Cumulative universes, first-class `Level`, `Sort(u)`, universe validation, and sort unification
    - `Prop` is `Sort(Level.zero)`; `Type` is `Sort(Level.one)`
    - Impredicative Prop with proof irrelevance and controlled large elimination
- Namespaces, file imports, dotted names, and scoped `open`
- Implicit parameters
- Type classes with `def instance`, `let instance`, `[f: Foo]` instance binders, and explicit `derive[Foo]`
  search
- Structs / Projections
- Quotients
- JVM CLI plus Scala Native build

## A few concrete examples

### Inductives and Pattern Matching

Inductives can split family arguments into uniform params and non-uniform indices with `indices`, and their result
can live in an explicit universe. Family params are supplied to constructors as implicit erased witnesses, while
ordinary constructor binders, including `{...}` binders, are stored as fields. Indices are supplied by ordinary fields or
fixed result expressions. This includes universe-polymorphic inductives whose fields and result type are parameterized
by a `Level`.

Pattern matches are checked for exhaustiveness. Required constructors must be present, duplicate cases are rejected,
and constructors that are impossible at the scrutinee's family type can be omitted.

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

inductive Box (u: Level)(A: Sort(u)) : Sort(u)
 | mk (value: A) : Box(u, A)

inductive Vec (u: Level)(A: Sort(u)) indices (n: Nat) : Sort(Level.max(Level.one, u))
 | nil : Vec(u, A, Nat.zero)
 | cons (n: Nat)(xs: Vec(u, A, n))(x: A) : Vec(u, A, Nat.succ(n))

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

def add (a: Nat)(b: Nat): Nat decreases structural(b) := {
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

### Implicit parameters

Binders written with `{...}` are implicit. Calls may omit them when the type checker can infer the value from the
surrounding application, while definitions can still refer to the bound names like ordinary parameters.
Implicit binders must form a prefix of their telescope: after an explicit or instance binder appears, later binders
must also be explicit or instance binders.

```raccoon
inductive Nat : Type
  | zero : Nat
  | succ (_: Nat) : Nat

inductive Vec {u: Level}(A: Sort(u)) indices (n: Nat) : Sort(Level.max(Level.one, u))
  | nil : Vec(A, Nat.zero)
  | cons (n: Nat)(v: Vec(A, n))(elem: A): Vec(A, Nat.succ(n))

inductive Pair {u1: Level}{u2: Level}(A: Sort(u1))(B: Sort(u2)): Sort(Level.max(u1, u2))
  | mk (a: A)(b: B): Pair(A, B)

def zip {A: Type}{B: Type}{n: Nat} (va: Vec(A, n))(vb: Vec(B, n)): Vec(Pair(A, B), n) decreases measure(n) := {
  let ResType := Vec(Pair(A, B), n)
  match va returning ResType with
  | Vec.nil => Vec.nil(Pair(A, B))
  | Vec.cons n0 va0 a => {
    match vb returning ResType with
    | Vec.cons _ vb0 b => Vec.cons(Pair(A, B), n0, zip(va0, vb0), Pair.mk(a, b))
  }
}
```

### Structs and Projections

A `struct` declaration is frontend sugar for an inductive family with one constructor plus ordinary named selector
definitions in the family's namespace. The checked inductive declaration carries no struct flag; internally,
projections are identified positionally by the family and constructor-field index.

Rules and consequences:

- `struct` syntax accepts exactly one constructor and generates a selector for each named field. Anonymous `_` fields
  remain positional fields but receive no selector alias.
- Params before `indices` must be returned uniformly by every constructor.
- Indices may be fixed by the constructor result or recovered from stored fields.
- May live in `Type`/`Sort(u)` or `Prop`; a projection from a `Prop` instance recovers only fields whose value and type
  dependencies are determined by the exact proposition, without inspecting the proof value.
- Any checked inductive family—not only one written with `struct`—gets definitional structure eta when it has exactly
  one constructor, zero indices, and no recursive constructor field. Indexed and recursive singleton families may
  still be projected, but do not get eta.

Projection syntax `p.field` uses the generated selector metadata to elaborate directly to a positional projection;
`Family.field(p)` remains an ordinary explicit call to the generated selector definition. Plain `inductive`
declarations do not generate these aliases, even when they qualify for eta.

Example: simple non-dependent projections

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

struct Pair (A: Type)(B: Type) : Type
 | mk (fst: A)(snd: B) : Pair(A, B)

def first {A: Type}{B: Type} (p: Pair(A, B)): A := p.fst
def second {A: Type}{B: Type} (p: Pair(A, B)): B := p.snd
```

### Type Classes

An instance is an ordinary definition or local binding marked as an instance, and instance search runs only where a term
expression explicitly asks for it with `derive[Goal]`.

Bracket binders such as `[x: T]` are instance-marked binders. They are still ordinary positional arguments at call
sites, but the bound value is registered for local instance search while checking the binder's scope. This lets instance
functions declare searchable dependencies with implicit parameters, and lets function bodies call `derive[...]`
against instance-marked parameters.

Search uses lexical priority and stops at the first successful candidate in a tier. Local instance bindings are
searched before globals, with newer local bindings tried first. If a local candidate succeeds, globals are not
considered. Globals are searched only when no local candidate succeeds. This means a local instance can intentionally
override a global one without creating ambiguity, and overlapping instances are resolved by search order rather than by
ambiguity detection.

```raccoon
struct DecEq (A: Type) : Type
 | mk (result: Bool) : DecEq(A)

inductive List (A: Type) : Type
 | nil : List(A)

def instance natEq : DecEq(Nat) := DecEq.mk(Nat, Bool.true)

def instance listEq {A: Type} [ea: DecEq(A)]: DecEq(List(A)) := DecEq.mk(List(A), Bool.true)

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
