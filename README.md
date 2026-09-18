# Raccoon

Raccoon is a small dependently typed language for verified programming and
AI-assisted proof generation. It has a compact surface language, a trusted
typechecker and evaluator, and a bundled source prelude.

The implementation favors:

- fast, predictable checking;
- explicit language rules over heuristic elaboration;
- a small semantic core;
- correctness and internal consistency over compatibility.

## Language at a glance

Raccoon currently provides:

- dependent functions with forced implicit parameters;
- first-class universe levels, `Prop`, `Type`, and `Sort(u)`;
- strictly positive inductive families with parameters and indices;
- dependent, exhaustive pattern matching;
- structural, lexicographic, and measure-based termination checking;
- single-constructor `struct` declarations, named projections, and structure eta;
- proof irrelevance and controlled elimination from `Prop`;
- namespaces, scoped `open`, and file imports;
- opaque definitions, axioms, and quotients;
- compact natural-number literals and trusted native natural-number reduction.

```raccoon
inductive Vec {u: Level}(A: Sort(u)) indices (n: Nat)
    : Sort(Level.max(Level.one, u))
 | nil : Vec(A, Nat.zero)
 | cons (n: Nat)(tail: Vec(A, n))(head: A) : Vec(A, Nat.succ(n))

def length {u: Level}{A: Sort(u)}{n: Nat}(xs: Vec(A, n)): Nat := n

def appendOne {u: Level}{A: Sort(u)}{n: Nat}(xs: Vec(A, n))(x: A)
    : Vec(A, Nat.succ(n)) := Vec.cons(n, xs, x)

{ length(appendOne(Vec.nil(Nat), 0)) }
```

Function binder groups have exact arity. For example, `A -> B -> C` is one
two-argument function type and is called as `f(a, b)`. Write
`A -> (B -> C)` for a function that returns a function and call it as
`f(a)(b)`.

See [the language reference](docs/language.md) for source syntax and semantics,
and [the kernel reference](docs/kernel.md) for the trusted rules behind
conversion, proofs, inductives, and native values.

## Run a program

The CLI accepts one entry file:

```bash
sbt "run examples/nats.rac"
```

The bundled `Init/Prelude.rac` is loaded automatically. A program may end in an
expression; if it does, the CLI evaluates and prints the result.

Imports are resolved from the entry file's directory by default. Add source
roots with repeatable `--root` options:

```bash
sbt 'run --root examples examples/nats.rac'
```

Other CLI options are:

```text
--prelude <file>   use a custom trusted prelude
--no-prelude       run without a source prelude
--wait-for-enter   pause after JVM startup
```

Choosing a custom prelude changes the trusted bootstrap. See the
[kernel reference](docs/kernel.md#trusted-bootstrap-and-native-values).

## Build and test

Requirements:

- Java 17 or newer;
- sbt 1.8 or newer;
- GraalVM `native-image` and a C++ toolchain for a native executable.

Run formatting checks and the complete test suite:

```bash
sbt validate
```

Build and run the native executable:

```bash
./scripts/build-graal-native.sh
./target/graalvm/raccoon examples/nats.rac
```

The native build includes the bundled prelude and writes its intermediate
classpath under `target/graalvm`.

## Repository guide

- `src/main/scala/com/raccoonlang`: parser, elaborator, checker, and evaluator;
- `src/main/resources/Init/Prelude.rac`: bundled source prelude;
- `src/test/scala/com/raccoonlang`: semantic and regression tests;
- `examples`: runnable Raccoon programs;
- `docs/language.md`: current source-language reference;
- `docs/kernel.md`: current trusted semantic reference;
- `STYLE.md`: project engineering conventions.
