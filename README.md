# Raccoon Lang

Raccoon is a small dependently typed language and implementation aimed to be a target for AI-assisted proof generation,
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

## Implemented today

- Inductive families with parameters and indices
    - Validates positivity, universes, uniform parameters, constructor result shape
- Dependent pattern matching
    - Branch refinement for indexed families / dependent pattern matching.  Supports equality proofs.
    - Validates exhaustiveness checking: missing, duplicate, and unreachable branches
- Cumulative universes, first-class `Level`, `Sort u`, universe validation, and sort unification
  - Impredicative Prop with controlled large elimination
- Extensible definitional equality through type-driven expression normalization
- Type patterns
- JVM CLI plus Scala Native build for macOS

## A few concrete examples

### Simple inductive types and functions

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

inline def pred (n: Nat): Nat := {
  match n as _ returning Nat with
  | Nat.zero => Nat.zero
  | Nat.succ x => x
}

{ pred (Nat.succ Nat.zero) }
```

### Universe-polymorphic identity

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

inline def idAt (u: Level)(A: Sort u)(x: A): A := x

{ idAt Level.zero Nat Nat.zero }
```

### Indexed vectors

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

inductive Vec (A: Type) indices (n: Nat) : Sort Level.one
 | nil : Vec A Nat.zero
 | cons (n: Nat) (xs: Vec A n) (x: A) : Vec A (Nat.succ n)
```

### Equality by computation with a normalizer

A normalizer rewrites a blocked expression into a different (equivalent) form.  For example, the 'add_normalizer'
flattens all additions to a list, removes zeros and then sorts the list.  Currently, for demonstration purposes, it
can be used without providing the relevant proofs, but in a full implementation it would require proofs of standard
monoid laws.

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

stable def add (a: Nat)(b: Nat): Nat := {
  match b as _ returning Nat with
  | Nat.zero => a
  | Nat.succ x => add (Nat.succ a) x
}

inline def nat_add_normalizer : Normalizer := add_normalizer Nat Nat.zero add

inductive Eq (A: Type) indices (x: A) (y: A) : Sort Level.one
 | refl (x: A) : Eq A x x

inline def addComm (a: Nat)(b: Nat): Eq Nat (add a b) (add b a) := {
  use nat_add_normalizer
  Eq.refl Nat (add a b)
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

inductive Vec (A: Sort $u) indices (n: Nat) : Sort u
  | nil: Vec A Nat.zero
  | cons (v: Vec A $n)(elem: A): Vec A (Nat.succ n)

inductive Pair (A: Sort $u1)(B: Sort $u2): Sort (Level.max u1 u2)
  | mk(a: A)(b: B): Pair A B

inline def zip(va: Vec $A $n)(vb: Vec $B n): Vec (Pair A B) n := {
  let ResType := Vec (Pair A B) n
  match va as _ returning ResType with
  | Vec.nil => Vec.nil (Pair A B)
  | Vec.cons va0 a => {
    match vb as _ returning ResType with
    | Vec.cons vb0 b => Vec.cons (Pair A B) (zip va0 vb0) (Pair.mk A B a b)
  }
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
- macOS only for the Scala Native build
- Xcode Command Line Tools for Scala Native (`clang`, `libc++`)

### Run tests

```bash
sbt test
```

### Run a program on the JVM

```bash
sbt "run path/to/program.rac"
```

The CLI reads a single `.rac` file, elaborates it, typechecks it, evaluates it, and pretty-prints the resulting value when the program body produces one.

### Build the native binary

```bash
sbt native/nativeLink
./native/target/scala-2.13/raccoon ./examples/nats.rac
```

## Repository map

- `src/main/scala/com/raccoonlang/Main.scala` — CLI entrypoint
- `src/main/scala/com/raccoonlang/SurfaceAst.scala` — parsed surface language
- `src/main/scala/com/raccoonlang/Elaborator.scala` — surface-to-core elaboration
- `src/main/scala/com/raccoonlang/CoreAst.scala` — core syntax
- `src/main/scala/com/raccoonlang/TypeChecker.scala` — typing, definitional equality, and match checking
- `src/main/scala/com/raccoonlang/Interpreter.scala` — evaluation
- `src/main/scala/com/raccoonlang/InductiveChecks.scala` — inductive-family validation
- `src/test/scala/com/raccoonlang` — semantic tests


## Limitations

Planned / not yet implemented:
- Strict positivity checking in inductive declarations is overly conservative
- Mutually-recursive inductives
- Quotients
- File imports
- No standard library
- No performance benchmarks
