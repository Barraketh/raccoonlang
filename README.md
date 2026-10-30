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

Results on an Apple M1 Max, October 26, 2026; process
wall-clock times, including startup:

| nested zips | Raccoon JVM | Raccoon native | Lean 4.37 nightly |
|------------:|------------:|---------------:|------------------:|
|         800 |      0.449s |         0.033s |            2.692s |
|       1,600 |      0.544s |         0.051s |            8.662s |
|       3,200 |      0.679s |         0.086s |           33.350s |
|       6,400 |      0.921s |         0.159s | fails after 138s  |
|      51,200 |      2.273s |         1.266s |               N/A |

Lean runs with raised `maxRecDepth` and disabled heartbeats; with default limits
it fails at 800 nested zips.

Note that at this point I have done 0 optimization - these performance wins are strictly algorithmic.

## Implemented today

- Inductive families with explicit params, indices, and erased constructor binders
    - Validates positivity, universes, constructor result shape, and uniform params
    - [Nominal Type-family rules](docs/kernel.md#nominal-type-families) with argument size checks
- Lambdas in types, such as the predicate in `List.Every(xs, fun (x: Nat): Prop => True)`, with no partial
  application (see [lambdas in types](docs/kernel.md#lambdas-in-types))
- Termination checking of recursive functions
- Dependent pattern matching
    - Branch refinement for indexed families / dependent pattern matching. Supports equality proofs.
    - Validates exhaustiveness checking: missing, duplicate, and unreachable branches
- Non-cumulative universes, first-class `Level`, `Sort(u)`, universe validation, and sort unification: a type is used
  at exactly its universe, and universe-polymorphic signatures (`Sort($u)`) take every level
    - `Type` is `Sort(Level.zero)`; `Prop : Type` is separate from the `Sort(u)` hierarchy
    - Impredicative Prop with proof irrelevance and controlled large elimination
    - Universe polymorphism ranges over Type levels only; propositions cannot be carriers for `Eq`, `DecidableEq`, or `Subsingleton`
- [Linear types](docs/kernel.md#linear-types): kinds, with universes `Univ(k, u)` of copyable, linear and
  kind-polymorphic types (`Sort(u)` and `Lin(u)` name the constant kinds), and families whose values are used at most
  once on every path when their kind is not copy
    - Copyable functions over linear values, with no linear captures; types and proofs may read linear values without
      consuming them, keeping each call's linear inputs separate; no linear globals or axioms
- [Resource protocols](docs/kernel.md#resource-protocols): first-class protocols, linear tokens changed only by
  `Protocol.step`, and `Protocol.observe`, which proves that tokens held together are part of one reachable
  configuration; an untrusted protocol library in [`lib/Protocol`](#the-protocol-library)
- Extensible definitional equality through type-driven expression normalization
- Canonical sums of products for builtin Nat addition, multiplication, and powers, deciding associativity,
  commutativity, units, numeral arithmetic, and the exponent product law `x^a * x^b = x^(a + b)` by conversion, plus
  native truncated subtraction and comparisons
    - Distributivity is the prelude axiom `Nat.mul_add`; `(x * y)^a` and `(x^a)^b` are the prelude theorems
      `Nat.mul_pow` and `Nat.pow_mul`
    - Decimal literals such as `0` and `42` denote kernel Nat values of any size, in terms and types
    - See [the Nat normal forms design](docs/nat-normal-forms.md) for the laws, representation, and kernel integration
- Kernel `List` with packed storage and a native `append` that follows the source definition with the right unit
  `append(l, nil) = l` definitional; native `length` maps lists to Nat sums, so the length law
  `length(append(l, r)) = length(l) + length(r)` holds by conversion
    - Associativity is the prelude theorem `List.append_assoc`; it computes whenever the first list ends in `nil`
    - The prelude also has membership (`List.Mem`), the laws of the kernel's `List.Perm`, `List.flatMap` with its laws,
      `Nat.max` and the order laws of `Nat.le` and `Nat.lt`
    - See [kernel lists](docs/packed_lists.md#kernel-list)
- Kernel `Char` and `String` with string literals `"…"`: JSON-style escapes (`\"`, `\\`, `\/`, `\b`, `\f`, `\n`,
  `\r`, `\t`, `\uXXXX`, with surrogate pairs for scalars beyond U+FFFF) denoting Unicode scalar values; the prelude's
  `String.append` and `String.length` call the List natives (see [kernel strings](docs/packed_lists.md#kernel-strings))
- Namespaces, file imports, dotted names, and scoped `open`
- Type patterns
- Type classes with `def instance`, `let instance`, `[f: Foo]` instance binders, and explicit `derive[Foo]`
  search
- Structs / Projections
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
and each recursive call must pass a strict constructor subterm in that position. A `measure` annotation checks that an
evaluated inductive-valued measure gets structurally smaller. A `lexicographic` annotation checks a sequence of
components, each a parameter or a measure written `measure(e)`: an earlier component may decrease, or an equal prefix
can be followed by a later decrease. A `Nat` component, a parameter or a measure, is ordered by `<` instead, decided on
its normal form: `b` is below `a + b + 1` but not below `a + b`, and a prefix component may be at most the current one
rather than equal. In a `mutual` block, a constant measure is a rank: when `f` decreases `lexicographic(h, measure(0))`
and `g` decreases `lexicographic(h, measure(1))`, `g` may call `f` with `h` unchanged.

Decrease metrics must be inductive values. A function whose result is a proposition may also decrease a proof, as a
`structural` metric or a `lexicographic` parameter; other functions' metrics must live in `Type`/`Sort(u)`, and measures
always must. A proof metric decreases only by passing one of the matched proof's proof fields, or a proof field of
those, unchanged: proofs are compared by identity, since proof irrelevance makes any two proofs of a proposition
convertible. Subterm search for data metrics does not traverse proof fields. See
[recursion on proofs](docs/kernel.md#recursion-on-proofs).

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

The `decreases` clause continues the definition's header, so it may start the line after the result type, and its
specification the line after `decreases`.

### Syntax and layout

Line breaks separate imports, declarations, the members of a `mutual` block, a block's statements, a match's cases and
an inductive's constructors. Any number of blank and comment-only lines may stand in place of one, including right after
a block's `{`. A case or a
constructor ends its line, so a match's cases never share a line with its header or with each other, and a match's
`returning` clause may start the line after its scrutinee.

`A -> B` is the non-dependent function type wherever a type or a term may stand: as a binder type, a codomain or an
argument, as in `List.nil(Nat -> Nat)`. A binder type may be any type, such as an application followed by an arrow,
`(f: List(Nat) -> Nat)`, an application of an application, `(h: R(x)(y, z))`, or an application headed by a
projection, `(h: P.Step(A, B))`; a pattern with captures, such as `List($A)`, applies a name once. A lambda binds at
least one parameter. `use` is an identifier except at the start of a block's statement, where it begins a `use`
statement.

```raccoon
def apply (f: List(Nat) -> Nat)(xs: List(Nat)) : Nat := f(xs)

def count (n: Nat): Nat
    decreases structural(n) := {
  // a comment right after the brace

  match n returning Nat with
  | Nat.zero => 0
  // a comment between cases
  | Nat.succ k => Nat.succ(count(k))
}
```

### Type patterns

An alternative to implicit parameters. A binder can contain captures in the type, and later parameters can reference
these captures. See example below. You declare a capture with a '$'[name] . When applying a function,
these patterns bind the incoming type like regular pattern matches in a language like Lean. A failure to match will
result in a typecheck failure. A pattern's head may be a function, such as an alias of a family; its captures read the
incoming type by position and are then checked as the head's arguments. This feature allows us to greatly reduce the number of function params - zip would
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

### Records and Projections

A record is an inductive family with exactly one constructor. Each of its named fields has a selector, and
`p.field` selects that field from a value `p` of the family. Projections from `Prop` records obey Prop elimination
restrictions, and a record whose field type names a capture that is no family parameter has no selectors. A record
without indices or recursive fields, outside `Prop`, also has structure eta: a value converts with its constructor
applied to its projections, and a match on a neutral value computes (see
[structure eta](docs/kernel.md#structure-eta-and-projections)).

Example: simple non-dependent projections

```raccoon
inductive Nat : Type
 | zero : Nat
 | succ (_: Nat) : Nat

inductive Pair (A: Type)(B: Type) : Type
 | mk {A: Type}{B: Type} (fst: A)(snd: B) : Pair(A, B)

def first (p: Pair($A, $B)): A := p.fst
def second (p: Pair($A, $B)): B := p.snd
```

Let bindings can unpack the stored fields of an inductive family with exactly one declared constructor:

```raccoon
def firstByUnpacking (p: Pair($A, $B)): A := {
  let (first, _) := p
  first
}
```

Patterns may nest, use `_` to discard a field, and must list exactly the stored constructor fields in order.
Erased arguments and type-pattern captures are not fields. `()` unpacks a constructor with no stored fields;
`(value)` unpacks one field. An optional type annotation applies to the whole right-hand side. The right-hand side
uses the original scope and is evaluated once; pattern names may shadow outer names, but repeated names in one
pattern are rejected. The bindings and any match refinements are in scope for the rest of the block.

Unpacking follows ordinary match rules, including for indexed, recursive, and Prop families. Prop elimination
restrictions still apply, and a branch-local type cannot escape into an invalid outer result type. Match result types
come from an explicit `returning` clause, otherwise a surrounding expected type, otherwise inference from the branch
bodies. Dependent results may require an annotation. `let instance` requires a single name, and unpacked fields do
not become instances automatically.

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
inductive DecEq (A: Type) : Type
 | mk {A: Type} (result: Bool) : DecEq(A)

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
forms such as `open Nat`, `open Nat.{zero, succ}`, `open Nat.{*, -succ, succ as nsucc}`, and `open _root_.Nat`. A name
an `open` selects explicitly, such as `zero` in `open Nat.{zero}`, wins over a member of the enclosing namespace with
that name; a wildcard open's names do not.

A declaration's name may be dotted: `def Data.Tree.size (t: Data.Tree) : Nat := ...` declares `size` in the namespace
`Data.Tree`, exactly as a `namespace Data.Tree { ... }` block around it would. A `mutual` block's members share one
scope, so their names are not dotted: a block that declares into a namespace stands in a namespace block.

Match case heads use normal global resolution. Prefix a case head with `.` to match by the constructor short name from
the scrutinee type: `| .zero => ...`.

See [docs/namespaces.md](docs/namespaces.md) for the exact resolution and open rules.

### Linear types

A universe `Univ(k, u)` has a kind `k`: `Kind.copy`, `Kind.lin`, a kind variable, or a `Kind.join` of them, and `Sort(u)`
and `Lin(u)` name the constant kinds. A type of linear or variable kind is linear: each of its values is used at most
once on every path through the scope that binds it, so a match consumes its scrutinee, and a value or field may be
dropped. Families may be kind-polymorphic, as the kernel's `List (A: Univ($k, $u)) : Univ(k, u)` and the prelude's
`Prod`, `Option` and `Sum` are, so `List(Nat)` is copyable and a list of tokens is linear. Kind-polymorphic code treats
its values as linear, and a capture such as `List($A in Sort($u))` asks for copyable elements. Functions are always
copyable and cannot capture linear locals. Types and proofs may read linear values without consuming them, as long as no
one call inside them receives the same value twice. See [linear types](docs/kernel.md#linear-types). The prelude's
`Fact(p)` carries a proof beside tokens in a `Prod`, and `Eq.subst` transports a value of any kind along an equation.

```raccoon
def map (xs: List($A))(B: Univ($k, $v))(f: A -> B) : List(B) decreases structural(xs) := {
  match xs with
  | List.nil => List.nil(B)
  | List.cons h t => List.cons(f(h), map(t, B, f))
}

def count (xs: List($A)) : Nat decreases structural(xs) := {
  match xs with
  | List.nil => 0
  | List.cons h t => Nat.succ(count(t))
}
```

At a linear `xs`, `count(xs)` after `count(xs)` is `LinearReused`, while a branch may drop `xs`. A type may read `xs`:
`Eq(Nat, count(xs), count(xs))` reads it twice, in two separate calls, and consumes nothing, but
`count(append(xs, xs))` in a type is `LinearReusedInType`.

### The protocol library

`lib/Protocol` is untrusted library code over the kernel's protocol declarations, loaded with `--root lib`
(`import Protocol.Laws`):

- `Laws`: derivations (`Protocol.Derives`) and their laws, `Reach.iff_derives`, `Reach.frame` and the `Valid` laws,
  all over a protocol `P: Protocol.Proto`, as the kernel families take one;
- `Morphism`: protocol morphisms with `transport`, `pullback` and `comp`;
- `Packets`: `append`, `split`, `exchange`, `swap`, a framed step, and token-first `inspect`, which observes a packet
  and returns it with a fact;
- the building blocks `Exclusive` and `Shares`;
- support: `Lists` (`Subset`, `Every`, `Pairwise`, `Nodup`) and `Logic`. Membership (`List.Mem`), the `List.Perm`
  laws, `List.flatMap`, `Nat.max`, the `Nat.le`/`Nat.lt` order laws and `False.elimProp` are in the prelude; `Nats`
  remains, empty, for its importers.

Protocol theorems hold only without user axioms, so run them with `--no-user-axioms`. See
[resource protocols](docs/kernel.md#the-protocol-library).

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
registry. A builtin's declared type is trusted, not checked, so a program, or a module it imports, cannot declare one
(`ProgramBuiltin`). `Kind`, `Univ`, `Sort`, `Lin`, `Bool`, `Nat`, the kind-polymorphic `List`, `Char`, `String`, their constructors and selectors, the native Nat arithmetic,
subtraction, and comparisons, and the native `List.append` and `List.length` are built into the kernel: every
environment has them, including with `--no-prelude`, and they cannot be redeclared. So are the resource-protocol
families `List.Perm`, `Protocol.Proto`, `Protocol.Reach` and `Protocol.Valid`, the opaque `Protocol.Supply`,
`Protocol.Inst` and `Protocol.Tok`, which have no constructors, the linear `Protocol.Toks`, `Protocol.Observed` and
`Protocol.Fresh`, and the primitives `Protocol.new`, `Protocol.step` and `Protocol.observe` (see
[resource protocols](docs/kernel.md#resource-protocols)). A program body of type `(sup: Protocol.Supply) -> R`, for an
unrestricted `R`, is an entry: once it has checked, `Interpreter.run` applies it to the root supply, and the CLI prints
the result.

```bash
sbt 'run --root examples examples/nats.rac'
```

`--root <dir>` can be repeated. `import Lib.Nat` searches source roots for `Lib/Nat.rac`. When no root is specified,
the entry file's directory is used.

Axioms declared by the program or its imports are unchecked assumptions. The CLI lists them on standard error, and
`--no-user-axioms` rejects them instead, at the first one's declaration. The prelude's axioms are the trusted bootstrap
and are always allowed; a custom `--prelude`'s axioms are listed on standard error in both modes. See
[axioms](docs/kernel.md#axioms).

### Build the native binary

```bash
./scripts/build-graal-native.sh
./target/graalvm/raccoon ./examples/nats.rac
```

The script builds the JVM classes with sbt, writes the runtime classpath to `target/graalvm/classpath.txt`, and then
runs GraalVM `native-image`.

## Next Planned Features

- Mutually-recursive inductives
