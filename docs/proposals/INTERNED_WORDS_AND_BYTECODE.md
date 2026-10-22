# Interned values, word values and a bytecode evaluator

> **Historical proposal details.** The bytecode sketch includes `SCOPE` and
> `Scoped`, which represented Raccoon's removed `Lifetime`/scope feature.
> Those nodes are not part of the current language or compiler. See the
> [language reference](../language.md) and [kernel reference](../kernel.md).
> The original source is available from baseline `81759785` with
> `git show 81759785:docs/proposals/INTERNED_WORDS_AND_BYTECODE.md`.

Status: proposal, 2026-10-05. Not implemented.

Scope: make type checking, and the evaluation it performs, as fast as possible
within one run. Out of scope:

- caching checked modules across runs, which is a separate proposal;
- a runtime for closed programs, which may later compile through LLVM;
- removing eagerly computed value types, which is
  [TYPE_PROGRAMS.md](TYPE_PROGRAMS.md). Part 3 builds the code structure that
  proposal needs.

## Purpose

An allocation census of CUDA generation in `../lemur-raccoon` (2026-10-05,
`gpu/gen.sh gpu/encoding/examples/attention_pingpong.rac` on the JVM; the
output was byte-identical to the recorded benchmark) found:

- 4.27M constructor and type applications per run: about 470 MB, estimated from
  measured object sizes, in about 9 s;
- a live heap of only about 33.5 MB at its peak, of which values are about 4 MB.

So the cost is churn, not resident memory. Every application builds a `VApp`
(48 bytes), a `Key` (32 bytes), an argument `Vector` (16 bytes) and its array.
It also does work when built: `require` checks, determining arguments, a
`DepSet` union over its children, and an eager 128-bit key mix.

The corpus is small and does not represent the workloads this design targets,
such as a large proof library or general programs. The census is a measuring
instrument for each step, not the rationale for any of them. Allocations by
class on that corpus (`attention_a3b` agrees to within half a point):

| Class | Share | Largest contributors |
|---|---|---|
| nullary constructors | 29.8% | `Bool.false`/`true` 512k, `DType.f32` 114k, `Option.none` 96k |
| string machinery | 20.0% | `String.mk` 543k, `Char.mk` 164k, `List(Char)` cells 147k |
| `List` cells | 16.0% | `List(Bool)` 311k, `List(Stmt)` 257k |
| tree nodes | 11.3% | `Cuda.Expr.*`, `Check.NatSet.node` |
| type values | 8.3% | `List(A)`, `Core.Val(…)`, `Core.Ctx(…)` as the types of values |
| records | 7.4% | `Core.Gen.mk` (7 fields), `Core.Val.mk` |
| sums | 6.5% | `Check.Leaf.*`, `Cuda.Stmt.*` |

The run loop adds its own overhead:

- Every reference to a nullary constructor (`CoreEvaluator.nullaryConstructor`)
  builds a fresh value through `Packed.construct`.
- A `match` selects its branch through `ConstructorForm.Stored`, which
  allocates a `Some` and a tuple, and then looks the constructor's *name* up in
  a `Map[String, Branch]`.
- A Nat held unboxed in a frame slot is boxed into a `VPacked` to be matched,
  and its predecessor is decoded as another `VPacked`.
- Plans are trees of case-class nodes. Each step is a pattern match on a node,
  plus a push and pop of a `(kind, node, index)` continuation.

This proposal removes that work in three independent steps:

1. **Interning** (Part 1): one shared value per nullary constructor and per
   closed type value.
2. **Word values** (Part 2): a closed value whose fields fit in 64 bits is a
   word, not a tree of objects.
3. **A bytecode evaluator with typed slots** (Part 3): linear code instead of
   plan trees, and words and Nats held unboxed in frame slots.

Principle: **representation is invisible.** No value, no definitional
equality, no key and no output changes. Each step ships on its own, with
byte-identical outputs.

## Terms

- **Closed value**: a value with no dependencies and no blockers.
- **Intern table**: a process-wide map from a closed value's identity to its one
  shared instance.
- **Layout**: for one closed instance of a family, how each constructor's
  stored fields pack into 64 bits.
- **Word value**: a closed constructor application stored as `(layout, bits)`.
- **Heap node**: today's `VApp` representation of a constructor application.
- **Boxing**: turning an unboxed slot (a Nat or a word) into a `Value` object.
- **Typed slot**: a frame slot that holds a reference, an unboxed Nat or an
  unboxed word.

## Part 1. Interning

### Nullary constructors

A `ConstructorHead` of total arity 0 whose type is closed keeps its canonical
value. The value is built once, on first use, through `Packed.construct`.
`nullaryConstructor` and every other path that builds such a value return it.

A nullary constructor of a family with parameters, such as `List.nil(A)` or
`Option.none(A)`, has total arity at least 1. It is built through ordinary
application, and is interned by the closed-value table below when its type is
closed.

### Closed type values

A family application whose arguments are all closed, such as
`List(Cuda.Stmt)` or `Core.Val(…)`, is interned.

- The table is keyed by the head's identity and the arguments' keys, and is
  consulted *before* the type is built: before evaluating the codomain and
  before binding its environment. A hit costs one key mix and one probe.
- It sits behind the existing four-entry per-`VPi` `constructorResults` cache,
  which stays as a first level.
- Construction sites: the `VConst` head case of `CoreEvaluator.applyFunction`,
  `VPi.dependentConstructorResult`, and their `Interpreter` counterparts.

### The tables

- They are process-wide and safe for concurrent use. The kernel already uses
  thread-local runtimes and synchronized caches.
- Their size is bounded by the program's distinct closed types and nullary
  constructors, so v1 holds entries strongly.
- A hit is confirmed by head identity and argument keys. That trusts 128-bit
  keys exactly as conversion's key fast path already does, and no further.

Interning is justified because it is cheap and Part 2 needs interned
instances. On the 2026-10-05 corpus, these classes are about 38% of application
allocations. Interning never changes a key, and conversion already treats `eq`
as equality.

## Part 2. Word values

### Layouts

A layout is computed on first construction for each closed family instance:
the family head together with its interned closed arguments. It is computed
from constructor metadata, using stored fields only, after the family arguments
are erased.

A constructor is **word-eligible** when it has no evidence fields (v1) and
every stored field's type is one of:

- a closed instance of an all-nullary family, taking `⌈log₂ #constructors⌉`
  bits;
- a closed instance of another family whose word-eligible constructors have
  bounded width, with no recursion through itself;
- Nat. At most one Nat field per constructor; it takes the remaining bits.

The word is the constructor tag (`⌈log₂ #constructors⌉` bits over *all* the
family's constructors, or 0 for one constructor), then the fixed-width fields,
then the optional Nat field. The total is at most 64 bits.

Eligibility is per constructor, and fitting is per value:

- In `Cuda.Expr`, `var`, `lit` and `zero` are word-eligible, while `bin` and
  `select` stay heap nodes.
- `Expr.var(5)` is a word. `Expr.var(2⁷⁰)` does not fit, so it is a heap node.
- `Char.mk(n)` is a word through its one Nat field, so `Char` needs no special
  case.

The choice is deterministic, so every value has exactly one representation.

### The value

`final class VWord(layout: WordLayout, bits: Long) extends Value`:

- **Type:** the layout's interned closed type.
- **Dependencies:** none. **Blockers:** none.
- **Key:** computed on first demand and memoized. The key is
  **representation-independent**: it equals the key the same value would have
  as a heap node, `ValueKey.application(head, fields, tpe)`. A heap node built
  for a word-eligible value by any path therefore still has the right key, and
  conversion and apartness stay correct. Only memory is lost. This is defence
  in depth; construction must still be canonical.
- **Sharing:** each layout preallocates every word whose bits are below 256. So
  every enum, and most small payloads, cost no allocation at all.

### Canonical construction

`Packed.construct`, through `foldCtor`, is already the single construction
entry; today it folds only Nat.

- Generalize it: when the constructor is word-eligible and every field is
  closed, encodable and fits, return a word; otherwise return a heap node.
- Make the raw constructor for constructor-headed `VApp`s private to `Packed`,
  so the compiler enforces the single entry. About 22 sites build `VCtor` or
  `VApp` directly today. Those with constructor heads move to the entry; stuck
  applications are unaffected.
- Substitution and materialization rebuild through the entry. A heap node whose
  neutral field becomes closed therefore turns into a word.

### Consumers

- **Matching sites.** Constructor values are read through the
  `ConstructorForm` views. Add a variant that also returns the
  `ConstructorHead`. Migrate the roughly 36 sites that match `VApp` or `VCtor`
  directly.
- **Words only decode.** Printing, structural descent, `StructEta` and
  projection decode a word through the view.
- **Words are never propositions.** Families whose instances may be
  propositions are excluded from layouts.

### Not covered here

- One-field wrappers around packed payloads (`String.mk`). These interact with
  the validated String layout and the delayed-key `String.append` path, and need
  their own design.
- Lists of words as packed arrays or bit strings (`List(Bool)`). This is
  shape-derived packing of linear types, a separate design.

On the 2026-10-05 corpus, the small-payload sums (`Char.mk`, `Expr.var`/`lit`,
`Leaf.var`/`lit32`) are about 10.6% of application allocations. Words also
subsume Part 1's nullary interning for closed families.

## Part 3. Bytecode evaluator with typed slots

### Code

Each `Plan` compiles to `Code`:

- an `ops: Array[Int]` stream with inline operands;
- a `consts: Array[AnyRef]` pool for globals, constructor heads, literals, match
  tables and nested plans.

Registers are today's frame slots, with the same layout. A call saves a return
address, `(code, pc)`, instead of pushing a `(kind, node, index)` continuation.

Each function compiles to two programs, as [TYPE_PROGRAMS.md](TYPE_PROGRAMS.md)
requires:

- a **body** `Code`, run to produce the function's value;
- a **type** `Code` for its Pi's codomain, run only when a type is asked for.

In the same way, each `match` gets a motive `Code`, and each constructor of an
indexed family gets an index `Code`. The body path never runs type code. Until
TYPE_PROGRAMS.md lands, the body path still computes value types as today; this
part only builds the structure.
Each of today's node kinds becomes one instruction family, and each
continuation kind becomes control flow:

| Instruction | Replaces |
|---|---|
| `LOAD_REF`, `LOAD_GLOBAL`, `LOAD_NAT`, `LOAD_STR` | `Ref`, `Global`, `NatLiteral`, `StringLiteral` |
| `CALL`, `TAIL_CALL` (function register, argument range, destination) | `Application` with `AppFunction`/`AppArgument` |
| `CONSTRUCT` (head, argument range, destination) | constructor application through `Packed.construct` |
| `MATCH` (scrutinee register, table) | `Matching` with `MatchScrutinee` |
| `BIND`, `MOVE`, `DESTRUCT` | `Binding` with `LetValue` |
| `CLOSURE`, `PI`, `SCOPE`, `SORT`, `PROP`, `FORM` | `LambdaValue`, `PiValue`, `Scoped`, `SortValue`, `Proposition`, `FormValue` |
| `RET` | `Return` |

Each constructor gets an index within its family. A match table is an array
indexed by that index, so dispatch is one array load: no name hashing, and no
`Some` or tuple. The boxed path (`frame.boxed`, with `Env`-based locals) remains
for closures that are not fast-path eligible, as today.

### Typed slots

Generalize the Nat slots (`values`, `longs`, `bigs`, `natTypes`). A slot holds
one of:

- a reference;
- an unboxed Nat (`long` or `BigInt`, as today);
- an unboxed word (`long` plus layout).

Then:

- `MATCH` on a Nat slot branches on zero or nonzero, and writes the predecessor
  into a long slot. No `VPacked` is built.
- `MATCH` on a word slot reads the tag, jumps, and writes the fields into slots
  by shift and mask.
- `CONSTRUCT` of a word-eligible constructor from Nat and word slots computes
  the bits straight into the destination slot. Nothing is allocated.

A slot is boxed only when its value escapes:

- into a heap node's field;
- into an `Env` or a closure capture;
- by return to a boxed caller;
- as an argument to a native or residual call, or to any generic path.

Boxing a word takes a preallocated `VWord` when one exists.

### Neutrals

Type checking spends most of its time on open terms, so neutrals are a first
class path, not a fallback.

- **Context slots.** A fourth slot kind holds a Nat context value as a base
  reference plus the two counts `[k, j]` (PACKED_CONTEXTS §1).
  - `MATCH` on a context slot with `j > 0` takes the `succ` branch and writes the
    predecessor's counts in place, so peeling a symbolic prefix allocates
    nothing per layer. With `j = 0` and `k > 0`, the match is stuck on the base.
  - `CONSTRUCT` of `succ`, and the validated `Nat.pred`, update the counts in
    place.
  - A context slot boxes through the smart constructor `natContext`.
- **Stuck terms.** A `match` on a neutral builds its stuck match, and a call
  with a neutral head builds its stuck application. Only these points box the
  live typed slots in scope. The stuck term is identical, key for key, to the
  one today's evaluator builds, so conversion and refinement are unaffected.
- **Cheap construction is a goal.** Building a stuck term today costs a key, a
  `DepSet` union and an evaluated type, which for a stuck match is its motive.
  TYPE_PROGRAMS.md removes the type. Dependency and key costs for neutrals are
  measured after each step here.

### PACKED_CONTEXTS

- Acceleration (PACKED_CONTEXTS §2) runs at entry, reading guard counts from
  long slots.
- Tail calls modulo a context (§3) are a `TAIL_CALL` variant, with a
  pending-context register per frame.

### Transition and tooling

- During the transition, the plan evaluator stays as a test-only reference,
  selected by a flag. It is removed once the bytecode evaluator passes the
  differential validation below.
- A disassembler prints `Code` for debugging.

## Order of work

1. Part 1. Measure.
2. Part 2, through `Packed.construct` and the views. Measure.
3. Part 3 with reference and Nat slots only, giving byte-identical outputs.
   Then add typed word slots and context slots. Measure.

Each step ships on its own.

## Not in scope

- Caching checked modules across runs.
- A runtime for closed programs (an erased value model, possibly compiled
  through LLVM).
- Removing eagerly computed value types: [TYPE_PROGRAMS.md](TYPE_PROGRAMS.md).
- Packing linear types (arrays, bit strings), one-field wrappers, ropes.
- Any change to definitional equality (see PACKED_CONTEXTS §6).
- A self-managed heap.

## Required validation

1. **Outputs.** Every generation example in `../lemur-raccoon` produces
   byte-identical output after each step, and `sbt validate` passes in both
   repositories. Key assertions stay on in tests.
2. **Allocation.** Make the 2026-10-05 census a permanent `-Draccoon.census`
   flag, and record its table after each step against the 2026-10-05 baseline.
   The census measures each step; it does not set targets.
3. **CPU.** Measure `attention`, `attention_pingpong`, `attention_a3b` and
   `tinygemm` with the paired native-image protocol of
   interpreter-performance.md. No step may regress.
4. **Key independence.** For generated word-eligible values, a `VWord` and a
   heap node built through a test-only bypass have equal keys and convert.
5. **Canonicity.** Every public construction path, including substitution and
   materialization rebuilds, yields a word for a word-eligible closed value.
6. **Bytecode differential.** The full test suite runs under both evaluators,
   with equal results and keys.
7. **No allocation per layer.** Structural recursion over a Nat, a word or a
   Nat context value held in slots allocates nothing per layer, measured with an
   allocation counter.
8. **Neutrals.** Stuck matches and stuck applications built by the bytecode
   evaluator have the same keys as those built by the plan evaluator, across
   the test suite.

## Open questions

- Should the intern tables use weak references, for long-running processes such
  as an editor server?
- Should a Nat field keep "all remaining bits", or should a constructor with
  two Nat fields get fixed budgets?
- Evidence fields: v1 excludes them from word-eligible constructors. Should they
  instead take 0 bits, with the canonical proof rebuilt from the proposition on
  decode?
