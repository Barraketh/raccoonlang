# Packed lists and kernel strings

Raccoon checks and runs programs with one evaluator, so lists and strings must
be cheap to build, match, compare and concatenate inside the kernel. This
document specifies how the kernel stores lists, how it keys them, the kernel's
`List`, `Char` and `String` declarations with their native operations, and why
the design takes the shape it does.

In brief:

- Any inductive whose values are "a run of layers ending in something" is
  stored in shared arrays instead of one object per element. The choice is made
  by the type's shape, so user types benefit as much as `List`.
- Storage is invisible. Every value has the same definitional equalities,
  matches, quotations and printed forms however it was built.
- Keys of such values are polynomials, which cons, tail and append update in
  constant time, so append can share storage instead of copying it.
- The kernel owns `List`, `Char` and `String`, as it owns `Nat`. Native
  `List.append` and `List.length` follow their source definitions, plus two
  definitional laws: `xs ++ [] = xs` and
  `length(xs ++ ys) = length(xs) + length(ys)`.
- The representation lives in one package, `com.raccoonlang.packed`, behind a
  small interface.

## Design principles

**Storage is invisible.** The same list may be stored as one run or several,
and two lists may share storage. Nothing outside the representation can tell.
Keys depend only on a list's elements and its end, and every reader goes
through the constructor view or the token interface. This is what lets the
storage strategy change without touching conversion, refinement or any other
kernel rule.

**Representation by shape, not by type.** What makes strings fast is about
sequences, not text: contiguous storage, constant-time matching and tails,
cheap equality, and fast append and length. The same properties help
`List(Stmt)`, a list of path steps, or any user type with the same shape.
Strings are special in only two ways: a literal needs a fixed type, since types
are derived locally and never from the expected type, so `Char` and `String`
must be kernel declarations; and text input and output happen at the edges.

**The kernel owns its builtins.** `List`, `Char` and `String` are declared by
the kernel beneath every prelude and program, so nothing about them is
validated or recognised in prelude source. The natives' meaning is fixed by the
kernel.

**Definitional equality stays small.** Code in definitional equality is
trusted, so a law becomes definitional only when it is cheap to decide
completely and stable under substitution. The kernel's list laws are the source
definition's equations plus the right unit and the length law, which need no
new value form. Associativity would need lists normalised by flattening, so it
is a prelude theorem instead (see [Laws](#laws)).

**The representation is contained.** Only the `packed` package knows chunks,
slots or segments. The rest of the kernel sees a word as a sequence of tokens,
and each consumer handles words in one place.

## List-shaped types

A type is **list-shaped** when:

- it is an inductive family with parameters and no indices, not a proposition
  family, not part of a mutual block, and not `Nat`;
- exactly one constructor, the **cons**, has a recursive field, and it has
  exactly one; that field's type is the family applied to its own parameters,
  not nested in another family and not under a binder;
- it has at least one other constructor, the **end constructors**, and none of
  them is recursive.

The cons constructor's other stored fields are its **payload**; the payload of
one cons application is a **layer**. Every value of a list-shaped type is zero
or more layers followed by a **terminator**: an end-constructor value, or a
stuck value (a variable, a stuck match or a stuck application). `List`
qualifies, and so do user types such as

```text
inductive Path : Type
 | done (dest: Node) : Path
 | step (dir: Dir)(rest: Path) : Path
```

`Nat` has the shape too, with an empty payload, but keeps its own compact
normal forms, which already do what packing would and also decide arithmetic.

`InductiveChecks` decides the shape once per declaration and records it on the
cons constructor's head (`ConstructorHead.listShape`: the recursive field's
index among the stored fields, and the payload width), so construction
dispatches on the head without a lookup.

## Words

### Representation

Every cons application of a list-shaped type is a **word**, a `VWord`. It is
never a `VApp`; `Value.VApp` requires this, as it does for Nat successors.

```text
Chunk                     a shared array of layers
  payloads                payload-width slots per layer
  front, back             the written range [front, back); claims extend it outward
  tpe                     the family instance of every layer in the chunk

Word (a segment)          the layers in chunk[start, end), then next
  next                    the rest: another word, or the terminator
  layers                  the number of layers in the whole chain
  terminator              the first value along the chain that is not a word
  φ                       the key, in both lanes (see Keys)
```

A word is a chain of **segments**, each a run of slots in one chunk, ending in
its terminator. Invariants:

- A written slot never changes, so segments can share slots freely.
- `start < end`, so every word has at least one layer, and every word is
  constructor data, never stuck: a word has no reduction blockers and its
  `rigidForm` is a data constructor.
- `next` is a value of the same family in any representation; `layers`,
  `terminator` and `φ` are derived from it where the segment is built.
- A word's type is its chunk's type.

### Construction

`ConstructorValue.apply` sends a cons to `Words.cons`, which splits the fields
into the layer and the tail `t`:

1. If `t` is a word whose first segment starts at its chunk's `front`, with a
   free slot before it, and the new cons has the chunk type's key, it **claims**
   that slot, writes the layer, and returns the segment one slot longer. O(1).
2. Otherwise it starts a new chunk, writes the layer into the chunk's last
   slot, and returns a one-layer segment followed by `t`.

The new chunk doubles the tail chunk's capacity, up to 4096, only when `t`
starts at slot 0 of its chunk, so the conses that filled that chunk continue
into the next. Any other tail, such as one whose front slot another value
claimed or one decoded mid-chunk, gets the minimum, 8.

Why: a list built cons by cons fills chunks from the back with doubling sizes,
so it has O(log n) segments up to the maximum size; two conses onto one tail
never copy it, since the first claims the slot and the second starts a chunk
pointing at the shared tail (Bagwell's VList technique); and replacing the head
of a long list costs a minimum-size chunk, not a large one. Requiring equal type
keys keeps one type per chunk without retyping any value.

### Observation

For a word `v`, `ConstructorValue.unapply(v)` returns the cons head with the
layer at `start` and the tail: the segment from `start + 1` with the same `next`
while layers remain, and `next` otherwise. This is O(1), and the tail's key
follows from `v`'s.

Single-constructor matching and refinement use this view. Code that walks
whole words reads them through the token interface (see
[The packed package](#the-packed-package)) in one loop per word, so long lists
never recurse once per element.

### Dependencies and structural conversion

- `synDeps` is exact, because occurs and scope checks read it. It is computed on
  demand for the whole chain from the back in one loop, and cached on each
  segment. A chunk bounds the slots with dependencies by a window, so a
  segment outside that window, such as most strings and the closed prefix of
  `cons(a, cons(b, xs))`, answers in O(1) and allocates nothing. Inside the
  window the chunk caches dependency unions for aligned blocks of 1, 2, 4, …
  slots. A query combines O(log capacity) block summaries with one union;
  missing blocks are built once from their children. Only wholly written blocks
  are cached, so their summaries remain valid when either end grows. Growing
  prefixes and decoded tails share O(n) cached summaries for n written slots,
  in addition to the space for the dependency sets themselves. A first query
  may inspect all payloads in its range; subsequent queries reuse the blocks.
- `needsStructuralDefEq` is the chunk's flag, `next`'s, or the type's.
  Over-approximating it costs only an unneeded structural comparison.

Chunks are single-threaded, like the evaluator: claims, writes and metadata are
plain reads and writes.

### Memory

A layer costs its payload references and nothing else: no per-element key,
argument vector or object. Each segment costs two objects, its representation
and the `VWord` that wraps it, and decoding a tail allocates one segment.
Elements stay boxed, but closed `Char` values are interned, so a string costs
about one reference per character. A segment keeps its whole chunk alive;
doubling bounds the waste for lists built in order.

## Keys

### Why polynomial keys

Conversion compares keys first, and equal keys are taken as convertible. With
sharing, one chunk's slots are followed by different `next` values in different
lists, so no key can be stored per slot; and recomputing a key by walking a
segment would make decoding quadratic. The kernel's usual key, a one-way mix
folded from the end, can extend a list by one element but cannot remove one, and
cannot combine two lists without walking the left one.

The operations need a key that turns concatenation into arithmetic, with an
inverse for removing the first element: a polynomial in a base B.

### Definition

For a word whose layers contribute the letters s₀ … sₙ₋₁ and whose terminator
is τ, in each of the key's two 64-bit lanes:

```text
φ = s₀ + s₁·B + … + sₙ₋₁·B^(n−1) + B^n · τ̂        in F = Z_p, p = 2^61 − 1
```

A layer's letter mixes its payload keys under a layer tag and reduces each lane
into F. τ̂ is the terminator's ordinary key, mixed under a terminator tag and
reduced the same way; a value that is not a word has that as its φ. The key of a
word is its φ in both lanes. Each lane has its own fixed base and uses only that
lane of its inputs, matching the rest of the kernel, where the `hi` lane of a
key reads only its children's `hi` lanes and `lo` only `lo`.

The type is not mixed into letters: every layer of a word has the terminator's
type, and the terminator's key determines it.

### Maintenance

| Operation | φ of the result | `layers` of the result |
|---|---|---|
| cons layer e onto t | λ(e) + B·φ(t) | layers(t) + 1 |
| tail of v, whose first layer is e | (φ(v) − λ(e))·B⁻¹ | layers(v) − 1 |
| segment h of k layers followed by a new rest instead of its old one | φ(h) + B^k·(φ(new rest) − φ(old rest)) | k + layers(new rest) |

A value that is not a word has 0 layers. B⁻¹ is a constant; B^k costs one
modular power. Splitting a word's layers into segments leaves φ unchanged, which
is what makes storage invisible to keys. Because letters come from payload
keys, building a layer computes its payload's key, where other values compute
keys only when first demanded.

The debug flag `-Draccoon.verifyPackedKeys=true` recomputes every built word's
`layers` and φ from its chain and fails on disagreement. It makes building
quadratic in a word's length, so it is off by default.

### Trust

Like every key in the kernel, word keys guard against accidental collisions,
not crafted ones. They are 122 bits over two lanes. The modulus is prime because
polynomial hashing modulo 2^64 has structured collisions that ordinary programs
could produce: a Thue–Morse word and its complement collide for every odd base.

A polynomial with a public base does make crafted collisions cheap, by lattice
reduction or a generalized-birthday search. The answer to crafted input is a
checking mode that does not trust keys for equality, not a secret base: a
secret would make keys differ between runs and constrain how keys may reach
output, for a guarantee that mode gives anyway. Keys are therefore deterministic.

## Kernel `List`

### Declarations

`Kernel.Source` declares, beneath every prelude and program:

```text
inductive List (A: Sort($u)) : Sort(u)
 | nil {A: Sort($u)} : List(A)
 | cons (head: $A in Sort($u))(tail: List(A)) : List(A)

namespace List {
  def append (xs: List($A))(ys: List(A)): List(A) := builtin
  def length (xs: List($A)): Nat := builtin
}
```

`Sort` is a kernel declaration too, since `List` needs it. None of these can be
redeclared. The prelude's other list functions, such as `map`, `foldr` and
`reverse`, are source over the kernel type, and `List` is list-shaped, so its
values are words.

A `List` value is `nil`, a word, or a stuck value. A stuck value occurs only at
the end of a list: as the whole value, or as a word's terminator.

### Native append

`append(l, r)`:

1. If `l` is `nil`, the result is `r`.
2. If `r` is `nil`, the result is `l`.
3. If `l` is a word with terminator τ, its segments are rebuilt from the back,
   in one loop, onto τ ++ r: that is `r` when τ is `nil`, and otherwise the stuck
   append `List.append(τ, r)`. Each segment keeps its slots and takes the rebuilt
   rest as its `next`, so element storage is shared, never copied, except at the
   junction below. The cost is one segment per segment of `l`.
4. Otherwise `l` is stuck, and the result is the stuck append
   `List.append(l, r)`.

The **stuck append** is an ordinary stuck application of the native. Generic
code handles it like any other: it converts with an application of the same
head to convertible arguments, has no rigid form, matches on it are stuck, and
it prints and quotes as an application. It nests only as deep as the program
writes it, so `append(append(x, m), r)` stays
`List.append(List.append(x, m), r)`.

It is blocked on the reduction blockers of its left operand, plus those of `r`
when `r` is neither a word nor `nil`. Those are exactly the changes that let it
compute: the left operand becoming `nil` or a word, and `r` becoming `nil`,
which a word never does. When one is solved, the generic resumption re-runs the
native, which applies the right unit if `r` became `nil`.

### The junction

When `l` ends in `nil` and `r` begins with a segment, let A be `l`'s last
segment and C be `r`'s first. If their chunks have types of the same key:

1. If the smaller of A and C (C on a tie) fits in free slots beside the larger
   that can be claimed, it is copied there: after A if A ends at its chunk's
   `back`, or before C if C starts at its chunk's `front`.
2. Otherwise, if A is the larger and ends at its chunk's `back` without enough
   room, A and C are copied into a new chunk of twice their combined length,
   filled from slot 0, leaving free slots after them.
3. Otherwise A links to C.

Why: append is never worse than copying append (at most 2·|l| elements copied,
and at most one new segment per element of `l`), while the common patterns get
much better:

- **Accumulating on the left**, repeated `acc ++ piece`, keeps `acc` in one
  segment that grows like an array list: amortized O(|piece|) per step.
- **Accumulating on the right**, repeated `piece ++ acc`, never rebuilds `acc`:
  O(|piece|) per step, by claiming before `acc` or linking.
- **Branching**, two appends onto one value, finds the slots already claimed and
  links, so shared data is never copied.
- The prelude's `List.reverse`, which appends a one-element list to the reversed
  tail, is linear.

### Laws

These hold definitionally:

- `append(nil, r) = r` and `append(cons(h, t), r) = cons(h, append(t, r))`, the
  source definition's equations;
- the right unit `append(l, nil) = l`, for every `l`, stuck or not;
- closed lists compute, as does any append whose left operand is a word ending
  in `nil`;
- `length(append(l, r)) = length(l) + length(r)` and
  `length(cons(h, t)) = succ(length(t))` (see [`length`](#length)).

Associativity is not definitional: for a stuck `x`, `append(append(x, m), r)`
and `append(x, append(m, r))` are different stuck appends. The prelude proves it
as `List.append_assoc`, by structural recursion on the first list.

Why this set: the right unit and the length law keep the analogy with `Nat`,
where `n + 0 = n` and lengths add, and each is a few lines with no new value
form. The right unit is the native's second case plus one blocker; the length
law is local to `length`. Associativity would require normalising lists into
flat sequences of elements and stuck values, with stuck values in the middle of
a list, a new kind of stuck word, its own blocking rule, cancellation in
unification, and special cases in every traversal. That is the kind of complex
logic definitional equality should not carry. Without it the kernel behaves as
Lean, Coq and Agda do, none of which make associativity definitional.

### Conversion

Two words convert exactly when they have the same number of layers, agree layer
by layer, and have convertible terminators. Conversion tries keys first; if they
differ, it rejects words with different layer counts in O(1), since a
terminator is never a word. Otherwise it walks both words with two cursors
(`Words.zip`), skipping in O(1) any run where both cursors are on the same chunk
slot, and accepting where both rests begin new segments with equal keys.

### Substitution

The native computes each segment's key, count and structural flag when it
builds the segment, from those of the rest, which it built first, so none of
them recurses down a word. `materialize` of a word rebuilds it in one loop
(`Words.map`): it keeps the first rest with no solved dependencies, or else
materializes the terminator, so a stuck terminator solved to `nil`, a word or
another stuck value is spliced in, and a stuck append resumes by the generic
rule. Then, from the back, each segment is rebuilt onto it: one whose payloads
have no solved dependencies keeps its slots, joining storage at the junction as
above where its old `next` was the terminator; any other is consed again.

### Unification

Refinement records consequences only and never searches. Two words are unified
in one loop over their aligned layers: payloads before the recursive field at
once, and those after it with the layers' types once the rests are done, as the
constructor rule orders them. `nil` against cons is a `Contradiction`. Where one
word ends, its terminator is unified with the other's rest as usual, so a
refinable variable is linked, with the occurs check.

A stuck append against anything it does not convert with is `Stuck`, as for any
stuck application: `append(xs, ys) = cons(a, t)` has two solution shapes, and
`append(xs, ys) = nil` needs both operands. Deriving `xs = nil` and `ys = nil`
from the latter would be sound and cheap, but nothing needs it yet.

### Termination and positivity

Only cons layers are structural subterms: `r` is not a subterm of
`append(x, r)`, just as summands are not subterms of a Nat sum. The termination
check walks a word's layers and then its terminator, with an O(1) path for a
suffix stored in the same chain (`Words.isProperSuffix`).

Positivity walks a word in one loop: the layers' types are positive positions,
and payloads and the terminator are constructor arguments. A stuck append is an
application of a native, whose arguments have no positive positions.

## `length`

The native maps a list to a Nat form: the layers of every word along it, plus a
stuck `length(x)` for each stuck value `x`, blocked on `x`'s reduction blockers.
It looks through stuck appends, adding the lengths of both operands. This is the
only place outside generic code that recognises the native's application, and it
stays inside `packed`.

A program can share stuck appends, as repeated `let y := List.append(d, d)`
does, so one list can use an application exponentially many times. `length`
visits each distinct application once, by identity: one loop orders them so each
comes after everything that uses it, a second counts the uses of each, and a
stuck `length(x)` met m times is added as `m * length(x)`. Neither loop
recurses, so applications may nest as deep as a program writes them, and the
parts are summed in one balanced tree. The cost is linear in the distinct
applications plus the size of the sum. On a word ending in `nil`, `length` is
O(1), since every segment records its chain's layer count and terminator.

## Kernel strings

### Declarations

`Kernel.Source` also declares:

```text
struct Char : Type
 | mk (val: Nat) : Char

struct String : Type
 | mk (data: List(Char)) : String
```

with the selectors `Char.val` and `String.data`. None can be redeclared.

`Char.mk` is unconstrained: a character is text only when its code is a closed
Unicode scalar value, a numeral at most U+10FFFF outside the surrogates. Why:
a validity proof would need a kernel-owned proposition, since `Eq` is a prelude
family, and literals already produce only scalars. `String` is a struct rather
than `List(Char)` itself so that strings and lists stay distinct for instances
and printing.

Strings have no laws of their own: they convert exactly when their lists do. The
prelude's `String.append` and `String.length` apply the `List` natives to
`data`, so each is one interpreted step, not one per character.

### Literals

A string literal `"…"` denotes a sequence of Unicode scalar values. It accepts
the escapes `\"`, `\\`, `\/`, `\b`, `\f`, `\n`, `\r`, `\t` and `\uXXXX`; a
high-surrogate escape must be followed by a low-surrogate escape, and the pair
denotes one scalar. An unpaired surrogate, escaped or raw, an unknown escape and
a raw control character below U+0020 are parse errors at the offending position.

A literal always has type `String`, whatever type is expected. It evaluates to
`String.mk` of `nil`, or of one segment filling a chunk of exactly its size from
slot 0, followed by `nil`, with its key computed in one pass. Each evaluation of
the same literal node shares that value; this is safe because the chunk is
full, so no claim can extend it.

### Interning

Every `Char.mk` of a closed code at most U+10FFFF, surrogates included, is
interned: construction returns one value per code, so literals, decoded lists
and characters built by source share their characters. The table has two
levels, with pages of 4096 codes allocated when their first character is built.
Larger codes are never scalars and are not interned.

### Printing and quotation

A `String.mk` whose list ends in `nil` and holds only closed scalar characters
prints and quotes as a literal. Any other string prints as `String.mk` applied
to its list, such as `String.mk([Char.mk(97), Char.mk(55296)])`, and a bare
`List(Char)` prints as a list.

## Printing and quotation of lists

Kernel lists print as `[a, b] ++ end`, with `nil` as `[]` and a stuck append as
`List.append(x, r)`; user list-shaped types print as constructor applications.

Quotation emits a word as one flat `ElabAst` node, `Word(consHead, pieces)`.
Each piece is either a layer, the quoted arguments of its cons application
around the recursive field, or a splice, a list term; the last piece is a
splice, the end of the word. For `List`, a maximal run of closed scalar
characters is a splice of `String.data` of a string literal, which also ends the
word when only `nil` follows; a user chain is its layers, then its terminator. A
word of one splice quotes as that splice, and a `String.mk` of a closed string
as a bare literal.

Evaluating a `Word` is a loop that, from the back, conses each layer onto the
rest and appends each other splice with the native, rebuilding the same value
with the same key. Why a flat node: nested cons and append terms would be as
deep as the list, and any recursive walk over them would overflow the stack for
long lists. The node prints as the nested applications it stands for.

## The packed package

`VWord` lives in `Value.scala`, since `Value` is sealed, but only delegates
`tpe`, `key`, `synDeps` and `needsStructuralDefEq` to its representation.
Everything else is in `com.raccoonlang.packed`, with internals private to it:

| File | Contents |
|---|---|
| `Field.scala` | arithmetic modulo 2^61 − 1 |
| `PolynomialKeys.scala` | bases, letters, terminator symbols and the maintenance formulas |
| `Chunk.scala` | chunks, claims and dependency metadata |
| `Word.scala` | the segment representation, `Token` and `Zipped` |
| `Words.scala` | the interface below: construction, the junction, the stuck append, `length`, traversals and the key check |
| `Strings.scala` | literals, `Char` interning and reading text |
| `Storage.scala` | a read-only view of segments and chunks for tests; the checker never uses it |

Consumers see a word only as a sequence of **tokens**: its layers, then its
end, the terminator.

| Operation | Used by | Hides |
|---|---|---|
| `foreach(word)(layer, end)` | printing, quotation, positivity, termination | segments, slots and chunk boundaries |
| `zip(a, b)(layers)` | conversion, unification | the O(1) skip over shared storage |
| `sameLength(a, b)` | conversion only | layer counts |
| `map(word, mayChange, mapValue)` | `materialize` | per-segment rebuilding, the junction, which segments are kept |
| `isProperSuffix(candidate, root)` | termination | chunk, offset and `next` comparisons |
| `cons`, `uncons`, `append`, `length`, `Strings.literal` | `ConstructorValue`, the natives, literals | claims, chunk growth, key maintenance, the stuck append |

```scala
object Words {
  def cons(head: ConstructorHead, shape: ListShape, fields: Vector[Value], tpe: Value): Value
  def uncons(word: VWord): (ConstructorHead, Vector[Value])
  def append(l: Value, r: Value): Value
  def length(list: Value): Value
  def foreach(word: VWord)(layer: Token => Boolean, end: Token => Boolean): Boolean
  def sameLength(left: VWord, right: VWord): Boolean
  def zip(left: VWord, right: VWord)(layers: (Token, Token) => Boolean): Zipped
  def map(word: VWord, mayChange: DepSet => Boolean, mapValue: Value => Value): Value
  def isProperSuffix(candidate: Value, root: VWord): Boolean
}

final class Token {          // valid only during the callback that receives it
  def head: ConstructorHead  // a layer's cons head
  def recursiveIndex: Int
  def payloadWidth: Int
  def payload(index: Int): Value
  def tpe: Value             // the type of the rest from this token
  def value: Value           // the end's value
  def rest: Value            // the word from this token on, or the terminator
}

sealed trait Zipped          // Refused | Agreed | Rests(left, right)
```

- Callbacks return whether to continue. `zip` returns `Refused` when its
  callback declines, `Agreed` where both rests begin new segments and are the
  same value or have equal keys, and otherwise `Rests` where a word ends; its
  rests are built only on demand. `sameLength` must not be used for
  unification, where a stuck end of one word can still be solved to the
  other's remaining layers.
- `Token.rest` serves quotation, which stops at a rest with its own quote-map
  entry, and termination, which compares each layer's tail with the candidate.
  At a segment start it is the existing word; in the middle of a segment it is
  built, and asking at every token stays linear.
- `ValueKey` dispatches a word's key to its representation, reserves the tags
  of word symbols beside its own, and exposes a mixer from a tag so that letters
  and terminators reuse the kernel's mixing.
- The stuck append's head is the native `Kernel.append`, compared by identity,
  as `NatNormalForm` recognises a stuck `Nat.sub`.

## Costs and limits

Known costs:

- Decoding a tail allocates a segment, where decoding a cons `VApp` allocated
  nothing; building no longer allocates per element.
- Building a layer computes its payload's key.
- A segment keeps its whole chunk alive.
- Repeated `piece ++ acc` leaves about one segment per two appends, because the
  junction alternates between growing and linking; each step still copies at
  most a few elements.
- The blockers of a stuck append include `r`'s when `r` is stuck, so a chain of
  k right-nested stuck appends of distinct stuck values stores O(k²) blocker ids
  in all. Blocking only on the leftmost stuck operand of each side would be
  enough, but is not implemented.
- Printing, generic structural conversion and `materialize` walk shared stuck
  terms without memoization, as for any shared stuck term in the kernel, so
  repeated doubling of a stuck list costs exponential time there.

Not covered:

- indexed list-shaped families such as `Vec`;
- unboxed payload storage, such as an int array for `Char`;
- natives beyond `append` and `length`, such as `get`, `drop` and `take`, which
  `layers` would make O(segments);
- surface syntax for list literals;
- literals in match patterns.
