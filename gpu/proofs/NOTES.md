# Soundness proofs of the structural checkers: notes

Layer 1 of `gpu/OBLIGATIONS.md` §8, second half: each checker of `gpu/Check.rac` proved sound against a short
syntactic statement of its invariant in `gpu/Spec.rac`. This file records what was proved and, as evidence for the
design of proof automation, what made the proofs hard in Raccoon as it is today. It was written as the proofs were.

Line counts are of the files as committed, comments included.

## Status

| Checker | Spec (`Spec.rac`) | Proof | Lines | Status |
|---|---|---|---|---|
| (shared) | occurrence relations and program order, 127 lines | `Fold.rac`: the traversal lemmas | 450 | done |
| (shared) | | `Lib.rac`: Bool, Nat, List and string facts | 184 | done |
| (shared) | | `NatSet.rac`: `Check.NatSet` is a set | 148 | done |
| `errors` | `NoErrors`, 5 lines | `Errors.rac` | 32 | proved |
| I2 `sharedMemory` | `SharedMemory`, `SharedAt`, 18 lines | `SharedMemory.rac` | 109 | proved |
| I3 `namedBarriers` | `NamedBarriers`, `BarrierIds`, `BarrierCounts`, `Barrier`, `LiteralOperands`, 29 lines | `Barriers.rac` | 273 | proved |
| I4 `literals` | `Literals`, `Lit32`, `Lit64`, 25 lines | `Literals.rac` | 108 | proved |
| I5 `names` | `Names`, `Chosen`, `CIdent`, `PrinterName`, `Declared`, `Twice`, …, 60 lines | `Names.rac` | 266 | proved |

## The shape of every proof

Every checker is a walk that collects messages, and every statement in `Spec.rac` is a universal over an occurrence
relation (`InBlock`, `ExprIn`, `HostExpr`, `Mem`, …). The proofs share one argument, in `Fold.rac`:

1. **Keeps.** The checker's step never removes a message: `Fold.Keeps(A, f)`, that `f(found, x)` empty implies `found`
   empty. Proved per step, by cases on the statement or expression.
2. **Acc.** A walk that ends empty started empty (`foldlAcc`, `exprFoldAcc`, `stmtExprsAcc`, `blockFoldAcc`,
   `blockExprsAcc`, `hostExprsAcc`), by structural recursion on the data walked.
3. **At.** A walk that ends empty found nothing at each thing it visits: `f(nil, x)` is empty for every `x` the
   occurrence relation reaches (`foldlAt`, `exprFoldAt`, `stmtExprsAt`, `blockFoldAt`, `blockExprsAt`,
   `hostExprsAt`), by recursion on the data, matching the occurrence proof.
4. **The step's condition.** `Check.unless(found, ok, message)` empty means `ok` is `Bool.true` (`unlessOk`), and a
   Bool condition is the Prop the spec states by conversion (`Nat.lt` is `Eq(Bool, Nat.ble(…), Bool.true)`).

All the real induction is in `Fold.rac`; the per-checker files are step lemmas and plumbing.

## Per invariant

**errors.** Spec: `(m: String) -> InBlock(Stmt.error(m), k.body) -> False`. The proof is `Fold.blockFoldAt` applied
to a 14-case `Keeps` lemma for the step; no lemma of its own.

**I4, literals.** Spec: every `n` that `Lit32(k, n)` (a `lit` in the body or the launcher's expressions, the block
size, a box dimension) is `Nat.lt(n, Cuda.u32Limit)`, and every `Lit64` below 2^64. Needed F1's checker change.

**I2, shared memory.** Spec: `Nat.le(k.dynamicShared, 232448)`; a positive size means `k.launcher` is not `none`;
a `Stmt.shared` anywhere in the body means the size is 0; every `sharedAddr`/`sharedPtr` offset is below the size.
Two small Bool/Nat facts (`orNot`, `notPositive`).

**I5, names.** Spec: the kernel's name is `Chosen` (a `CIdent`, a letter or `_` then letters, digits and `_`, and
not a `PrinterName`: `v` and digits, `gpu_…`, or one of the launcher's locals); the parameters' names are
`Declared` (each chosen, none the kernel's name, none `Twice` in the list); every `param`/`paramAddr` in the body
names one of them; and likewise for the launcher, whose declared names are its parameters' then its maps' and whose
expressions name only its parameters. This is the first proof that needs both directions of a Bool test: soundness
for what the checker accepts (`isIdent` true gives `CIdent`), and completeness for what it rejects (a
`PrinterName` makes `printerName` true, so its `Bool.not` being true is a contradiction). Hence `Lib.rac`.

`Check.declaredNames` folded a `Prod(List(String), List(String))` of the names so far and the messages over the
names with `List.foldl`. It became a direct recursion, `declaredAfter`, whose `before` is an argument: the lemmas
(`declaredChosen`, `declaredFresh`, `declaredOnce`) then recurse on the names with `before` growing, which is the
whole induction. The fold was not attempted, since `Fold`'s lemmas are for a `List(String)` accumulator and a pair
would have needed its own `Keeps`, `Acc` and an invariant relating the first component to the prefix walked.

**I3, named barriers.** Spec: every `bar.sync` in the body (an asm statement with its template) has
`LiteralOperands` (no outputs, two `lit` inputs); every `Barrier(id, threads, s)` in the body has `id` in 1..15 and
`threads` positive with `Nat.mod(threads, 32) = 0`; and no two barriers, one `Before` the other in
`Spec.statements(k.body)` (every statement at any depth, in program order), have one id. Distinctness needs positions,
which `InBlock` does not have (two identical `bar.sync 1, 64` are one statement to it), hence the flattening. The
proof first turns the checker's `blockFold` into a `List.foldl` over `Spec.statements` (`Fold.blockFusion`, generic in
the walk's state), then reasons about a flat walk: ids seen stay seen (`stepSeen`), a barrier's id was not seen before
it (`barrierFresh`), and an id is seen after its barrier (`NatSets.inserted`). The literal operands come from a case
split on the operand lists and on `Check.literal` of each (`shape`, `twoLiterals`, `literalSome`), which is the only
place the proof inspects expressions.

The checker's steps were named (`barrierStep`), and the decisions it matched on became arguments of `barrierAt`
(`isBarrier`, `args`), so the lemmas case on variables (F2). The sets of ids needed a change of representation,
next.

**`Check.NatSet`.** The trie branched on `Nat.isZero(Nat.mod(m, 2))` and recursed on `Nat.div(m, 2)`, and a node held
a Bool. Its soundness (a member was inserted) then rests on distinct numbers having distinct paths, which is
arithmetic about the prelude's `Nat.div` (a `divFuel` recursion) and `Nat.mod` (`a - (a / b) * b`) that no library
provides, and every step case-splits on two computed parities at once (the member's and the inserted number's),
which F2 makes painful: each needs a mirror definition and an `Eq.subst` along the parity's equation. It became a
trie that follows a precomputed path (`NatSet.path(n)`, a `List(Bool)`) and whose node lists the numbers inserted at
it. Membership compares numbers at the end of the path, so no fact about paths is needed, and every case split is on
a path's head, a variable. `NatSet.rac` proves the three facts the checkers need (`inserted`, `kept`, `fromInsert`) in
148 lines of plain structural recursion. Check time on the persistent GEMM did not change measurably (the machine's
load dominated the noise; see the report).

## Lemmas a standard library would provide

Written here because Raccoon's prelude has none of them:

- **List membership** as an inductive predicate (`Spec.Mem`), `Mem` of `List.append` left and right
  (`Fold.memAppendLeft`, `memAppendRight`).
- **`List.foldl` with a non-shrinking step**: emptiness propagates backwards (`foldlAcc`), and to each element
  (`foldlAt`). The same two lemmas again for each of the AST's own folds (`exprFold`, `stmtFold`/`blockFold`).
- **Reverse**: `revOnto(xs, acc)` empty implies both empty (`revOntoAcc`, `inOrder`).
- **Constructor disjointness** as named lemmas: `cons ≠ nil` (`consNotEmpty`), `some ≠ none`
  (`SharedMemory.someNotNone`). The prelude has `Bool.falseNeTrue`, `Nat.succNeZero`, and nothing for `List` or
  `Option`.
- **Bool elimination**: `Bool.or(Bool.not(a), b) = true` and `a = true` give `b = true` (`SharedMemory.orNot`);
  the `unless` lemmas are `Bool.cond` elimination.
- **Nat order facts**: `Bool.not(Nat.blt(0, n)) = true` gives `n = 0` (`SharedMemory.notPositive`).
- **Bool reflection** (`Lib.rac`): `Bool.and` and `Bool.or` introduction and elimination into `Eq(Bool, …, true)` and
  `Or` (`andLeft`, `andRight`, `andIntro`, `orCases`, `orLeft`, `orRight`, `notBoth`); `Nat.beq` sound and reflexive
  (`beqSound`, `beqRefl`); `List.all` sound and complete (`allMem`, `allIntro`); string equality, `Check.sameChars`
  and `Check.same`, sound and reflexive; `Check.mentions` (`List.any` of `same`) sound and complete. `Char` and
  `String` equality from their fields is `congrArg(h, Char, Char.mk)`, which structure eta makes a proof about `c`.
- **Congruence of a two-argument constructor** (`Lib.consEq`): the prelude's `congrArg` takes one argument.
- **`List.foldl` over `List.append`** (`Fold.foldlAppend`), and **fold fusion** for the AST (`Fold.stmtFusion`,
  `blockFusion`): a derived traversal is a fold over a flattening. `Option.some` injectivity (`Barriers.someInj`,
  copied from the prelude's `Nat.succInj` idiom), `Nat.isZero` soundness (`Barriers.isZeroSound`).
- **`Eq` transport**: never needed as a lemma, since matching an equation proof rewrites the goal and every
  hypothesis (finding P1).

## Findings

Each finding has a minimal example and a guess at the feature that would remove it. P-findings are things that
worked better than expected.

### P1. Matching a variable refines every hypothesis, and matching `Eq.refl` rewrites

Matching on a variable (or a projection of a struct-typed variable, such as `k.launcher`) refines the motive and the
types of all hypotheses in scope, Agda style. No convoy pattern is needed, and `match e returning … with | Eq.refl z
=> h` transports `h` along `e` (used for every rewrite in these proofs):

```raccoon
def unlessOk (found: List(String))(ok: Bool)(message: Unit -> String)
    (h: Eq(List(String), Check.unless(found, ok, message), List.nil(String))): Eq(Bool, ok, Bool.true) := {
  match ok returning Eq(Bool, ok, Bool.true) with
  | Bool.true => Eq.refl(Bool.true)
  | Bool.false => { match h returning Eq(Bool, Bool.false, Bool.true) with }   // h: Eq(…, List.cons(…), List.nil)
}
```

### P3. A `let` can name a `returning` motive

`let goal := Eq(Expr, x, Expr.lit(n))` then `match x returning goal with` refines `goal` in each branch like a written
motive. Found late: `NatSet.rac` still restates its motives (up to 130 characters) in each of its nested matches.

### P2. Induction over an inductive predicate works through its data index

A proof cannot be a termination metric, but matching an occurrence proof refines its data index, and recursion on
the fields it exposes is accepted as structural descent on that index:

```raccoon
def blockFoldAt (y: Stmt)(b: Block)(occ: Spec.InBlock(y, b)) … decreases structural(b) := {
  match occ returning … with
  | Spec.InBlock.tail s rest inner => Fold.blockFoldAt(y, rest, inner, …)   // rest is a subterm of b, refined
  …
```

So every "At" lemma is a recursion on the occurrence proof in all but name, with no case split on the data first.

### F1. A native Nat operation on a variable and a large literal hides its definition

`Nat.lt(n, m)` is `Eq(Bool, Nat.ble(Nat.succ(n), m), Bool.true)`, and `Nat.blt(n, m)` is defined as
`Nat.ble(Nat.succ(n), m)`. But `blt` is native, and applied to a variable and a literal above the unfolding limit
(2^8) it is a neutral headed by `blt` that never unfolds (`docs/kernel.md`, natural numbers). So:

```raccoon
def f (n: Nat)(h: Eq(Bool, Nat.blt(n, 4294967296), Bool.true)): Nat.lt(n, 4294967296) := h
// type mismatch: Nat.ble(Nat.succ(n), 4294967296) vs Nat.blt(n, 4294967296) (not reducible: stuck)
```

Nor can it be proved propositionally: induction on `n` meets `Nat.blt(Nat.succ(m), 4294967296)`, which is as stuck.
The checker compared literals with `Nat.blt(n, Cuda.u32Limit)`, so the spec's `Nat.lt` could not be reached from it.
Worked around by a checker change: `Check.below(n, limit)` is `Nat.ble(Nat.succ(n), limit)`, which is `Nat.lt`'s
own form. With no literal above the limit (`Nat.blt(offset, bytes)`, both variables) the body unfolds and nothing is
lost.

*Feature:* let a native operation whose declared body is not recursive (`blt`, and wrappers like it) unfold that one
layer on neutral arguments, since the limit exists only to bound recursive unfolding; or ship the native equations
as trusted propositional lemmas (they are obligation T5 already).

### F2. No `inspect`: matching a computed value refines nothing

Matching an application, such as `Nat.isZero(n)` or `Check.NatSet.member(s, id)`, refines neither the motive nor the
hypotheses, so a hypothesis about a function that branches on the same value stays stuck:

```raccoon
def g (n: Nat): Nat := { match Nat.isZero(n) returning Nat with | Bool.true => 0 | Bool.false => 1 }

def t (n: Nat)(h: Eq(Nat, E.g(n), 0)): Eq(Bool, Nat.isZero(n), Bool.true) := {
  match Nat.isZero(n) returning Eq(Bool, Nat.isZero(n), Bool.true) with
  | Bool.true => …    // goal still Eq(Bool, match n …, Bool.true)
  | Bool.false => …   // h still Eq(Nat, E.g(n), 0): `match h` has a missing Eq.refl case
}
```

Every decision a proof must case on has to reach it as a variable. `Check.unless(found, ok, message)` does that
by taking the decision as an argument, which is why most of these proofs are easy: `unlessOk` is stated over a
variable `ok` and applied to the checker's expression. Where a checker matched a computed Bool itself, it was
restructured to go through a function taking it as an argument, or the lemma was stated over a Bool variable and
applied to the expression (`SharedMemory.orNot`, `notPositive`).

Where the match is inside a function the proof reasons about (`Check.sameChars` matches `Nat.beq(c.value,
d.value)`), a *mirror definition* works: restate the match over a variable (`Lib.sameRest(heads, rest, more)`),
prove the lemma by matching the variable, and apply it to the expression. Conversion identifies the two blocked
matches, since they have the same scrutinee and branches:

```raccoon
def sameRest (heads: Bool)(rest: List(Char))(more: List(Char)): Bool := {
  match heads returning Bool with
  | Bool.true => Check.sameChars(rest, more)
  | Bool.false => Bool.false
}
// h: Eq(Bool, Check.sameChars(List.cons(c, rest), List.cons(d, more)), Bool.true) is accepted at
// Lib.sameHeads(Nat.beq(c.value, d.value), rest, more, h), whose h is Eq(Bool, Lib.sameRest(…), Bool.true)
```

It costs a definition and two lemmas per such match, and the proof must copy the checker's branches exactly.

*Feature:* a `match e as b with (h: Eq(Bool, e, b))` form (Agda's `with … in`, Lean's `match h : e with`) that
abstracts `e` in the goal and in the hypotheses and hands the branch the equation.

### F3. Proofs cannot name what a checker leaves anonymous

A lemma about a checker's step must name the step, but the checkers folded with inline lambdas. Stating
`Keeps(Stmt, fun (found: List(String))(s: Stmt): List(String) => { … 14 cases … })` would repeat the checker's code
in the proof, so the steps became definitions: `Check.errorStep`, `literalStep`, `boxStep`, `launcherSizes`,
`u64Printed`, `gridExprs`, `sharedSize`, `staticArray`, `staticStep`, `sharedOffset`, `offsetStep`, `paramUses`
(now returning its step), `launcherNames`, and `printerName`'s parts `variableName` and `printerLocals` (a proof that
`printerName` holds must name the disjuncts it does not prove). Behaviour and
messages are unchanged, and the checker reads no worse.

A step that closes over a value (`bytes`) must be a definition returning a function,
`def staticStep (bytes: Nat): List(String) -> Stmt -> List(String) := fun …`, because a definition with one binder
group cannot be applied partially.

*Feature:* none needed for the checkers; for proofs about third-party code, a way to refer to a subterm of a
definition (a `simp`-style normal form in which the lemma statement is matched against the unfolded goal).

### F4. Every argument is explicit, message texts included

An implicit binder must be forced through constructor frames of a later explicit argument's type, and a hypothesis
`h: Eq(List(String), Check.exprFold(List(String), x, acc, f), List.nil(String))` has an application there, not a
constructor. So every lemma call spells out what `h`'s type already determines:

```raccoon
Fold.blockFoldAt(Stmt.error(m), k.body, occ, List.nil(String), Check.errorStep, Errors.keeps, walk)
Fold.unlessOk(List.nil(String), Nat.blt(offset, bytes), SharedMemory.offsetMessage(bytes, offset), here)
```

The second restates the checker's message text (`offsetMessage`), only to state `here`'s type; a wrong text is a
type mismatch, so this is brittle rather than unsound. Roughly half of each per-checker file is such restated
arguments. The accumulators are the worst: the proof must write the checker's intermediate results
(`Check.blockFold(List(String), k.body, size, Check.staticStep(bytes))`) to name the point it reasons about.

*Feature:* elaboration-time unification of implicit arguments against the types of later arguments
(higher-order pattern unification, as in Lean's `apply`), or tactics (`apply`, `exact`) that do it. This is in
tension with the "precise local typing" principle only if the expected type is consulted; here everything needed
is in the argument `h`, which is local.

### F5. No catch-all case

`match` has no `_` case, so each step's `Keeps` lemma is a 14-way (statement) or 15-way (expression) match whose
arms are all `h` but one or two, and the traversal lemmas repeat the same split:

```raccoon
match s returning Fold.Empty(found) with
| Stmt.decl t id init => h
| Stmt.declMut t id init => h
… 11 more …
| Stmt.error message => False.elim(Fold.consNotEmpty(message, found, h), Fold.Empty(found))
```

So far: `Errors.keeps` (14 arms, 13 trivial), `Literals.keeps` (15, 13), `SharedMemory.staticKeeps` (14, 13),
`SharedMemory.offsetKeeps` (15, 13), `Names.usesKeeps` (15, 13), `Fold.stmtFoldHere` (14, 10), `Fold.stmtExprsAcc` (14, 7),
`Fold.exprFoldHere` (15, 9).

*Feature:* a wildcard case, checked once per remaining constructor under its refinement; or a tactic combinator
(`cases s <;> first | exact h | …`).

### F6. A `struct` in `Prop` with a data field is rejected

A `struct` generates selectors, and a selector of a data field out of a proposition is a forbidden large
elimination, which is reported as an error on the declaration instead of the selector being left out:

```raccoon
struct ExprIn (x: Expr)(b: Block) : Prop
 | mk (s: Stmt)(stmt: InBlock(s, b))(own: OwnExpr(x, s)) : ExprIn(x, b)
// error: Cannot eliminate proposition Spec.ExprIn into non-Prop motive Cuda.Stmt (in definition Spec.ExprIn.s)
```

Written as a one-constructor `inductive`. *Feature:* generate no selector for such a field (as `_` fields get none).

### F7. A negation is a binder group of its own

`Not(P)` unfolds to the function type `(h: P) -> False`, so `(n: String) -> Not(P(n))` has two binder groups, and a
lambda written as one does not fit:

```raccoon
let once := fun (n: String)(twice: Spec.Twice(String, n, names)): False => …
// expected: (n: String) -> ((h: Spec.Twice(String, n, names)) -> False)
// actual:   (n: String) -> (twice: Spec.Twice(String, n, names)) -> False
fun (n: String): Not(Spec.Twice(String, n, names)) => fun (twice: Spec.Twice(String, n, names)): False => …   // accepted
```

The message is clear once one knows the rule; the rule itself (grouping is part of a type's identity) is the cost.
*Feature:* none for the kernel; an `intro`-style tactic would hide it.

### F9. Declaring an inductive whose field applies `Nat.mod` to a variable takes exponential time

```raccoon
struct S (t: Nat) : Prop
 | mk (h: Eq(Nat, Nat.mod(t, 20), 0)) : S(t)
```

checks in 13 s of CPU, and with modulus 32 did not finish in 100 s; moduli 12, 16 and 18 take 2.8, 4.1 and 6.2 s. The
same type as a definition's binder, or as the body of a `def … : Prop`, checks at once, and so does a `Type`-sorted
struct only slightly faster (modulus 20: 12.5 s). So `Spec.BarrierCounts` is a definition, and `Spec.NamedBarriers`
is an `And` of it and a struct, where the other invariants are structs with named fields. Whatever the family check
does to a field type (it looks like full normalization, under binders and into blocked matches, of `Nat.mod`'s body:
`Nat.sub(a, Nat.mul(Nat.div(a, b), b))` with `Nat.div` a fuelled recursion), it is exponential in the literal.

*Feature:* a kernel fix: check field types by weak-head normalization, or stop at native operations on neutral
arguments, as conversion does above the unfolding limit.

### F8. Small syntax and diagnostic traps

- A `decreases` clause must stay on the line of the result type; on a continuation line the error is
  `Failed to parse Sym(:=)`, pointing at the result type.
- Which family parameters a constructor takes explicitly depends on forcing by later fields, so
  `Spec.Mem.here(x, rest)` takes `x` and `Spec.Mem.there(y, rest, h)` does not; the arity error
  (`expected 2 params, got 3`) names neither binder.
- `False.elim(h, T)` must be given the goal `T` again (no expected type is consulted), and `Or.inl` and `Or.inr`
  must be given the other disjunct: `Or.inl(Eq(Bool, b, Bool.true), p)`, since nothing forces it.
- A lambda cannot appear in a type at all, a constructor field's or a binder's (a parse error at the `fun`), so
  `Spec.mapNames` and `Barriers.pairWith` are definitions.
- `open Check` inside a namespace that already opens `Cuda` fails at once (`launcher is ambiguous: Cuda.launcher,
  Check.launcher`), even if neither is used; `open Check.{Scan, NatSet}` works.
- A match cannot appear in a binder's type written inline (`(h: Eq(Bool, { match … }, Bool.true))` is a parse
  error), which is one reason the mirror definitions of F2 are definitions.

## Evaluation versus induction

None of the soundness theorems is "evaluate and compare": each quantifies over every kernel, and every kernel's
walk is a recursion over an open AST. What evaluation does inside them is small and local: a step applied to a
constructor reduces by conversion (`Check.literalStep(found, Expr.lit(v))` to `Check.u32Printed(…)`), and a Bool
condition converts to the spec's Prop. One step in I5 is a genuine evaluation: that a name spelled `gpu_` then
anything starts with `gpu_` is `Eq.refl(Bool.true)`, since `Check.startsWith` recurses on the literal prefix.
Proof by evaluation would help only where it does already, in discharging
`Check.WellFormed` of a concrete kernel at `render`.

The induction is all in `Fold.rac`, and it is the same induction eight times over (acc and at, for four traversal
shapes). A generic traversal (one fold over a "children" function, or a derived eliminator for the occurrence
relations) would make it one lemma pair.
