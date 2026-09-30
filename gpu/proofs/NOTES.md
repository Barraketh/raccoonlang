# Soundness proofs of the structural checkers: notes

Layer 1 of `gpu/OBLIGATIONS.md` §8, second half: each checker of `gpu/Check.rac` proved sound, in Raccoon, against a
short syntactic statement of its invariant in `gpu/Spec.rac`. This file records what was proved and, as evidence
for the design of proof automation, what made the proofs hard in Raccoon as it is today. It was written as the
proofs were.

Line counts are of the files as committed, comments and blank lines included.

## Status

Every checker is proved sound for every kernel, `Eq(List(String), Check.x(k), List.nil(String)) -> Spec.X(k)`, and
the whole certificate, `WellFormed.sound: Check.WellFormed(k) -> Spec.WellFormed(k)`.

| Checker | Spec (`Spec.rac`) | Proof | Lines |
|---|---|---|---|
| (shared) | occurrence relations and program order, 120 lines | `Fold.rac`: the traversal lemmas | 450 |
| (shared) | | `Lib.rac`: Bool, Nat, List and string facts | 188 |
| (shared) | | `NatSet.rac`: `Check.NatSet` is a set | 148 |
| `errors` | `NoErrors`, 5 lines | `Errors.rac` | 32 |
| I1 `scoping` | `Scoping`, `StmtScope`, `BlockScope`, `declaredBy`, `Uses`, `Binds`, `DeviceOnly`, 72 lines | `Scoping.rac` | 517 |
| I2 `sharedMemory` | `SharedMemory`, `SharedAt`, 18 lines | `SharedMemory.rac` | 109 |
| I3 `namedBarriers` | `NamedBarriers`, `BarrierIds`, `BarrierCounts`, `Barrier`, `LiteralOperands`, 31 lines | `Barriers.rac` | 274 |
| I4 `literals` | `Literals`, `Lit32`, `Lit64`, 25 lines | `Literals.rac` | 109 |
| I5 `names` | `Names`, `Chosen`, `CIdent`, `PrinterName`, `Declared`, `Twice`, …, 61 lines | `Names.rac` | 271 |
| I6 `launcher` | `LauncherOk`, `Launched`, `NotMap`, 20 lines | `Launcher.rac` | 317 |
| certificate | `WellFormed`, 7 lines | `WellFormed.rac` | 21 |
| **total** | 370 | | 2436 |

Check time. Each proof file checks in 1.4 to 2.3 s of wall time, most of it loading `Check.rac` (a file that loads
only the prelude takes 0.8 s); `WellFormed.rac`, which loads every proof, takes 2.3 s. `check.sh` gains the 11 files
of `proofs/` (63 ok). The checker restructurings below cost the persistent GEMM about 0.06 s of its 3.25 s of
generation (six alternating runs of each: 3.25 s against 3.31 s wall, 7.46 s against 7.51 s CPU); the four
generated kernels are byte-identical to those before.

## The shape of every proof

Every checker is a walk that collects messages, and every statement in `Spec.rac` is a universal over an occurrence
relation (`InBlock`, `ExprIn`, `HostExpr`, `Mem`, `Before`, …). The proofs share one argument, in `Fold.rac`:

1. **Keeps.** The checker's step never removes a message: `Fold.Keeps(A, f)`, that `f(found, x)` empty implies `found`
   empty. Proved per step, by cases on the statement or expression.
2. **Acc.** A walk that ends empty started empty (`foldlAcc`, `exprFoldAcc`, `stmtExprsAcc`, `blockFoldAcc`,
   `blockExprsAcc`, `hostExprsAcc`), by structural recursion on the data walked.
3. **At.** A walk that ends empty found nothing at each thing it visits: `f(nil, x)` is empty for every `x` the
   occurrence relation reaches (`foldlAt`, `exprFoldAt`, `stmtExprsAt`, `blockFoldAt`, `blockExprsAt`,
   `launcherExprsAt`, `hostExprsAt`), by recursion on the data, matching the occurrence proof.
4. **The step's condition.** `Check.unless(found, ok, message)` empty means `ok` is `Bool.true` (`unlessOk`), and a
   Bool condition is the Prop the spec states, by conversion (`Nat.lt` is `Eq(Bool, Nat.ble(…), Bool.true)`) or by a
   reflection lemma (`Lib.rac`).

That covers errors, I2, I4 and I5 outright. I3 and I1 carry a set of ids through the walk, and need their own
induction on top (F11).

## Per invariant

**errors.** Spec: `(m: String) -> InBlock(Stmt.error(m), k.body) -> False`. The proof is `Fold.blockFoldAt` applied
to a 14-case `Keeps` lemma for the step; no lemma of its own.

**I1, scoping.** Spec: `BlockScope(x, visible, [], k.body)` relates each statement `x` of the body to the variables
in scope where it stands: a block extends the scope of the rest of it by what a statement declares (`declaredBy`: a
declaration's or a shared array's id), and a loop's body has the loop's variable; every variable `x` `Uses` (in an
expression it holds itself, or as an assignment's target) is in `visible`. No two statements, one `Before` the other
in program order, `Binds` one id (declarations, shared arrays and loop variables). No expression the launcher
evaluates is `DeviceOnly` (a variable, a thread index, an array element, the shared buffer).

The proof carries `Within(v, vars)`, that the checker's set `v` of visible variables holds only variables of the
spec's scope; `NatSets.fromInsert` keeps it across a declaration and a loop. That gives the uses (`stmtInScope`,
`blockInScope`, a mutual recursion over the occurrence proof). Distinctness is the barrier argument over a tree:
`seen` only grows (`stmtSeen`, `blockSeen`), what a statement binds is fresh when it is declared (`bindsFresh`) and
seen after it (`seenAfterStmt`, `seenAfterBlock`), and a statement does not bind what was seen before it
(`freshStmt`, `freshBlock`); two places in program order are split along `Spec.statements`' appends (`memSplit`,
`beforeSplit`, `blockCases`). Most of the 517 lines are these mutual recursions, and those that reach into a
statement's blocks split on the statement (14 arms, 10 of which say "no blocks").

The checker's use of a variable goes through `unless` (`useVar`, its message named `unscoped`); its expression walk
became a `List(String)` fold (`useStep`, closing over the `seen` set, which the walk of one statement's expressions
never changes), so `Fold`'s lemmas apply; a declaration takes whether its id was seen as an argument (`declared`);
the launcher's step is `hostUse`.

**I2, shared memory.** Spec: `Nat.le(k.dynamicShared, 232448)`; a positive size means `k.launcher` is not `none`;
a `Stmt.shared` anywhere in the body means the size is 0; every `sharedAddr`/`sharedPtr` offset is below the size.
Two small Bool/Nat facts (`orNot`, `notPositive`).

**I3, named barriers.** Spec: every `bar.sync` in the body (an asm statement with its template) has
`LiteralOperands` (no outputs, two `lit` inputs); every `Barrier(id, threads, s)` in the body has `id` in 1..15 and
`threads` positive with `Nat.mod(threads, 32) = 0`; and no two barriers, one `Before` the other in
`Spec.statements(k.body)` (every statement at any depth, in program order), have one id. Distinctness needs places,
which `InBlock` does not have (two identical `bar.sync 1, 64` are one statement to it), hence the flattening. The
proof first turns the checker's `blockFold` into a `List.foldl` over `Spec.statements` (`Fold.blockFusion`, generic in
the walk's state), then reasons about a flat walk: ids seen stay seen (`stepSeen`), a barrier's id was not seen before
it (`barrierFresh`), and an id is seen after its barrier (`NatSets.inserted`). The literal operands come from a case
split on the operand lists and on `Check.literal` of each (`shape`, `twoLiterals`, `literalSome`), which is the only
place the proof inspects expressions. The checker's step was named (`barrierStep`), and the decisions it matched on
became arguments of `barrierAt` (`isBarrier`, `args`), so the lemmas case on variables (F2).

**I4, literals.** Spec: every `n` that `Lit32(k, n)` (a `lit` in the body or the launcher's expressions, the block
size, a box dimension) is `Nat.lt(n, Cuda.u32Limit)`, and every `Lit64` below 2^64. Needed F1's checker change.

**I5, names.** Spec: the kernel's name is `Chosen` (a `CIdent`, a letter or `_` then letters, digits and `_`, and
not a `PrinterName`: `v` and digits, `gpu_…`, or one of the launcher's locals); the parameters' names are
`Declared` (each chosen, none the kernel's name, none `Twice` in the list); every `param`/`paramAddr` in the body
names one of them; and likewise for the launcher, whose declared names are its parameters' then its maps' and whose
expressions name only its parameters. This is the first proof that needs both directions of a Bool test: soundness
for what the checker accepts (`isIdent` true gives `CIdent`), and completeness for what it rejects (a `PrinterName`
makes `printerName` true, so its `Bool.not` being true is a contradiction). Hence `Lib.rac`.

`Check.declaredNames` folded a `Prod(List(String), List(String))` of the names so far and the messages over the
names with `List.foldl`. It became a direct recursion, `declaredAfter`, whose `before` is an argument: the lemmas
(`declaredChosen`, `declaredFresh`, `declaredOnce`) then recurse on the names with `before` growing, which is the
whole induction. The fold was not attempted, since `Fold`'s lemmas are for a `List(String)` accumulator and a pair
would have needed its own `Keeps`, `Acc` and an invariant relating the first component to the prefix walked.

**I6, the launcher.** Spec: for a kernel with launcher `l`, every parameter of the kernel that is `NotMap` is a `Mem`
of `l.params` (the same constructor, element type and name); every `tensorMap(name)` of the kernel is among the
encodings' names and not `Twice` there; and every encoding names a `tensorMap` of the kernel and reads
`input(bf16, source)`, `scalar(u32, rows)` and `scalar(u32, cols)` of the launcher. Its size is in Bool reflection:
`Check.sameParam` sound (a 4 × 4 case split, 12 arms impossible), `Check.sameType` sound (through an inverse of
`typeIndex`, which saves a 5 × 5 split), `Check.declares` sound, and `Check.count` against `Mem` and `Twice` (lower
bounds with `Nat.ble`, since `count = 1` is what the checker tests). `Check.count` was a `List.foldl` with a `Nat`
accumulator; it became a direct recursion, so the bounds are proved by induction on the maps without a lemma relating
the accumulator to the prefix walked.

**The certificate.** `Spec.WellFormed(k)` is the conjunction of the seven statements, and `WellFormed.sound` takes
`Check.Clean` apart and applies the seven theorems. It is a conjunction rather than a structure with named fields
because of F9.

**`Check.NatSet`.** The trie branched on `Nat.isZero(Nat.mod(m, 2))` and recursed on `Nat.div(m, 2)`, and a node held
a Bool. Its soundness (a member was inserted) then rests on distinct numbers having distinct paths, which is
arithmetic about the prelude's `Nat.div` (a `divFuel` recursion) and `Nat.mod` (`a - (a / b) * b`) that no library
provides, and a proof by recursion must case-split on two computed parities at once (the member's and the inserted
number's), which F2 makes painful: each would need a mirror definition and an `Eq.subst` along the parity's
equation. (This was judged from the code; that version was not attempted.) It became a trie that follows a
precomputed path (`NatSet.path(n)`, a `List(Bool)`) and whose node lists the numbers inserted at it. Membership
compares numbers at the end of the path, so no fact about paths is needed, and every case split is on a path's
head, a variable. `NatSet.rac` proves the three facts the checkers need (`inserted`, `kept`, `fromInsert`) in 148
lines of plain structural recursion. This is the restructuring that changed the difficulty most: from arithmetic no
library provides to a textbook induction.

## Lemmas a standard library would provide

Written here because Raccoon's prelude has none of them:

- **List membership** as an inductive predicate (`Spec.Mem`), and its algebra: `Mem` of `List.append` left and
  right (`Fold.memAppendLeft`, `memAppendRight`), and the converse split (`Scoping.memSplit`); two places in a list
  (`Spec.Twice`, `Spec.Before`) and their split over an append (`Scoping.beforeSplit`).
- **`List.foldl` with a non-shrinking step**: emptiness propagates backwards (`foldlAcc`), and to each element
  (`foldlAt`); `List.foldl` over `List.append` (`Fold.foldlAppend`). The same lemmas again for each of the AST's own
  folds (`exprFold`, `stmtFold`/`blockFold`), and fold fusion for the AST (`Fold.stmtFusion`, `blockFusion`).
- **Reverse**: `revOnto(xs, acc)` empty implies both empty (`revOntoAcc`, `inOrder`).
- **Constructor disjointness and injectivity** as named lemmas: `cons ≠ nil` (`consNotEmpty`), `some ≠ none`
  (`SharedMemory.someNotNone`, `Barriers.noneNotSome`), `Option.some` injective (`Barriers.someInj`, copied from the
  prelude's `Nat.succInj` idiom). The prelude has `Bool.falseNeTrue`, `Nat.succNeZero`, and nothing for `List` or
  `Option`.
- **Congruence of a two-argument constructor** (`Lib.consEq`, `Launch.paramEq`): the prelude's `congrArg` takes one
  argument.
- **Bool reflection** (`Lib.rac`): `Bool.and` and `Bool.or` introduction and elimination into `Eq(Bool, …, true)` and
  `Or` (`andLeft`, `andRight`, `andIntro`, `orCases`, `orLeft`, `orRight`, `notBoth`, `SharedMemory.orNot`);
  `Nat.isZero` sound (`Barriers.isZeroSound`); `Nat.beq` sound and reflexive (`beqSound`, `beqRefl`); `List.all`
  sound and complete (`allMem`, `allIntro`); string equality (`Check.sameChars`, `Check.same`) sound and reflexive;
  `List.any` of an equality (`Check.mentions`, `Check.declares`) sound and complete. `Char` and `String` equality
  from their fields is `congrArg(h, Char, Char.mk)`, which structure eta makes a proof about `c`.
- **Nat order facts**: `Bool.not(Nat.blt(0, n)) = true` gives `n = 0` (`SharedMemory.notPositive`); `Nat.ble` is
  monotone in its second argument (`Launch.bleSucc`).
- **`Eq` transport**: never needed as a lemma, since matching an equation proof rewrites the goal and every
  hypothesis (P1); `Eq.subst` with an explicit motive where one side is not a variable (`Barriers.sound`,
  `Launch.launched`).

## Findings

Each finding has a minimal example and a guess at the feature that would remove it. P-findings are things that
worked better than expected.

The five that cost the most, in order: F4 (every argument explicit, messages included), F2 (no `inspect`), F5 (no
catch-all case), F11 (walks with state need their own induction) and F1 with F9 (native `Nat` operations, which made
one invariant unprovable as the checker was written and one specification take exponential time to check).

### P1. Matching a variable refines every hypothesis, and matching `Eq.refl` rewrites

Matching on a variable (or a projection of a struct-typed variable, such as `k.launcher`) refines the motive and the
types of all hypotheses in scope, Agda style. No convoy pattern is needed, and `match e returning … with | Eq.refl z
=> h` transports `h` along `e` when a side of `e` is a variable (used for most rewrites in these proofs):

```raccoon
def unlessOk (found: List(String))(ok: Bool)(message: Unit -> String)
    (h: Eq(List(String), Check.unless(found, ok, message), List.nil(String))): Eq(Bool, ok, Bool.true) := {
  match ok returning Eq(Bool, ok, Bool.true) with
  | Bool.true => Eq.refl(Bool.true)
  | Bool.false => False.elim(Fold.consNotEmpty(message(Unit.unit), found, h), Eq(Bool, Bool.false, Bool.true))
}
```

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

### P3. A `let` can name a `returning` motive

`let goal := Eq(Expr, x, Expr.lit(n))` then `match x returning goal with` refines `goal` in each branch like a written
motive. Found late: `NatSet.rac` still restates its motives (up to 130 characters) in each of its nested matches.

### F1. A native Nat operation on a variable and a large literal hides its definition

`Nat.lt(n, m)` is `Eq(Bool, Nat.ble(Nat.succ(n), m), Bool.true)`, and `Nat.blt(n, m)` is defined as
`Nat.ble(Nat.succ(n), m)`. But `blt` is native, and applied to a variable and a literal above the unfolding limit
(2^8) it is a neutral headed by `blt` that never unfolds (`docs/kernel.md`, natural numbers). So:

```raccoon
def f (n: Nat)(h: Eq(Bool, Nat.blt(n, 4294967296), Bool.true)): Nat.lt(n, 4294967296) := h
// type mismatch: Nat.ble(Nat.succ(n), 4294967296) vs Nat.blt(n, 4294967296) (not reducible: stuck)
```

No propositional route was found either: induction on `n` meets `Nat.blt(Nat.succ(m), 4294967296)`, which is as
stuck, and nothing else relates the two neutrals. The checker compared literals with `Nat.blt(n, Cuda.u32Limit)`,
so the spec's `Nat.lt` could not be reached from it. Worked around by a checker change: `Check.below(n, limit)` is
`Nat.ble(Nat.succ(n), limit)`, which is `Nat.lt`'s own form. With no literal above the limit (`Nat.blt(offset,
bytes)`, both variables) the body unfolds and nothing is lost.

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

(The match arms are on separate lines in real code; see F8.) Every decision a proof must case on has to reach it as
a variable. `Check.unless(found, ok, message)` does that by taking the decision as an argument, which is why most of
these proofs are easy: `unlessOk` is stated over a variable `ok` and applied to the checker's expression. Where a
checker matched a computed value itself, it was restructured to take it as an argument (`Check.barrierAt`,
`Check.declared`, `Check.useVar`), or a lemma was stated over a Bool variable and applied to the expression
(`SharedMemory.orNot`, `notPositive`, `Launch.countCases`).

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

It costs a definition and two lemmas per such match, and the proof must copy the checker's branches exactly. It
does not help when two functions match the same computed value and the proof needs both to agree (the old
`NatSet`'s `member` and `insert` on one number's parity): the lemma over a variable loses the link to the other
function's match.

*Feature:* a `match e as b with (h: Eq(Bool, e, b))` form (Agda's `with … in`, Lean's `match h : e with`) that
abstracts `e` in the goal and in the hypotheses and hands the branch the equation.

### F3. Proofs cannot name what a checker leaves anonymous

A lemma about a checker's step must name the step, but the checkers folded with inline lambdas. Stating
`Keeps(Stmt, fun (found: List(String))(s: Stmt): List(String) => { … 14 cases … })` would repeat the checker's code
in the proof, so the steps became definitions: `errorStep`, `literalStep`, `boxStep`, `launcherSizes`, `u64Printed`,
`gridExprs`, `sharedSize`, `staticArray`, `staticStep`, `sharedOffset`, `offsetStep`, `paramUses` (now returning
its step), `launcherNames`, `barrierStep`, `passedStep`, `encodingStep`, `mapParams`, `useStep`, `hostUse`,
`unscoped`, and `printerName`'s parts `variableName` and `printerLocals` (a proof that `printerName` holds must name
the disjuncts it does not prove). Behaviour and messages are unchanged, and the checker reads no worse.

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

The second restates the checker's message text (`offsetMessage`), only to state `here`'s type; a wrong text is a type
mismatch, so this is brittle rather than unsound. Each per-checker file restates the checker's messages for this
alone: `Names` 5 message definitions, `Launch` 6, `Barriers` 3 and one text twice inline, `SharedMemory` 2 and 2
inline, `Literals` 2 texts in 4 lemmas, `Scoping` 5 texts in 12 places. The accumulators are as bad: the proof must
write the checker's intermediate results (`Check.blockFold(List(String), k.body, size, Check.staticStep(bytes))`,
`Scoping.used(v, s, st)`) to name the point it reasons about, and most `let`s in the proofs exist to name them.

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

Arms (trivial ones) per such match: `Errors.keeps` 14 (13), `Literals.keeps` 15 (13), `SharedMemory.staticKeeps` 14
(13), `SharedMemory.offsetKeeps` 15 (13), `Names.usesKeeps` 15 (13), `Barriers.stepFound` 14 (13),
`Barriers.stepSeen` 14 (13), `Barriers.literalSome` 15 (14 impossible), `Scoping.useKeeps` 15 (14),
`Scoping.hostKeeps` 15 (10), `Scoping.withinAfter` 14 (10), `Scoping.seenAfterStmt`, `freshStmt` and
`distinctStmt` 14 (10 "no blocks" each), `Fold.stmtFoldHere` 14 (10), `Fold.stmtFusion` 14 (10),
`Fold.stmtExprsAcc` 14 (6), `Fold.exprFoldHere` 15 (9), `Launch.sameParamSound` 16 (12 impossible); in the spec,
`Spec.inner` and `Spec.declaredBy` 14 (10).

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

The same rule makes `notMap(n)(e)` the application of a `Spec.NotMap(p)`, not `notMap(n, e)`, and made a lemma
returning `(id: Nat) -> Uses(id, x) -> Mem(…)` unfit for a field whose type chains all five binders; the fix is a
lambda that applies it, `blockInScope(…)(id, use)`. The messages are clear once one knows the rule; the rule itself
(grouping is part of a type's identity) is the cost. *Feature:* none for the kernel; an `intro`-style tactic would
hide it.

### F8. Small syntax and diagnostic traps

- A `decreases` clause must stay on the line of the result type; on a continuation line the error is
  `Failed to parse Sym(:=)`, pointing at the result type.
- Which family parameters a constructor takes explicitly depends on forcing by later fields, so
  `Spec.Mem.here(x, rest)` takes `x` and `Spec.Mem.there(y, rest, h)` does not (likewise `Spec.Before.here(x, rest,
  later)`, and `Spec.LauncherNames.mk(l, …)` without its `kernel`); the arity error (`expected 2 params, got 3`)
  names neither binder.
- `False.elim(h, T)` must be given the goal `T` again (no expected type is consulted), and `Or.inl` and `Or.inr`
  must be given the other disjunct: `Or.inl(Eq(Bool, b, Bool.true), p)`, since nothing forces it.
- A lambda cannot appear in a type at all, a constructor field's or a binder's (a parse error at the `fun`), so
  `Spec.mapNames` and `Barriers.pairWith` are definitions. Nor can a match (`(h: Eq(Bool, { match … }, …))` is a
  parse error), which is one reason the mirror definitions of F2 are definitions.
- The cases of a match must be on lines of their own, so an impossible case cannot be closed inline:
  `| Expr.var id => { match h returning … with }` is a parse error, and `Barriers.noneNotSome` exists to say it.
- `open Check` inside a namespace that already opens `Cuda` fails at once (`launcher is ambiguous: Cuda.launcher,
  Check.launcher`), even if neither is used; `open Check.{Scan, NatSet}` works.
- A proof module about launchers cannot be `namespace Launcher`: inside it, `Launcher` resolves to the namespace
  before the opened `Cuda.Launcher`, and a binder `(l: Launcher)` is `Launcher not found`; it is `Launch`. `indices`
  and `scope` are keywords, so `let indices := …` (`Failed to parse pattern`) and a parameter `(scope: …)`
  (`Failed to parse Sym(:)`) are parse errors.

### F9. Declaring an inductive whose field applies `Nat.mod` to a variable takes exponential time

```raccoon
struct S (t: Nat) : Prop
 | mk (h: Eq(Nat, Nat.mod(t, 20), 0)) : S(t)
```

checks in 13.3 s of CPU; moduli 12, 14, 16 and 18 take 2.8, 3.4, 4.1 and 6.2 s (a file with no such declaration takes
about 2 s), and with modulus 32 it did not finish in 60 s. The same type as a definition's binder, or as the body of
a `def … : Prop`, checks at once; a `Type`-sorted struct is as slow (modulus 20: 12.5 s), and so is a field whose type
is a definition that unfolds to it. `Spec.NamedBarriers` states "a multiple of 32", so `Spec.BarrierCounts` is a
definition and `Spec.NamedBarriers` an `And` of it and a struct; and `Spec.WellFormed`, a struct holding
`Spec.NamedBarriers`, did not check in 120 s, so it is a conjunction too. Whatever the family check does to a field
type (it looks like full normalization, under binders and into blocked matches, of `Nat.mod`'s body:
`Nat.sub(a, Nat.mul(Nat.div(a, b), b))` with `Nat.div` a fuelled recursion), it is exponential in the literal.

*Feature:* a kernel fix: check field types by weak-head normalization, or stop at native operations on neutral
arguments, as conversion does above the unfolding limit.

### F10. One diagnostic per definition hides the rest

When several arms of one definition are wrong, only one is reported:

```raccoon
def t (b: Bool): Nat := {
  match b returning Nat with
  | Bool.true => Bool.true      // not reported
  | Bool.false => Bool.false    // TypeMismatch, the only diagnostic of `t`
}
```

Fixing it reveals the next, one check run at a time. *Feature:* report each failing arm.

### F11. Walks with state need their own induction

The checkers that carry state beyond a list of messages (`namedBarriers`' seen ids, `scoping`'s visible and seen
sets) fit `Fold`'s lemmas only in part. For I3 a fusion lemma turned the walk into a list fold; for I1 the visible
set changes with the block structure, so the walk is not a fold over program order, and eight mutual recursions
(`ownFound`/`blockAcc`, `stmtSeen`/`blockSeen`, `stmtInScope`/`blockInScope`, `seenAfterStmt`/`seenAfterBlock`,
`freshStmt`/`freshBlock`, `distinctStmt`/`distinctBlock`) restate the traversal. The distinctness half of I1 is the I3
argument again, over a tree instead of a list.

*Feature:* a derived induction principle for a walk (Coq's functional induction, Lean's `fun_induction`), which
would give each lemma the checker's own case structure; or a generic "state-threading traversal" with its lemmas
proved once.

## Evaluation versus induction

None of the soundness theorems is "evaluate and compare": each quantifies over every kernel, and every kernel's
walk is a recursion over an open AST. Evaluation inside them is local and small:

- a step applied to a constructor reduces by conversion (`Check.literalStep(found, Expr.lit(v))` to
  `Check.u32Printed(…)`), and a Bool condition converts to the spec's Prop;
- a few steps are genuine evaluations of closed terms: that a name spelled `gpu_` then anything starts with `gpu_`
  (`Eq.refl(Bool.true)`, since `Check.startsWith` recurses on the literal prefix); that `Spec.barrierTemplate` is
  `Check.same` as `Check.barrierTemplate` and `Check.barrierArgs` of two literal operands is their pair (both reduce
  inside `Barriers.atBarrier`); and that `Spec.printerLocals` is `Check.printerLocals`.

The induction is everywhere else: the traversals (`Fold.rac`, the same two lemmas for each of four traversal shapes),
the sets (`NatSet.rac`), the Bool reflection (`Lib.rac`, `Launcher.rac`), the name lists (`Names.rac`), and the
walks with state (`Barriers.rac`, `Scoping.rac`). Proof by evaluation would help only where it does already, in
discharging `Check.WellFormed` of a concrete kernel at `render`. A generic traversal (one fold over a "children"
function, or a derived eliminator for the occurrence relations) would make `Fold.rac` one lemma pair.
