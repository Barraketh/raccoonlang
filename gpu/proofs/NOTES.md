# Soundness proofs of the structural checkers: notes

Layer 1 of `gpu/OBLIGATIONS.md` §8, second half: each checker of `gpu/Check.rac` proved sound against a short
syntactic statement of its invariant in `gpu/Spec.rac`. This file records what was proved and, as evidence for the
design of proof automation, what made the proofs hard in Raccoon as it is today. It was written as the proofs were.

Line counts are of the files as committed, comments included.

## Status

| Checker | Spec (`Spec.rac`) | Proof | Lines | Status |
|---|---|---|---|---|
| (shared) | occurrence relations, 95 lines | `Fold.rac`: the traversal lemmas | 371 | done |
| `errors` | `NoErrors` | `Errors.rac` | 32 | proved |
| I4 `literals` | `Literals`, `Lit32`, `Lit64` | `Literals.rac` | 108 | proved |
| I2 `sharedMemory` | `SharedMemory`, `SharedAt` | `SharedMemory.rac` | 111 | proved |

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

*Feature:* a `match e as b with (h: Eq(Bool, e, b))` form (Agda's `with … in`, Lean's `match h : e with`) that
abstracts `e` in the goal and in the hypotheses and hands the branch the equation.

### F3. Proofs cannot name what a checker leaves anonymous

A lemma about a checker's step must name the step, but the checkers folded with inline lambdas. Stating
`Keeps(Stmt, fun (found: List(String))(s: Stmt): List(String) => { … 14 cases … })` would repeat the checker's code
in the proof, so the steps became definitions: `Check.errorStep`, `literalStep`, `boxStep`, `launcherSizes`,
`u64Printed`, `gridExprs`, `sharedSize`, `staticArray`, `staticStep`, `sharedOffset`, `offsetStep`. Behaviour and
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
`SharedMemory.offsetKeeps` (15, 13), `Fold.stmtFoldHere` (14, 10), `Fold.stmtExprsAcc` (14, 7),
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

### F7. Small syntax and diagnostic traps

- A `decreases` clause must stay on the line of the result type; on a continuation line the error is
  `Failed to parse Sym(:=)`, pointing at the result type.
- Which family parameters a constructor takes explicitly depends on forcing by later fields, so
  `Spec.Mem.here(x, rest)` takes `x` and `Spec.Mem.there(y, rest, h)` does not; the arity error
  (`expected 2 params, got 3`) names neither binder.
- `False.elim(h, T)` must be given the goal `T` again (no expected type is consulted).

## Evaluation versus induction

None of the soundness theorems is "evaluate and compare": each quantifies over every kernel, and every kernel's
walk is a recursion over an open AST. What evaluation does inside them is small and local: a step applied to a
constructor reduces by conversion (`Check.literalStep(found, Expr.lit(v))` to `Check.u32Printed(…)`), and a Bool
condition converts to the spec's Prop. Proof by evaluation would help only where it does already, in discharging
`Check.WellFormed` of a concrete kernel at `render`.

The induction is all in `Fold.rac`, and it is the same induction eight times over (acc and at, for four traversal
shapes). A generic traversal (one fold over a "children" function, or a derived eliminator for the occurrence
relations) would make it one lemma pair.
