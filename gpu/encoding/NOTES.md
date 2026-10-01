# gpu/encoding: notes for review

Observations from building A1 (`Core.rac`'s attention sections, `examples/attention.rac`, `checks/emitted.rac`), for
the readability review and for quality-of-life work on Raccoon. Each says what was awkward and where.

## Readability and incidental complexity

1. **Sixteen straight-line calls per pass.** `PFree`'s chunk index is in its type, and `loadAcc8` and `storeP` take
   their chunk as a generation-time `Nat` with evidence (`fits`). The evidence is discharged only where the index is
   a literal, so no generation-time loop over chunks can call them, and `examples/attention.rac` spells out
   `maxChunk(…, 0, …)` to `maxChunk(…, 15, …)` in `pass1`, the same for `expChunk` in `pass2`, and `checks/emitted.rac`
   repeats it for `storeP`. A chunk combinator in the core (the `forChunks` of P: one step function over chunk `c`
   with `c < 16` in scope) would replace all three, but needs a way to pass the evidence along (§Raccoon 3).
2. **Done-token plumbing.** Seven protocols (three stage rings, the S ring, the exchange, the tensor-memory split and
   the allocation) each open a callback and each wants its `…Done` tokens back in a `Pair` beside the callback's own
   result. `examples/attention.rac` needs `AllDone`, nested in the order the scopes close, the re-shuffle at the end
   of `roles`, and a `kernel` of 40 lines of nested callbacks whose result types restate that nesting
   (`Pair(Attn.RingDone(rk), Pair(Attn.RingDone(rq), Pair(Attn.ExDone(x), Attn.AccDone(q))))` and so on). The
   explicit result types are required (`DESIGN.md` §1), so most of the kernel's text is types.
3. **Peeled iterations duplicated.** The first iteration changes `OState` (`fresh` to `held`), so `loopPeeled`'s
   `first` and `rest` are two closures that differ in one call each: `mmaPVFirst`/`mmaPVNext` in `issuer`, and the
   rescale and the start of the maximum in `softmax`. Both copies have to be kept in step by hand.
4. **No way to name a value.** A `Val` is an expression, printed wherever it is used, and there is no public `let`:
   the only ways to make the code compute a value once are a register (`reg`, `set`, `get`) or an instruction that
   declares its result (`ex2`, `fconst`, …). So the running maximum and the sum are registers with a `get` and a `set`
   per chunk (`maxChunk`, `expChunk`), where a value would do, and the row maximum is materialized with a `get` before
   pass 2 uses it 128 times. A Key-free `bind` (declare a constant from a `Val`) would be sound (a `Val` carries no
   authority) and remove these registers.
5. **A `branch` for one optional step.** Issuing S_{j+1} only when `j + 1 < blocks` (`nextScores` in `issuer`) needs a
   `branch` whose state is the whole score-issuing state (`Scores`, with `fixedScores` built from three `fixed…`) and an
   empty `no` arm with the full closure type.
6. **Redundant fences in pass 1 and pass 2.** `loadAcc8` fences `after_thread_sync` before every load, as the GEMM's
   `stageChunk` does, although every thread holding `AccFull` waited and fenced itself in `awaitAcc` (`Core.rac`,
   `loadAcc8`): 32 fences per key block where one would do. Kept for M9's "whoever observed it" until the review
   settles whether `AccFull` can reach a thread that did not wait.
7. **`tmemBase` special-cases offset 0** (`Core.rac`, `tmemBase`) so that the GEMMs' generated code stays byte-identical
   to `gpu/Gpu.rac`'s (`(v0 + 0u)` would otherwise appear in every MMA). `offsetBy`/`boxAt` do the same for box and
   column offsets.
8. **Fixed shapes in types.** `mmaScores` takes `AccRing(q, 128)` and checks both rings' boxes at generation; the
   exchange's layout (Ô at +0, P at +128) and `Tmem(a, 256)` are fixed in `withExchange`; `storeO` takes
   `AttnOut(L, DType.f32)` only, although `AttnOut` has a type parameter (A2's bf16 output).
9. **Two rings of one type.** The K and V rings are both `Ring(r, RingCfg.mk(2, box, box))`; nothing tells K's data
   from V's (`ATTENTION.md` §5 "the wrong data in a ring"). The example names them `kRing` and `vRing` only.
10. **The first block's statistics.** `softmax` starts the first block's maximum at −∞ (`fconst` of its bits) and sums
    the first block straight into `l`, while later blocks sum into a fresh register and combine with `fma`; the two
    closures differ in these details as well as in the rescale (item 3).

## Raccoon limitations and bugs met

1. **Parse trap: `decreases` on a continuation line.** A declaration whose `decreases` clause starts a new line fails
   with "Failed to parse Sym(:=)", pointing at the end of the previous line. Worked around by keeping the signature and
   `decreases` on one line (`Core.mmaBoxes`). Reproducer:
   ```raccoon
   def f (n: Nat): Nat
       decreases structural(n) := {
     match n returning Nat with
     | Nat.zero => 0
     | Nat.succ m => f(m)
   }
   ```
2. **`Bool.cond` is strict, so recursion through it is exponential.** Both branches are evaluated before the choice,
   so a structurally recursive function whose recursive calls are `Bool.cond`'s arguments doubles its work per step.
   The first version of `checks/emitted.rac`'s line splitter did not finish in minutes; with `match` on the
   condition it is linear. Reproducer (with `--prelude gpu/Prelude.rac`, for `Nat.mod`): 4.2 s at 20, 16.9 s at 22.
   ```raccoon
   def evens (n: Nat): Nat decreases structural(n) := {
     match n returning Nat with
     | Nat.zero => 0
     | Nat.succ m => Bool.cond(Nat.isZero(Nat.mod(m, 2)), Nat, Nat.succ(evens(m)), evens(m))
   }
   { evens(22) }
   ```
   A lazy `Bool.cond` (or a warning on a recursive call in an argument of it) would remove the trap.
3. **No dependent `if` for evidence.** Evidence (`[fits: Nat.lt(c, 16)]`) is discharged by evaluation only where the
   index is concrete, and a function generic in `c` must take the evidence itself and forward it. There is no idiom
   for producing `Nat.lt(Nat.succ(c), 16)` inside a generation-time recursion over `c` (`OBLIGATIONS.md` §9.5 notes the
   same gap for `render`), which is why the chunk calls are written out (§1 above).
4. **`List.reverse` is quadratic** (`gpu/Prelude.rac`: `append(reverse(tail), [head])`). Splitting the 43 KB rendered
   kernel into lines with it took 14 s of checking; with an accumulating reverse (`E.revOnto` in
   `checks/emitted.rac`), 1 s. The core's own uses reverse lists of at most a few dozen statements.
5. **Unknown qualified names report "Type is not a type".** With the bundled prelude, which has no `Nat.mod`:
   ```raccoon
   { Nat.isZero(Nat.mod(5, 2)) }
   ```
   reports `error: Type is not a type` at `Nat.mod`, not that the name is unknown.
6. **Constructor arity errors do not say which parameters are implicit.** `F32x8.mk(l, Grain.thread, v0, …, v7)`
   reports "Cannot apply function - expected 8 params, got 10": a struct constructor takes the family's parameters
   implicitly when its fields determine them (`F32x8.mk(v0, …)`, `AttnLaunch.mk(…)`), and explicitly otherwise
   (`Val.mk(l, u, t, …)`, `HeadMap.mk(l, spec, …)`). The message could name the implicit ones.

## Timing

CPU time of the native binary (`target/graalvm/raccoon`), on an idle machine, 2026-10-01:

| What | CPU s |
|---|---|
| checking `Core.rac` with `Check`, `Cuda`, `Text` (an empty file importing `encoding.Core`) | 0.3 |
| `gen.sh encoding/examples/tinygemm.rac` | 0.9 |
| checking `examples/attention.rac` without its final expression | 2.7 |
| `gen.sh encoding/examples/attention.rac` (checking, generation, the certificate, printing) | 7.9 |
| checking `checks/emitted.rac` | 2.6 |
| `gpu/check.sh`, everything | 48 (40 wall) |

The generated attention kernel is 2726 lines (185 KB) with its launcher: the two softmax iterations (peeled and
looped) unroll 16 chunks per pass and 16 per rescale, and every tensor-memory address repeats the warp-quadrant
expression.
