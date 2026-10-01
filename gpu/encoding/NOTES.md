# gpu/encoding: notes for review

Observations from building A1 (`Core.rac`'s attention sections, `examples/attention.rac`, `checks/emitted.rac`), for
the readability review and for quality-of-life work on Raccoon. Each says what was awkward and where. Items marked
*(removed)* are gone since the readability refactor (§"Readability refactor" at the end).

## Readability and incidental complexity

1. *(removed)* **Sixteen straight-line calls per pass.** `PFree`'s chunk index is in its type, and `loadAcc8` and `storeP` take
   their chunk as a generation-time `Nat` with evidence (`fits`). The evidence is discharged only where the index is
   a literal, so no generation-time loop over chunks can call them, and `examples/attention.rac` spells out
   `maxChunk(…, 0, …)` to `maxChunk(…, 15, …)` in `pass1`, the same for `expChunk` in `pass2`, and `checks/emitted.rac`
   repeats it for `storeP`. A chunk combinator in the core (the `forChunks` of P: one step function over chunk `c`
   with `c < 16` in scope) would replace all three, but needs a way to pass the evidence along (§Raccoon 3).
2. *(removed)* **Done-token plumbing.** Seven protocols (three stage rings, the S ring, the exchange, the tensor-memory split and
   the allocation) each open a callback and each wants its `…Done` tokens back in a `Pair` beside the callback's own
   result. `examples/attention.rac` needs `AllDone`, nested in the order the scopes close, the re-shuffle at the end
   of `roles`, and a `kernel` of 40 lines of nested callbacks whose result types restate that nesting
   (`Pair(Attn.RingDone(rk), Pair(Attn.RingDone(rq), Pair(Attn.ExDone(x), Attn.AccDone(q))))` and so on). The
   explicit result types are required (`DESIGN.md` §1), so most of the kernel's text is types.
3. *(removed)* **Peeled iterations duplicated.** The first iteration changes `OState` (`fresh` to `held`), so `loopPeeled`'s
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
6. **Fences where the waiting thread is the loading one.** `loadAcc8` first fenced `after_thread_sync` before every
   load, as the GEMM's `stageChunk` does: 32 fences per key block. Review settled that `AccFull` comes only from
   `awaitAcc` in the same aligned warpgroup, every thread of which waited and fenced, so M9 does not apply and the
   fence is gone. `stageChunk` and `storeO` still fence once each; whether a token records who fenced is a question
   the GEMM epilogue shares.
7. **`tmemBase` special-cases offset 0** (`Core.rac`, `tmemBase`) so that the GEMMs' generated code stays byte-identical
   to `gpu/Gpu.rac`'s (`(v0 + 0u)` would otherwise appear in every MMA). `offsetBy`/`boxAt` do the same for box and
   column offsets.
8. **Fixed shapes in types.** `mmaScores` takes `AccRing(q, 128)` and checks both rings' boxes at generation; the
   exchange's layout (Ô at +0, P at +128) and `Tmem(a, 256)` are fixed in `withExchange`; `storeO` takes
   `AttnOut(L, DType.f32)` only, although `AttnOut` has a type parameter (A2's bf16 output).
9. **Two rings of one type.** The K and V rings are both `Ring(r, RingCfg.mk(2, box, box))`; nothing tells K's data
   from V's (`ATTENTION.md` §5 "the wrong data in a ring"). The example names them `kRing` and `vRing` only.
10. *(removed)* **The first block's statistics.** `softmax` starts the first block's maximum at −∞ (`fconst` of its bits) and sums
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

CPU time of the native binary, built from lemur_gpu at 9a390fe, on an idle machine, 2026-10-01:

| What | CPU s |
|---|---|
| checking `Core.rac` with `Check`, `Cuda`, `Text` (an empty file importing `encoding.Core`) | 0.3 |
| `gen.sh encoding/examples/tinygemm.rac` | 0.9 |
| checking `examples/attention.rac` without its final expression | 2.7 |
| `gen.sh encoding/examples/attention.rac` (checking, generation, the certificate, printing) | 7.5 |
| checking `checks/emitted.rac` | 2.9 |
| `gpu/check.sh`, everything | 35 (26 wall) |

The generated attention kernel is 2663 lines (181 KB) with its launcher: the two softmax iterations (peeled and
looped) unroll 16 chunks per pass and 16 per rescale, and every tensor-memory address repeats the warp-quadrant
expression.

## Paged attention (P1)

Observations from building `PAGED.md`'s P1 (`Core.rac`'s paged-attention section, `examples/paged_attention.rac`,
`harness/paged_attention_test.cu`, `rejected/paged_attention_mutants.py`).

1. *(removed)* **The example copies A1's roles.** `examples/paged_attention.rac` is `examples/attention.rac` with `Attn` renamed
   `Paged`, `Launch` defined as `PagedLaunch`, the kernel builder and its name changed, and a new loader: about 300 lines
   of the issuer, the softmax warpgroup (with `pass1`/`pass2` and their chunk functions), `roles` and `kernel` are
   duplicated. They could not be shared without editing `attention.rac`: every role takes the whole `Attn.Launch(l)`
   (`AttnLaunch`) and reads its fields, and `PagedLaunch` is another type. Sharing needs either the roles to take only
   what they read (the issuer `blocks`; the softmax `blocks`, `scale` and `out`; the loader is the one that differs),
   or the loader as a parameter of a kernel generic in its launch record. `diff` of the two files, after the rename,
   shows exactly the differences; keep them in step until then.
2. **Core repeats A1's builder.** `pagedAttentionKernel` repeats `attentionKernel`'s prologue (the `blocks`
   declaration, `q0`, `seq`), and `pagedLauncher` restates four of `attnLauncher`'s requirements (`seq > 0`,
   `seq mod 128 = 0`, `B > 0`, `dim = 128`) and its map encoding. Both were kept additive so that A1's output could not
   change; a shared prologue and requirement list would not change either kernel's text.
3. **The table is read twice per block.** `fillPage` reads its entry itself, so the loader's K and V fills each read
   it. One read would need a page value passing from one fill to the next, and a page value in the caller's hands is
   what `fillPage`'s signature rules out (a caller-chosen row). A sealed `PageAt` value (made only by a core read of the
   table, consumed by fills of the same `j`) would allow it. Both reads sit on the loader's path, after `acquire`'s
   wait; that the second is an L1 hit, and that neither matters next to the TMA loads, is expected but not measured.
4. **One map for both boxes.** `fillPage` takes one `PageMap` typed by the ring's first box and loads both boxes
   through it, so the second box's spec is checked at generation (`headStage`), not by the type. A ring of two
   different boxes is reachable only that way (`rejected/paged_attention_mutants.py`, `half_page_box`).
5. **What the mutants report.** A `PageMap` or `PageTable` passed where `storeO` expects an `AttnOut`, or a `PageMap`
   where `fillBlock` (then `fillHead`) expects a `HeadMap`, is reported as `ImplicitReconstructionFailed` ("Cannot reconstruct implicit
   argument L of Core.storeO: expected an application of Core.AttnOut, got Core.PageMap(…)"), not `TypeMismatch`: the
   implicit `L` is solved from the argument's type before the types are compared. The message is clear; the kind is
   surprising.
6. **The harness ran against a mock.** With no GPU, `paged_attention_test.cu` was linked against a host mock of the
   runtime and driver whose `cudaLaunchKernel` emulates the kernel's semantics (the guarded table read, the u32 row,
   TMA's signed coordinates and clipping) with the generated launcher's own host code. Every check passed, every
   refusal came from the generated requirements, and a mock that ignores the table failed every numerical check. The
   mock is not in the repository; it checks the harness and the launcher, not the kernel.
7. **Emitted-code checks need a whole client.** (Since the refactor they need an S ring too: P is written only from
   S, by `writeP`.) `checks/paged_emitted.rac` tests three lines of `fillPage`'s output,
   but `render` needs a well-formed kernel and `OOwn` is linear and consumed only by `storeO`, so the check builds a
   full exchange (16 `storeP` chunks, a product, the output) around one paged fill: about 100 lines of scaffolding,
   much of it copied from `checks/emitted.rac`, as are the line-reading helpers (`revOnto`, `linesFrom`). A shared
   module of text helpers for `checks/` would remove the latter; an example cannot be imported for the former
   ("ImportedModuleHasBody": `examples/paged_attention.rac` ends in its program). Text search inside the checker is
   slow enough to matter: the first version, whose filter used `Bool.and` (strict, so every line was searched for
   every test), took 24 s; with a `match`, 8.6 s.

Timing (CPU s of the native binary, built from lemur_gpu at fb08df0, on a machine not idle, 2026-10-01):
`gen.sh encoding/examples/paged_attention.rac` 9.1, `gen.sh encoding/examples/attention.rac` 9.0 (7.5 above, idle). The
generated paged kernel is 2677 lines (182 KB) with its launcher.

## A2: masks, tails and bf16 output

Observations from building `ATTENTION.md`'s A2 for both kernels (`Core.rac`'s masks section, `attnStart`, `storeO`'s
conversion, the examples' second kernels, the harnesses' A2 sizes).

1. **Two kernels per example.** Causal and O's type are generation-time arguments, so one example file renders both
   of its kernels (`String.append` of two `render`s) rather than a third copy of the roles (§"Paged attention" 1).
   That needed `#pragma once` in `gpu/stub/`'s headers, since each rendered kernel brings its own includes, and it
   doubles generation: about 19 CPU s per example. Every role that sees the launch or `OOwn` gained `{t: DType}`.
2. **The mask is recomputed per chunk.** `maskedScores` declares the chunk's first key and the limit
   (`min(seq, q + 1)`, with the row and its `__shfl_sync`) for each of the 16 chunks of each of the two passes, where
   once per block would do: the limit is a value the next call cannot be handed back without a public `bind` (§1, 4).
   With the eight selects, each kernel is about 3370 lines, against A1's 2663. The non-causal kernel masks every
   block, although only the last can hold a key past `seq`; FA4 masks only the blocks that need it, by a uniform
   branch, which here would need the whole chunk state through `branch` (§1, 5). Neither cost is measured.
3. **A collective inside a select.** The first `maskedScores` printed the causal limit as
   `(seq < q + 1) ? seq : q + 1` with `q` inlined, so the false arm would have run `__shfl_sync(0xffffffff, …)` in part
   of the warp. It now declares `q + 1` first. Nothing in the core or in `Check` notices a warp collective
   (`Builtin.warp`) inside a select or a branch arm; a checker rule could.
4. **The −∞ guard needs a register.** The example's `usable` computes `select(m < lowest, 0, m)` once per block and
   uses it in 128 exponents and the rescale; without a public `bind` it is a register set once and read once (§1, 4).
5. **bf16 conversion through `static_cast`.** `storeO` converts with `Expr.cast`, which prints
   `static_cast<__nv_bfloat16>(…)`, cuda_bf16.h's conversion from float (round to nearest even). It does not compile
   where `__CUDA_NO_BFLOAT16_CONVERSIONS__` is defined, as PyTorch's extension builds define it; a call of
   `__float2bfloat16_rn` would, but `Cuda.Expr` has no call form. The stub's `__nv_bfloat16` gained the conversion.
6. **The paged harness's reference was not exact.** P1's reference weighted V by `exp(s − LSE)`, which leaves residues
   near 10⁻¹⁷ where a canary's mean is 0, so T2's exact comparison would have failed on a correct kernel; it now
   divides by `l` as the contiguous harness does. Its guard bands were 32 rows, too few for a tail tile's 127 rows past
   the last head; they are now 128.
7. **The harnesses ran against a mock.** Both harnesses were linked against a host mock of the runtime and driver
   (not in the repository) whose `cudaLaunchKernel` emulates the kernels' semantics per CTA: rank-2 TMA rows with
   signed coordinates and zero fill (so tail blocks read the next head's rows), the guarded table read, the mask, the
   −∞ guard, bf16 P, the peeled first block, the rescale, `storeO`'s guard and bf16 rounding, behind the generated
   launchers' own host code. Every check passed. Broken emulations were caught: no tail mask (T1 at `seq` = 1), no
   causal mask, one key block too few for the causal kernel, stores past `seq` (the paged harness only once its guard
   bands were 128 rows), and truncating bf16 conversion (T2 and T3 of the causal kernel); running every key block in
   the causal kernel, the mask alone keeping it correct, passed. The mock checks the harnesses, the references and
   the launchers, not the kernels.

Timing (CPU s of the native binary, built from lemur_gpu at 267aa37, on a machine not idle, 2026-10-01):
`gen.sh encoding/examples/attention.rac` 18.8 and `gen.sh encoding/examples/paged_attention.rac` 19.3, each two
kernels; checking `checks/emitted.rac` 3.5 and `checks/paged_emitted.rac` 8.7. The generated files are 6744 lines
(455 KB) and 6772 lines (457 KB) with their launchers.

## Readability refactor

The library changes of the readability review (2026-10-01), applied to A2's core: what they removed, how the code
changed, and what friction remains.

**Removed.**
- **`…Done` tokens** (item 2; review F1). The seven families (`ProducerDone`, `ConsumerDone`, `AccProducerDone`,
  `AccConsumerDone`, `ExWriterDone`, `ExReaderDone`, `StoreDone`) and the examples' aliases are gone. A side is
  linear and belongs to its opener's scope, which the callback's result cannot name, so the callback must use it up,
  and the only operation that uses a side up without handing it on is its finisher, which now threads the emitter.
  The audit behind it: every other operation that takes a side gives one back, so a close still follows the
  producer's drain (`OBLIGATIONS.md` §6.10, §7). `shared` and `withAccHandoff` already worked this way; now all
  protocols do.
- **The unrolled chunk calls** (item 1; F2). `eachChunk` (pass 1) and `writeP` (pass 2) recurse over the chunks
  inside the core and hand a step each chunk's values and index; `loadAcc8` and `storeP`, their `fits` evidence and
  `PFree`'s per-chunk index steps, are internal. M14 holds by construction, and the example no longer needs
  `match h : e` (`docs/MATCH_EQUATION.md`).
- **The peeled copies** (items 3 and 10; F3). `mmaPV` overwrites when its `PReady` is `fresh`, and `rescaleO` emits
  nothing while Ô is `fresh`, so each role writes one loop body generic in `OState` and passes it as both `loopPeeled`
  arguments. The softmax's maximum starts at −∞ and its sum at 0, so the first block is the others' code: `α` =
  `ex2(−∞)` = +0 (A26) and `l = fma(0, 0, sum)` = sum exactly. That changes generated code, the only change of the
  refactor that does: per kernel, the maximum's register is declared from a `mov` of −∞ (+2 lines) instead of from 0
  and set to −∞ in the first block (−3), and the first block gains the read of the old maximum (+1), `α`'s `ex2`
  (+2), the combine (+3) and a fresh sum register in place of the dead `l = 0` (±0): 5 lines more per kernel, 10 per
  example file (6754 and 6782 lines). Every other change was checked byte-identical, by generating the new examples
  with the old first block.
- **The paged example's copy of A1's roles** (P1 item 1; F5). The issuer, the softmax warpgroup and the CTA's
  protocol nesting live in `Attention.rac`; each example is its loader and its kernel builder. The roles take only
  what they read (the issuer `blocks`; the softmax `blocks`, `mask`, `scale`, `out`, `own`), and `Attention.cta`
  takes the loader as a callback.
- **Self-qualification** (F4). Names resolve through the current namespace and the opens, except `Core.lt`: under
  `open Core`, an unqualified `lt` silently resolves to the prelude's root `lt` (a wrapper around the `LT` selector),
  whose error ("expected 3 params (self, a, b)") does not mention the shadowing.
- **`fillHead`'s two maps and four coordinates** (F10). `fillBlock(e, ring, slot, map, row)` loads both halves of a
  stage through one map at one row, as `fillPage` does, so the mismatched halves the review verified (half a K stage
  from `V_map`) can no longer be written.
- **The role nesting** (F12). `Layout.roles4` runs the load, issue and warpgroup roles of the shared eight-warp CTA;
  tinygemm uses it too, byte-identical.
- **Small items.** The dead `set(lReg, 0)` and the −∞ set of the first block (above); the eta lambda around the
  issuer's `scores` in `branch`; `Nat.sub(512, 256)`.

**Measured** (the review's classifier, `readability/measure.py`, its `Core.`/namespace prefixes made optional so that
it classifies unqualified code by the same rules). Code means non-comment text.

| | before: `attention.rac` | after: `attention.rac` + `Attention.rac` |
|---|---:|---:|
| code lines | 321 | 41 + 176 = 217 |
| code chars | 19,132 | 1,826 + 8,966 = 10,792 (−44%) |
| schedule operations | 7,467 (39%) | 699 + 3,132 = 3,831 (35%) |
| lambda binder and result types | 3,065 (16%) | 396 + 1,953 = 2,349 (22%) |
| Done plumbing (aliases, X arguments, code-free finishers, regrouping) | 2,009 (10.5%) | 4 + 214 = 218 (2.0%) |
| loop-state plumbing | 693 | 25 + 659 = 684 |
| `Fixed` evidence | 575 | 54 + 417 = 471 |
| `[fits]` evidence | 170 | 0 |
| unrolled chunk calls | 32 lines | 0 |
| qualifiers in code | 417 (10.9%) | 6: `Core.lt` twice, and the final expression's four, outside the namespace |
| lines wider than 120 columns | 62 | 7 + 32 |

`paged_attention.rac` went from 321 code lines to 41, with the 176 of `Attention.rac` shared; `tinygemm.rac` from
114 to 87, with `Layout.rac`'s 24 shared. The share of operations falls because the unrolled calls, which counted as
operations, are gone; what remains is mostly lambda headers.

**Remaining friction.**
- **Lambda headers** are now the largest incidental item (22% of the code): the CTA's nesting in `Attention.cta`,
  the loader's eta lambda in each example (eleven binders, to pass the rings' lifetimes), and the step lambdas of
  `eachChunk` and `writeP`. Review F7 and F8 (synthesized lambda result types, callback result types read through
  their binders) are the language proposals that would reach them.
- **`first`/`rest` wrappers.** A lambda with an implicit binder (`fun {o: OState}…`) cannot be passed where a
  function type is expected: "codomain … depends on its binders". So each role still writes two one-line wrappers
  around its one body (review F9a, named implicit instantiation, would remove them).
- **`Fixed` evidence** (review F6) is unchanged: `fixedScores` and the `fixedPair` chains.
- **The chunk index is a `Nat`.** A2's mask needs it (`maskedScores` takes the chunk), so `eachChunk` and `writeP`
  hand the step its index; a step can pass `maskedScores` another one, a wrong result as before. A sealed chunk value
  would make that unwritable.
- **K and V rings have one type up to their lifetime** (item 9; `ATTENTION.md` §2.6 no longer claims otherwise). A
  tensor tag would need `RingCfg` or `TmaSpec`, which the GEMM track shares (`ATTENTION.md` §5).
- **`Acc` tokens still travel back** through `splitTmem`, `withAccRing` and `withExchange` (review F1's follow-on):
  `Acc` is also a region's ownership token, and returning it is what lets a region be reused.
- **Mutants of the shared module** are checked as a module, not rendered: `mutate.py` writes the mutated file to a
  scratch directory, where the examples cannot import it. Every attention mutant is a type error, so that suffices;
  `half_page_box`, which only generation refuses, moved to `rejected/page_box_mutants.py` on `checks/paged_emitted.rac`.

