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


## A3a: two query tiles in ping-pong

Observations from building `A3.md`'s A3a (`Core.rac`'s score buffer, `Layout.rolesPair`,
`examples/attention_pingpong.rac`, `harness/attention_pingpong_test.cu`, `rejected/attention_pingpong_mutants.py`).

1. **Four copies of the softmax block per kernel.** The softmax role is one function generic in its warpgroup `f`,
   but each split arm is generated separately, and each role peels its first block: the block body is generated four
   times per kernel (two warpgroups, first and rest). A body generated once for both warpgroups would select its
   buffer by a run-time tile index (`warp / 4`); the core has one token family per buffer, chosen at generation, and
   no family of two buffers indexed at run time. Each kernel is about 4,800 lines (4,717 of kernel), against A2's
   3,377: the one pass and the masks computed once per block offset most of the copies.
2. **The first product cannot know it is first.** The issuer's loop runs `n − 1` times, and the product after it is
   the first when `n = 1`. Code after a loop is generated once, so that product cannot read `OState` as A2's `mmaPV`
   does. The warpgroup's block-0 rescale zeroes Ô instead (16 `tcgen05.st` of zeros, once per tile), and every
   product accumulates. The type then says more than A2's: `publishProbs` needs `Probs(…, held)`, so Ô is defined
   before any product, where A2 relies on `mmaPV` choosing the overwrite.
3. **A loop from block 1.** The issuer's loop runs `n − 1` times, from block 1; `loopFrom` exposes the loop from
   another first index that `loopPeeled` already emits, and `loop` is `loopFrom` from 0.
4. **The warpgroup–tile binding is a convention.** `rowInPairCta` (`256·blockIdx.x + 32·warp + lane`) is right because
   `rolesPair` puts tile 0's warpgroup on warps 0–3 and the example hands it buffer 0, whose S the MMA thread computes
   from the Q stage the loader filled at row `q0`. Nothing in the types ties the three together: swapping the buffers,
   or the Q rings, between the tiles is a wrong result, not a refusal. The other tile's buffer with one's own side is
   refused (`other_tiles_region`). Where the warpgroups sit is not a convention: the row reads the warp, so a
   warpgroup on warps 8–11 would compute rows 256 to 383 of the CTA, the next CTA's. The review found that race
   (a layout of the client's own, through `split`), and `OOwn` now names its warpgroup: the pair kernel hands those of
   warps 0 and 4 only, so no other warpgroup stores (`wg_on_warps_8_11`).
5. **`OOwn` per warpgroup.** `OOwn(l, t, f)` names the warpgroup that stores with it, which A2's kernels did not
   need (their row reads `warp mod 4` and `128·blockIdx.x`, the CTA's rows from any warpgroup). It costs A2's roles and
   checks a `groupWarp` in their types, and refuses one warpgroup taking the other's (`own_swapped`).
6. **Helper lambdas in the issuer.** The MMA thread's three steps per tile (`hold`, `scores`, `product`) are let-bound
   lambdas with implicit binders over the tile's buffer and ring lifetimes, called directly. They read well at the
   call sites, but their signatures are most of the issuer's text. `hold` (await, then `holdStage`) is now used for
   Q, K and V alike; it could be a core operation.
7. **The CTA's nesting.** Eight openers (`withTmem`, `splitTmem`, two `withScoreBuffer`s, four `withRing`s), each a
   lambda with its full binder types, around `rolesPair`. The first score buffer's result type carries the second
   region's `Acc` back out (`Pair(Acc(c1, …), Unit)`), as `Attention.cta`'s exchange carries the S region's.
8. **Register pressure is unmeasured.** The row lives in registers: 128 loaded values, which die as pass 1 makes the
   128 masked scores, which pass 2 consumes chunk by chunk. 384 threads leave 170 registers each without
   `setmaxnreg` (`A3.md` §4).
9. **Generation time.** Checking and generating the example takes about 31 CPU s (A2's examples about 19), so
   `check.sh` gains about 10 s of wall time, mostly this example and its mutants.
10. **The harness is shared through a header.** `harness/attention_harness.h` holds A2's harness, parameterized by
    the kernels' name (`ATTENTION_KERNEL`); `attention_test.cu` and `attention_pingpong_test.cu` each name theirs.
    `fa4_compare.py` still calls only `attention_launch` and `attention_causal_launch`.
11. **The harness ran against a mock.** `attention_pingpong_test.cu` was linked against a host mock of the runtime
    and driver (not in the repository) whose `cudaLaunchKernel` emulates A3a per CTA and tile: two query tiles at rows
    `256x` and `256x + 128`, one block count per CTA (tile 1's, causal), the rank-2 maps' zero fill, the mask, the
    −∞ guard, bf16 P, Ô zeroed in block 0 and rescaled after, the store guard and bf16 rounding, behind the
    generated launchers' own host code (grid `(ceil(seq/256), BH)`, 384 threads, 200,736 bytes of shared memory).
    Every check passed (192 size and input checks, 12 refusals). Broken emulations were caught: tile 1 reading tile
    0's Q rows (30 checks failed), the causal kernel running tile 0's block count (`2x + 1`, 60), no tail mask (44),
    no store guard (120), and Ô not zeroed in block 0 (all 192). The mock checks the harness, the references and
    the launchers, not the kernels.

## P2: paged decode with append

Observations from building `P2.md` (`Core.rac`'s paged-decode section, `examples/paged_append.rac`,
`examples/paged_decode.rac`, `examples/paged_combine.rac`, `harness/paged_decode_test.cu`, the three mutant tables).

1. **The roles' trip count is not typed.** The design asked for a mutant in which a role computes its own trip count.
   The roles take the count as a `Val`, as A2's do, so a loader that loops another number of times type-checks, and
   the roles then deadlock (M11). Refusing it would need a sealed key range whose loop alone yields the block index
   that `fillPage` and the mask take. That changes A2's roles, examples and emitted-code checks; it is not built
   (`P2.md` §5).
2. **A split is a sequence of its own keys.** The roles count a split's blocks from 0, so the decode needs no new
   `Mask`: A2's non-causal mask with the limit `keys − 128·first` masks a split's keys exactly, and an empty split's
   limit is 0. The loader alone adds `first` to the block index, to read the table (`add(g.first, i)`).
3. **An empty split still runs a block.** `loopPeeled` runs at least once, so every role of an empty split runs one
   block whose keys are all masked: a wasted load and two MMAs per empty CTA, and an Ô that can be NaN (0 · V of a
   page outside the sequence) times `1/l = ∞`. The store keeps O only where the split is non-empty
   (`AttnOut`'s `kept`). A uniform branch around the CTA's work would skip it, but would need the roles' protocol
   state through `branch` (§1, item 5).
4. **Lambdas that capture sealed values are scoped.** `storeRow`'s per-element function first read `out.kept` inside
   the lambda; the lambda then captured `out`, whose scope is `L`, and `storeChunks`' unscoped `Expr -> Expr`
   parameter refused it ("closures differ in scope"). Binding `out.kept` first, a plain `Option(Expr)`, fixed it. The
   message is clear; the cause (a field projection captures its struct) is not obvious.
5. **No vector types.** Each lane of the append copies its 16 bytes of K and of V as 8 bf16 element stores each, and
   the combine reads its 4 floats one by one: `Cuda.Expr` has no `uint4` or `float4`, and an `asm` for `ld.v4`/`st.v4`
   would need four declared outputs per access. The compiler may merge them; it is not measured.
6. **`status` is the launcher's.** The design's `status` vector is a local the generated launcher declares itself
   (`const cudaError_t status`), so `Check.names` refused the kernel at `render`. It is `appended`.
7. **SIMT kernels with launchers printed no headers.** `Cuda.headers` included `cuda_bf16.h` and `cuda_runtime.h` only
   for kernels with tensor maps, so the append and combine kernels did not compile. `Cuda.rac` now includes them for a
   launched kernel without maps; every other kernel prints as before.
8. **Groups for one-warp CTAs.** The append and combine kernels are one warp per CTA, as `Group.warps(0, 1)`
   (`warpCta`), so that lane 0's broadcast flag is uniform and the claim's arm keeps the warp's group. A multi-warp CTA
   would make the flag per-warp, which `Grain` cannot say (it is `thread` or CTA-`uniform`), and the arm `diverged`.
9. **Comparisons.** `BinOp` has no `!=` and `Expr` no negation, so the claim's branch tests "the word holds this
   launch's epoch" and puts the CAS in the else arm, and the decode prologue names `nonEmpty` rather than `empty`.
   Neither reads worse.
10. **The combine's accumulators.** A `Reg4`, read whole and written whole per split (`get4`, `set4`), where four
    values would do: there is no public `bind` (§1, item 4).
11. **One example, three kernels.** `G` is a generation-time constant (it is Q's box height), so the decode example
    renders `paged_decode_g1`, `_g4` and `_g8`: about 27 CPU s, and 10,005 lines with their launchers. The append and
    combine examples take about 0.6 CPU s each (80 and 81 lines). `check.sh` grows by about 10 s of wall time.
12. **The harness ran against a mock.** `paged_decode_test.cu` was linked against a host mock of the runtime and
    driver (not in the repository) whose `cudaLaunchKernel` emulates the three kernels behind the generated
    launchers' own host code: the append's claims in a shuffled warp order, with the epoch and the CAS; the decode's
    prologue, split ranges, packed Q rows (box height G), paged TMA rows with signed coordinates and zero fill, the
    mask, A2's softmax with bf16 P, and the stores with the empty-split zero; and the combine. Every check passed (27
    decode configurations over three sets of lengths, G ∈ {1, 4, 8} and splits ∈ {1, 3, 8}; the collision (and a
    decode after it), out-of-range and epoch appends; 38 refusals). Broken emulations were caught: claims that ignore
    the owners (`noclaim`) or overwrite a current one (`steal`), each in the collision and reused-epoch checks; an
    entry past the table read as column 0 (`nobound`); floor-sized splits (6 checks), no length mask (28), empty splits
    not zeroed (19), a CTA storing G + 1 rows (28), and an unweighted combine (19). P1's harness, moved to the new
    layout, passed against the same mock. The mock checks the harness, the references and the launchers, not the
    kernels. It runs each claim at once, so it never exercises the concurrent path, a CAS that fails because another
    warp claimed the word between its load and its CAS; `harness/claim_model.py` checks that path instead (item 13).
13. **A model check.** `harness/claim_model.py` runs every interleaving of the claim's load and CAS for three warps of
    one word, from every start value, at three epochs, and requires at most one claim to hold; it also shows that two
    overlapping launches can both hold one. It takes a fraction of a second, so `check.sh` runs it (a `model` kind)
    rather than only compiling it.

**The hostile review** (2026-10-01) found:
- **A race on the row.** Every lane read `lens` and the table to compute its own row, but only lane 0's page was
  claimed: a writer of the table between lane 0's read and another lane's would send that lane to a page another warp
  claimed. Lane 0 now reads them alone and broadcasts the row with the result, so the row is the claimed one by data
  flow. The launch contracts now also say that nothing writes an input during a launch (M10).
- **Writes that repeat.** `appendRow` twice, in a loop, or not at all all checked, so "written once" (S5) was false and
  `appended` meant "claimed". The arm now receives a linear `AppendOwn` that `appendRow` uses up (`append_twice`,
  `append_in_loop`, `arm_without_append`).
- **A wrapping block count.** `n = (lens[b] + 1 + 127) / 128` wrapped for lengths near 2^32; it is now
  `lens[b] / 128 + 1`, and a split's keys `(lens[b] − 128·first) + 1`.
- **Overstated docs.** The claim's step 3 had a second success case (`prev = mine`) that one launch cannot reach;
  `claim_leaves_arm` is refused by the arm's result type, not by its scope (no mutant is refused by the scope alone);
  the owners' start value and the refusal of epoch 0 are about freshness, not safety.
- **Readability.** Hand-numbered ids and rebuilt `Gen`s in the decode prologue and the claim (now `bind`, `reg`,
  `asmOut` and `branch`), unrolled columns in the combine (now `F32x4.map`, `zip`, `Reg4`), launcher parameter lists
  written twice (now derived from the kernels'), and a nested `Bool.cond` in `Cuda.headers` (now a rule per header).

## CTA pairs

Observations from building `TWO_CTA.md`'s steps 1 and 2 (`Core.rac`'s pair sections, `examples/tinygemm_pair.rac`,
`harness/tinygemm_pair_test.cu`, `rejected/tinygemm_pair_mutants.py`).

1. **Reading the CTA group consumes the context.** `Ctx` is linear, so an emitter cannot look at the generation state
   and then emit. Every barrier wait and commit now prints the group's form, so their emitters pass a function of the
   group to `emitIn` (a lambda `fun (g: CtaGroup): List(Stmt) => …` where they built a list), at thirteen wait sites
   and five commits. A non-consuming read of a context's generation state would keep them as they were.
2. **No struct update.** `Gen` gained a field, and every one of its sixteen `Gen.mk(…)` constructions in `Core.rac`
   had to name it, though none changes it: most of them only bump `next`. A functional update (`{gen with next := …}`)
   would have made the change one line.
3. **`Pair` is taken.** The design's `Pair(l)` collides with the prelude's product type, which every signature of
   the core uses; the handle is `CtaPair(l)`.
4. **Shared printer types.** The cluster shape is a property of the kernel, but `Cuda.Kernel` and `Cuda.Launcher` are
   shared with `gpu/Gpu.rac`, which must not change, so neither could gain a field. The shape rides on the launcher's
   grid instead (`Grid.pairs`), which costs a constructor in `Cuda.Grid` and a case each in `Check.gridExprs`,
   `Spec.GridExpr` and `proofs/Fold.rac`'s `gridMem`.
5. **A 16-bit operand.** The multicast commit's CTA mask is a 16-bit operand, and `Cuda.DType` has no 16-bit integer
   for an `"h"` constraint, so the template sets the mask in a `.b16` register of its own block.
6. **Delegations per pair operation.** Since the group chooses the wait and commit forms (item 1), most pair ring
   operations are the single-CTA ones, but each still needs its own entry point on the sealed `PairRing` or
   `PairAccRing`: twelve of the pair sections' operations are one-line delegations. Merging them into the
   single-CTA operations would let the `Leader`-free takes and the caller-coordinate `fill` reach a pair ring. Sharing
   the token families, with the sealed `PairRing` wrapping a `Ring`, kept the types from doubling: sealed selectors are
   private, so a client cannot unwrap a `PairRing` and run a single-CTA operation on it.
7. **What the mutants can say.** Two of the brief's mistakes cannot be written, so their mutants show the nearest
   attempt refused: a consumer outside `onLeader` needs a `Leader`, which outside the arm only a forged one could be
   (`SealedConstructor`); a fill or store of the other CTA's half needs a `PairTile` of other rows, likewise forged.
   The `Leader` escaping its arm is a `TypeMismatch`, since the arm hands back only its context, not a scope error.
8. **The rank is the core's.** Rows and halves come from the sealed `PairTile`, so the example never names the rank.
   The review found that an exported `rank` let a client's trip count differ between the CTAs, which deadlocks the
   pair; it is no longer exported, and the attention kernels to come will need their per-CTA coordinates from the
   core as the GEMM does.
9. **One CTA per SM by padding.** Nothing in the launcher API states occupancy, so the pair builder pads its shared
   memory request to more than half an SM's (`pairShared`), wasting up to 116 KB when a pair kernel needs less.
10. **The harness ran against a mock.** `tinygemm_pair_test.cu` was linked against a host mock of the runtime and
   driver (not in the repository) whose `cudaLaunchKernel` checks the pair grid (`2·ceil(N/256)` × `ceil(M/256)`, 256
   threads) and emulates each pair per CTA: each CTA's A rows and half of B through the rank-2 maps with zero fill, the
   leader's M = 256 product of each CTA's rows with both halves, and each CTA's guarded stores of its own rows, behind
   the generated launcher's own host code. Every check passed: 13 sizes three times each, 5 refusals. Broken emulations
   were caught: the peer loading the leader's rows of A (11 of the 13 sizes failed: the two whose peer has no rows
   passed), the CTAs swapping their halves of B (13), stores not guarded by N (7), the peer storing nothing (11), one
   K slice only (7, every size with K > 64). The mock checks the harness, the reference and the launcher, not the
   kernel.

Timing (CPU s of the native binary, on a machine not idle, 2026-10-01): `gen.sh encoding/examples/tinygemm_pair.rac`
1.3, as `tinygemm.rac`. The generated pair kernel is 311 lines with its launcher, 266 without.

## A3b: a correction warpgroup

Observations from building `A3B.md`'s A3b (`Core.rac`'s correction-warpgroup section, `Layout.rolesCorrected`,
`examples/attention_a3b.rac`, `harness/attention_a3b_test.cu`, `rejected/attention_a3b_mutants.py`).

1. **Who rescales Ô is in the buffer's type.** A3b's softmax warpgroup holds the same tokens as A3a's (`RowsAt`,
   `Scored`, `Loaded`, `Probs`), so without more it could call A3a's `rescaleRow` and race the correction warpgroup
   on the same lanes. `ScoreBuffer(x, h)` now names its rescaler (`Rescaler.softmax` or `.correction`), chosen by its
   opener; every score-buffer operation gained `{h: Rescaler}`, and A3a's example changed in its types only.
2. **Block 0's α was dead code.** The first build sent α in every block, so the correction warpgroup read block 0's
   and never used it; the C++ compile of `check.sh` (`-Werror`) refused the unused variable. Block 0 now sends no α:
   `publishAlpha` sends only when the softmax side's Ô is `held`. The correction warpgroup zeroes Ô in block 0 without
   a wait, since no product has touched Ô, so its first publish can come before the softmax's.
3. **`__launch_bounds__` had no place.** `Cuda.Kernel` is `Gpu.rac`'s too, so it gained no field. `Core.Program` has
   `bounds`, `render` prints through `Cuda.boundedKernel`, and `Cuda.kernel` is `boundedKernel` without bounds. The
   `Gen` records the bounds when `splitWarpgroups` emits `setmaxnreg`, and `finish` hands them on, so no other builder
   names them; every `Gen.mk` carries the field.
4. **`setmaxnreg` is a split, not an operation.** `ptxas` allocates a role's code within a count only if the
   `setmaxnreg` dominates it, and the direction (`.inc` or `.dec`) is only known from the count before. So
   `splitWarpgroups` makes it the first instruction of each warpgroup's branch, once (a `RegPermit`), from 128 (A59),
   and the counts are the layout's (`rolesCorrected`), not the roles'. Each branch ends with the warpgroup's named
   barrier and `setmaxnreg` back to 128, so the code after the split (joins, invalidations, the deallocation) runs at
   128. That costs four named barriers (nine of 15 in all). `withRegs` returns the wrapped role as a function,
   since a definition cannot be partly applied, and takes its warp `f` explicitly, since a function parameter's type
   does not force an implicit one.
5. **The issuer and the loader are shared.** A3b's MMA order and loads are A3a's, so they moved from A3a's example to
   `Attention.rac` (`pairLoader`, `pairIssuer`), generic in their warp and in the buffers' rescaler. A3a's CUDA is
   byte-identical; its issuer mutant moved to `attention_mutants.py`.
6. **A branch with one arm.** The correction's skip has nothing to do where the vote is false. `Core.when` is
   `branch` with an else arm that hands the state on, so the example writes the rescaling arm only.
7. **Choosing between two emitters.** `exp2(e, emulated(c, j), x)` matches on a `Bool`: `Bool.cond` is strict, so it
   would build both `ex2` and `ex2emu` from one linear emitter. The softmax's `exps` is A2's with that choice; giving
   A2's `exps` the predicate would add a parameter to A2's and A3a's calls for a feature they do not use.
8. **The α ring's index is `threadIdx.x mod 128`,** not `32·(warp mod 4) + lane`: the same number in an aligned
   warpgroup, without the warp index's `__shfl_sync`, which would need the warp reconverged after the ring's wait.
   The ring has one slot: at most one α per tile is in flight (A3B.md §3.1). The first build had two, never both
   used.
9. **`Grain` can say "per warp".** P2's item 8 found that `Grain` could not express a value uniform in a warp;
   `Grain.warp` does now, from `voteAny` only. P2's one-warp CTAs still call such a value `uniform`, which there it is.
10. **FA4's emulated columns.** A3B.md first took `ex2_emu_freq = 10` from FA4's 2-CTA row; FA4's `cta_group::1`
    kernels use 16, so 16 columns of 128 (A3B.md §7).
11. **The polynomial's error, measured.** A host program (not in the repository) runs every f32 x in [−127, 8]
    (2,214,461,442 values: +0 to 8 and −0 to −127, subnormals included) through `ex2emu`'s instructions as the device
    rounds them: `max`; `add.rm` of c and K = 1.5·2²³, emulated as the round-to-nearest sum s stepped down by one ulp
    when s − K > c, a test that double computes exactly (s − K is exact); `sub.rn`, `fma.rn` (`std::fmaf`); the
    integer add of `j << 23` to the polynomial's bits; IEEE throughout, no flush to zero. f = x − j lies in [0, 1]: it
    is 1.0 when `sub.rn` rounds a value just below 1 up. Against `exp2` in double: at most 8.77 · 10⁻⁵ (below 2⁻¹³·⁴⁷)
    relative for x ≥ −126, at x ≈ 0.1007; at most 2⁻¹²⁷ absolute for x in [−127, −126), where the exponent's
    addition makes a subnormal and −127 itself gives +0. The cubic alone, in exact arithmetic on [0, 1), is off by
    8.76 · 10⁻⁵, so the rounding adds almost nothing. Integer x (T2's and T3's) give exact powers of two, and −∞ gives
    +0. `ATTENTION.md` §1.3 adds it to T1's budget. The first version of the program compared s with c + K in double,
    which rounds for c ∈ [−2⁻³⁰, 0) and so emulated `add.rm` wrongly for about 37% of the inputs; the hostile review
    found it. The corrected run gives the same bound. Outside [−127, 8]: x ≥ 128 overflows the exponent's addition
    (128 gives +∞, 129 gives −0), and NaN gives +0. A3b's exponents are at most 8.
12. **Register pressure is unmeasured.** Estimates: a softmax thread holds the 128 masked scores, the statistics, the
    ring's phase register and one chunk's exponentials (the emulation's 7 temporaries live inside one `asm`), about
    160–170 of its 192; a correction thread one chunk of Ô (8 loads), α and two ring registers, about 30 of its 72;
    the MMA and load threads their rings' registers and addresses, well under 56. `-Xptxas -v` on hardware will say.
13. **Size and time.** Each kernel is 4,807 (non-causal) and 4,935 (causal) lines, against A3a's 4,713 and 4,841: the
    softmax loses its rescale, the correction role adds about 450 lines (two tiles' rescales, peeled), and
    `ex2emu` is one `asm` line each. 201,760 bytes of shared memory (A3a's 200,736 and two α rings of 544). Checking and
    generating the example takes about 39 CPU s (A3a's 33, on the same loaded machine).
14. **Per block, per thread** (the loops' bodies, block i ≥ 1):

    | Role | `ex2.approx` | emulated | `tcgen05.ld` / `.st` | waits | arrivals |
    |---|---:|---:|---:|---:|---:|
    | A3a softmax | 129 | 0 | 32 / 32 (16 of each the rescale) | 1 | 1 |
    | A3b softmax | 113 | 16 | 16 / 16 | 2 (S full, α empty) | 2 (α full, P full) |
    | A3b correction, both tiles | 0 | 0 | 32 / 32 when both rescale, else fewer | 2 (α full) | 4 (α empty, P full) |

    The MMA and load threads' loops are A3a's: 4 waits, 32 MMAs and 4 commits; 2 waits, 2 arrivals and 4 TMA loads.
15. **The harness ran against a mock.** `attention_a3b_test.cu` was linked against a host mock of the runtime and
    driver (not in the repository), A3a's extended: 512 threads; the lazy maximum; `ex2emu`'s instruction sequence
    with the device's rounding in the emulated columns (`std::exp2f`, flushed, standing in for `ex2.approx`);
    the chunk sums in the kernel's order and `l = fma(α, l, sum)`; Ô zeroed in block 0 and, after, each warp's rows
    multiplied by their α when one of its 32 has α < 1. Every check passed (192 size and input checks, 12 refusals).
    Broken emulations were caught: no rescale (26 checks failed), `l` not rescaled (108), the vote taken from lane 0
    only (20), Ô not zeroed (192), `add.rn` in place of `add.rm` (14, LSE), which puts the cubic's argument in
    [−0.5, 0.5), and the cubic's coefficients reversed (192). Two variants that are not bugs passed every check: the
    maximum moved on every block (no lag), and no column emulated. After the review fixes (one slot, the registers back
    to 128, the corrected `add.rm`) the run was repeated, and every check passed again.

## The persistent pair GEMM

Observations from building `TWO_CTA.md`'s step 4 for the GEMM (`Core.rac`'s section "CTA pairs: the persistent GEMM",
`examples/gemm_pair.rac`, `harness/gemm_pair_test.cu`, `harness/run_gemm_pair.sh`, `rejected/gemm_pair_mutants.py`).

1. **Little new code.** The pair's families were already indexed by a lifetime, so a tile loop's `PairTile(m)` and
   `HalfOwn(m)` needed no new family; only `fillPair` had to let the tile's lifetime differ from the maps'. The
   single-CTA schedule became generic in its tile height, first index and step (`Sched`, `schedule`), and both
   persistent builders share it; `forChunks` and `forHalfChunks` share their loop (`chunkLoop`). Every other example
   generates byte-identical code. What is new: `PairSched`, its two loops, `forHalfChunks` and the builder, 82 lines.
2. **An implicit is not forced by a callback's binder.** `forHalfChunks` first took the chunks' width implicitly, from
   its body's `ChunkAt(p, n)`; the checker refuses ("cannot be implicit: it is not forced by the type of any later
   explicit parameter"), as A3b's `withRegs` found. It took the accumulator ring for its width, and checked it against
   the tile's at generation, until the review moved the width into `PairTile`'s type (`PairTile(l, w)`): the tile now
   forces it, and `storeHalf`'s check became a type too.
3. **The release cannot sit in the last chunk.** The accumulator should go back to the leader right after the tile's
   last tensor-memory load. The chunk loop is generated once, so code for the last iteration only would need the loop's
   state to change type in it, or a peeled last chunk (one more copy of the chunk's code). The release follows the
   loop instead: after the last chunk's shared-memory writes and its store's issue, before any store completes. Not
   measured; the chunk's writes are a small part of a tile's mainloop.
4. **A grid constructor costs five files.** `Grid.persistentPairs` needed a case in `Cuda.gridDims`,
   `Cuda.clusterDims`, `Check.gridExprs`, `Spec.GridExpr` and `proofs/Fold.rac`'s `gridMem`, as `Grid.pairs` did
   (§"CTA pairs" 4). A grid that were a launch shape (CTAs or pairs) times an extent (fixed or persistent) would take
   one.
5. **Stores per warp.** The epilogue is the single-CTA one, whose staging buffers are per warp: a 128×32 subtile is
   four 32×32 TMA stores, each warp's lane 0 committing and waiting for its own. CUTLASS stores one 128×32 box per
   subtile after a named barrier of the warpgroup. Which is faster is a hardware question.
6. **Two planned mutants cannot be written.** A staging buffer written before its store finished reading it needs a
   `StageFree` that no wait made; `stage_twice_per_acquire` tries a second chunk under one wait (a reused linear
   token). A tile sequence that differs between the CTAs needs a value that differs between them, which the client
   does not have (M18), or a role's loop run in one CTA only. The first build allowed the second: an `onLeader` arm
   could capture linear values, so a second producer loop, or the whole epilogue, could run in the leader alone, and
   so could a producer's drain or the stores' last wait (the review's `peer_skips_drain` and
   `peer_skips_store_wait`). The arm now captures no linear value and is handed only leader-only sides
   (`LeaderOnly`, M20); the four mutants are refused, by the closure's kind. The re-review found a third way, a
   register: an arm sets an outer register, and both CTAs read it, vote on it and branch. `set` now refuses a
   register declared outside the innermost arm (`leader_flag_tile_loop`). `single_cta_schedule` tries the
   single-CTA tile loop, whose start differs between the CTAs. An accumulator released before its loads is a reused
   `AccFull` (`release_before_loads`).
7. **The grid trusts residency.** `2·min(SMs/2, tiles)` CTAs, as FA4 launches, assumes every pair of
   SMs holds a cluster. If fewer clusters fit at once, the rest run their whole tile sequences after the others. The
   launcher does not ask `cudaOccupancyMaxActiveClusters`; the first hardware run's time will tell.
8. **Size and time.** The generated kernel is 400 lines with its launcher (332 without), and 230,496 bytes of shared
   memory. Checking and generating the example takes 1.6 CPU s; the mutant table about 10 s of wall time.
9. **The harness ran against a mock.** `gemm_pair_test.cu` was linked against a host mock of the runtime and driver
   (not in the repository), the pair TinyGEMM's extended: it checks the launch (grid `2·min(SMs/2, tiles)` × 1 of 256
   threads, the requested shared memory, the C map's f32 32×32 boxes) and emulates each pair's tile sequence from its
   cluster index in steps of the cluster count, in the band order, each CTA's loads and its stores in 32×32 boxes
   clipped to the matrix, and aborts on any element written twice. Every check passed: 15 sizes three times each at
   148 SMs (74 pairs: from 1 tile to 3 or 4 tiles a pair), again at 8 SMs (4 pairs, up to 64 tiles a pair), 7
   refusals, and the timing mode on small sizes. Broken emulations were caught: the peer loading the leader's rows of
   A (13 of 15 sizes failed), the CTAs swapping their halves of B (15), stores not clipped to N, every pair starting at
   tile 0, and a step of one tile (each a double write), the last band taken as full (2, the sizes whose last band is
   shorter), one K slice only (9, every size with K > 64), and the peer storing nothing (13). The run was repeated
   after the review fixes, with the size the review added (2560 × 2048, K = 520). The mock checks the
   harness, the reference and the launcher, not the kernel.
10. **The load before the wait.** The first build waited for a chunk's staging buffer (`acquireStage`) before loading
    the chunk from tensor memory, so each load queued behind the store of two chunks ago. `stageAcc` and
    `stageAccFull` are now split into a load (`loadAccChunk`, `loadBufferChunk`, `loadPairChunk`, giving the sealed
    `ChunkRegs` of the block) and `writeStage`, and the chunk loads first. It costs no registers: the 32 values were
    live from the load to the shared-memory writes before, and still are, now across the wait. The single-CTA
    TinyGEMM's CUDA changes by the moved wait only.
11. **An arm that captured too much.** The review found that `onLeader`'s arm could capture linear values: what it used
    up counted as used, but only the leader ran it, so the peer could skip a producer's drain or its stores' last wait
    and close with copies or stores in flight. The arm is now unrestricted, as `branch`'s arms are, and takes the sides
    it may use up as an argument, with evidence (`LeaderOnly`) that each is the leader's alone: a pair ring's consumer, a
    pair accumulator ring's issuing side, pairs of them, and `Unit`. The issuer's arm now names its two sides in its
    type.
12. **Mutants that change several places.** The `onLeader` mutants need the pair in the producer or the epilogue, a
    parameter and a call apart from the arm, so `mutate.py` takes `edits`, a list of replacements, beside `old` and
    `new`.
13. **A register out of the arm.** The re-review showed that an unrestricted arm could still carry a value out: it set
    a register declared before it, and code both CTAs ran read the register, voted on it (`voteAny`, grain `warp`)
    and ran a second tile loop under `when` in the leader only. A deadlock, not a race. `Gen` now records the first
    register an arm may write (`writable`, restored by `after`), and `set` refuses an older one. That cost a `Gen` field
    and the nineteen `Gen.mk` sites one more argument each (§"CTA pairs" 2: no struct update). Registers are the only
    unrestricted mutable state: every other write needs a linear token.
14. **The rule the bug broke** is M23: a callback that may capture linear values runs on exactly its group's threads,
    in every CTA; a combinator that runs a callback conditionally or repeatedly narrows the group or takes an
    unrestricted callback. The audit found every combinator in one of the two kinds, or unconditional, and gave each
    conditional one a standing mutant that captures an outer linear token: nine more, in `gemm_pair_mutants.py`,
    `tinygemm_mutants.py` and `paged_append_mutants.py`. `forTiles` and `forOwnedTiles` have no client here to mutate.
15. **The evidence names the pair handle.** `leaderOnlyConsumer(ring)` and `leaderOnlyAccProducer(accs)` take the
    `PairRing` and `PairAccRing`, so the evidence speaks of a pair protocol's side, not of any `Consumer`.
