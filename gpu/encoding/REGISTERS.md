# Registers as a modelled resource

Status: steps 1–3 of §8 **built** (2026-10-01): the toolkit container, the `Registers` module with bounds in every
builder, and the register check in `check.sh`. Steps 4 and 5 are design.

## 1. Why

The core models two of the SM's three on-chip resources exactly:
- **Shared memory.** Each opener reserves its bytes at generation, and `Check.sharedSize` refuses a kernel over
  232,448 bytes.
- **Tensor memory.** It is allocated in columns, and `splitTmem` hands out its regions as linear tokens.

Registers are the third, and the core does not model them. A `Val` or `reg` is a C++ variable, and `ptxas` allocates
the physical registers after we print. Two things on the first B200 session (`NOTES.md`, "Hardware session") came from
that:
- **A3a's causal kernel did not launch.** Unbounded, `ptxas` used 184 registers per thread; 384 × 184 = 70,656, more
  than an SM's 65,536.
- **A3b deadlocked in `setmaxnreg`.** The bookkeeping of the register pool was `Core.rac`'s own code, which nothing
  checks, because Core mints its own tokens.

Spilling is the other failure mode, and it is silent. A kernel that spills runs, correctly and slowly. **Performant code
is code that does not spill**, so a spill must be an error the user sees, not a fallback.

## 2. The discipline for every linear resource

**Rule.** Each resource family has its own small sealed module. That module alone mints its tokens, moves them, retires
them, and emits the instructions that do so. `Core.rac` composes the modules as their client, so its use of every
resource is type-checked like any client's.

**Why.** Sealing is per file. Today `Core.rac` seals every family, so it can mint any token anywhere, and its own
bookkeeping is unchecked. A3b's deadlock was such bookkeeping, and so was the `onLeader` capture. The `onLeader` one is
a control combinator's signature, which this rule does not reach (§9, decision 1).

**The families:**

| Module | Tokens |
|---|---|
| `Registers` | the CTA's register pool, per-warpgroup shares (§3) |
| `Tmem` | the allocation permit, regions, `Acc` |
| `Rings` | stage rings and their sides |
| `AccRings` | accumulator rings and their sides |
| `ScoreBuffers` | A1's exchange and A3's score buffers |
| `Staging` | TMA-store staging buffers and store sides |
| `Claims` | P2's claims and appends |
| `Pairs` | `CtaPair`, `Leader`, `LeaderOnly` |
| `Outputs` | `OOwn`, `TileOwn` |

**The language limit.** Raccoon seals per file and has no private definitions, and emission is gated by Core's sealed
`Key`. So the rule above cannot hold as stated:
- **A module cannot emit.** It would need the `Key`, and anything Core could use to hand it over a client could call
  too. A module also cannot import `Core` for it, since `Core` imports the module.
- **So a module is pure.** It owns its sealed families and their only operations, and emits nothing. `Core` emits, in
  emitters that need the `Key` and the module's tokens, so Core cannot emit an instruction of the family without the
  token whose type states it.
- **Creating a pool stays trusted.** `Registers.pool` is a definition any module can call. That only builders call
  it, at the count their kernel is compiled for, is a stated obligation (`OBLIGATIONS.md` §2 and §7, M24). A client's
  pool at another count makes changes from a count the warps do not hold; the register check (§5) refuses that
  kernel, when the toolkit is there.
- **Core's raw assembly stays trusted.** Core owns all emission, so it could still print a `setmaxnreg` through its raw
  `asm` statements, outside the emitters that need a share. That it does not is reviewed. The register check reads
  every `setmaxnreg` of an example's output against the split's rule, which a stray one breaks unless it happens to
  fit it.

`Registers.rac` is built so (§3). §9, open question 1, lists the remedies that would close the last two points.

**The trusted base.** What stays trusted is these modules plus the control combinators: the kernel builders, `split`,
`elect`, `branch`, `when`, the loops and `onLeader`. Their obligations are stated in `OBLIGATIONS.md` and reviewed.
That base is smaller than today's, which is all of `Core.rac`.

**Migration.** One family at a time, starting with registers (this document). Every example must still generate
byte-identical CUDA, apart from the changes §7 lists.

## 3. Supply

**What is known exactly:**
- **The SM's registers:** 65,536, of 32 bits each.
- **The CTA's threads:** from its builder.
- **The kernel's residency `r`:** the CTAs it means to run per SM. Every tensor-core kernel here is 1, set by its
  shared memory; one-warp SIMT kernels may want more.
- **The allocation granularity:** 8 registers per thread.

**The uniform budget.** For a kernel that does not change counts, the budget is ⌊65,536 / (threads · r)⌋ rounded down
to a multiple of 8, and at most 255. Every builder prints `__launch_bounds__(threads, r)`, so `ptxas` never allocates
beyond it. A kernel can then never fail to launch for registers. At worst it spills, and §5 makes a spill an error.

**Per-warpgroup counts.** For a kernel whose roles need different counts (A3b: softmax 192, correction 72, the rest 56):
- **The user** chooses the counts as generation-time numbers on the role layout, or `auto` (§5).
- **The `Registers` module** (`Registers.rac`) owns the CTA's register pool, `RegPool(l, threads, perThread)`: its
  threads times the uniform budget, which `setmaxnreg` draws on (SASS: `USETMAXREG…CTAPOOL`). The builder creates it
  (`Registers.pool(l, threads, r)`).
- **The split** (`Registers.split`, which A3b's `splitWarpgroups` calls) divides the pool into shares:
  - requires, as evidence, that the counts fit it (`Registers.fits`): each a multiple of 8 from 24 to 256, and
    128 · Σ counts ≤ 512 · budget, which is 65,536 at A3b's budget of 128;
  - gives each warpgroup a `RegShare(l, f, perThread, count)`: f its first warp, `perThread` the pool's count, which
    its warps hold before and after the split.
- **Core's entry emitter** (`Core.withShare`) needs the Key and warpgroup f's share. It emits the change from the
  share's per-thread count to its count as the first instruction of f's branch, runs the role, and hands the share on. The role
  itself never sees the share; it cannot change its count.
- **Core's way back** (`Core.regsBack`) needs the Key and all four shares, which leave the branches only at the split's
  join. It emits each warpgroup's change back to the budget after the join barrier, in warpgroup order, then a CTA
  barrier, then ends the shares.
- **The join** (`Registers.join`) returns the four shares to the pool, together. The pool is not consumed, so a kernel may
  split any number of times.
- **No user code calls `setmaxnreg`.**

**The invariant: outside a split, every warp holds the pool's per-thread count.** The barrier after the way back makes it true:
once every warp has passed it, every warp's change back has run.

**Why this cannot deadlock:**
- An increase at a split waits only for decreases at that split. Those never wait, and they depend on nothing.
- An increase after the join waits only for decreases after the join. Those also never wait.
- There is no operation that changes a share between the split and the join. So a warpgroup cannot take back
  registers another warpgroup's first increase needs, which is A3b's deadlock.
- No split starts before the last split's way back has finished, by the barrier. So each split starts from the uniform
  budget, and the argument holds per split: in sequence, in a loop, or under a uniform branch.

**Why the barrier.** Without it, nothing waits for the way back to finish, and two splits in sequence can deadlock.
With A3b's counts, after the first join:
1. Warpgroup 0 goes back from 192 to 128, and at once enters the second split and goes up to 192 again.
2. Warpgroup 1 does the same. The 128 registers per thread the two decreases freed are taken again.
3. Warpgroups 2 and 3, going back up from 72 and 56, wait for registers no one will free: warpgroups 0 and 1 are in
   their roles, waiting for the MMA warp, which is in warpgroup 3.

With the barrier, warpgroups 0 and 1 wait at it until warpgroups 2 and 3 are back at 128. It costs A3b one
`__syncthreads()` after the split, its only change to generated code in this step besides the bounds.

**Where a split can run.** It needs a `cta(512)` context: the kernel's spine, a uniform branch's arm or a loop's body,
never a role (`warps(f, 4)`) or a per-thread or per-warp branch (`diverged`, `warpwise`). So splits never nest.

**What the pool carries**, and why it stays: the CTA's threads and its per-thread count, `RegPool(l, threads,
perThread)`, which the kernel's context does not carry. The split checks the counts against the pool, and the emitters print the
changes from and back to the budget. It is unrestricted, since splitting again is safe: it is evidence of the budget,
not a resource used up.

**Three departures from the first design:**
- **The join returns no token.** The pool is unrestricted, so there is nothing to give back.
- **A share carries the pool's per-thread count**, `RegShare(l, f, perThread, count)`, not only its count, so the
  emitters take both ends of every change from the share's type.
- **The fit is against the pool**, 128 · Σ counts ≤ 512 · budget, not against 65,536. `setmaxnreg` draws on the CTA's
  pool, which is the threads times their entry count (§7), and the two agree only at residency 1.

**No change in the middle of a role.** FA4 and CUTLASS change counts only at role entry, and every kernel here does
too. A change mid-role would need its increase covered by a decrease that cannot depend on it: a protocol between
roles, carrying shares. That is designed when a kernel needs one.

## 4. Demand

**The floor.** The core can count part of what a role keeps live, from its typed state:
- `loadRow`'s `Loaded` row is 128 f32;
- an `F32x8` is 8;
- each ring cursor, phase register and `reg` is 1;
- a u64 value is 2.

Each operation that produces such values declares their weight. The role's floor is the largest set of declared values
live at once, plus its `reg`s.
- **What it is:** a floor, not a prediction. It misses `ptxas`'s addresses, predicates and temporaries, and `ptxas`
  may raise pressure by scheduling.
- **Example:** A3a's causal softmax has a floor of about 140. Unbounded, `ptxas` used 184; capped at 168, it fitted
  with no spills.

**Uses:**
- **An early error.** A role whose floor exceeds its count fails at generation, with both numbers.
- **The starting point for `auto`.**

## 5. Judged by `ptxas`

Generated code is compiled, and its register use read back, as a certificate after printing, as `Check.rac` is before
it:
- **Per kernel:** `ptxas -v` reports the registers and the spill stores and loads. The count must be within the
  budget, and both spill figures must be 0.
- **Per role** (kernels that change counts): `ptxas -v` reports the entry count only. So the check disassembles the
  kernel and attributes local-memory instructions (`STL`, `LDL`) to roles by their source lines (`-lineinfo`): a
  role is the block of generated code that starts with its `setmaxnreg`, to the block's end.
- **The error** names the role, its count, and its floor (the floor from step 4).
- **The user's options** are then to raise that role's count, to lower another's that has room, or to keep fewer
  values live.

**`auto`.** Optional:
1. Start each role at its floor, rounded up to 8.
2. Give the rest of the pool to the roles in proportion to their floors.
3. Compile.
4. Move registers, 8 at a time, from roles that do not spill to roles that do, until none spills or none can move.
   Each round is one `ptxas` run, 10 to 30 s for an attention kernel.
5. Cache the result by the kernel's text. A failure reports the roles' floors and the pool's size.

**Where `ptxas` runs.** NVIDIA ships no CUDA for macOS, so on the Mac it runs in the container of §6. `gpu/check.sh`
runs this check when the image is present, and says it skipped the check when it is not. The hardware session runs it
too, on the box's own toolkit.

**As built** (`gpu/toolkit/registers.py`, run by `check.sh` on every example of `encoding/`):
- **One compile per example:** the generated file through `cuda.sh` with `nvcc -std=c++17 -O2 -gencode
  arch=compute_100a,code=sm_100a -c -lineinfo -Xptxas -v`, then `cuobjdump -xelf` and `nvdisasm -g`. About 3 s for
  A3b's two kernels; the examples run in parallel with the other checks.
- **One line per kernel:** its registers, its budget from its printed bounds, and its spill stores and loads.
- **The file fails** when it has no kernel, or when `ptxas` warns (a residency above 32, say, which `ptxas` ignores).
- **A kernel fails** when its registers exceed its budget, when it spills, or when its SASS has any `STL` or `LDL`.
  The local-memory test runs on every kernel, not only those that change counts: no generated kernel means to use
  local memory.
- **A kernel that changes counts fails** when it does not enter at exactly its budget (A59), or when its `setmaxnreg`s
  are not splits of the CTA's pool at that budget:
  - every warpgroup's first change goes from the budget to its count, `.inc` up and `.dec` down;
  - every change back, the one in a block guarded by its warpgroup, goes from that count to the budget;
  - the counts fit the pool: threads/4 · Σ counts ≤ threads · budget.

  This is `Registers.split`'s rule, read from the output against the budget of the kernel's bounds. So it holds
  whoever created the pool: a pool created by a client at another count (`pool_at_other_count`) generates, and fails
  here.
- **Attribution** gives each local-memory instruction's role, as "the role at line L (`setmaxnreg…`)", or "no role".
  A role is the block that starts with a warpgroup's first change, within its kernel. The line is the last line of the
  kernel's own source that the line info named; it also names the CUDA headers' lines, which are skipped. It is
  approximate: spill code at a block's edge can carry a neighbour's line. In `softmax_starved` (below), the
  non-causal kernel's two softmax roles get 979 instructions each and 2 lie in no role; the causal kernel's get 827
  each, its correction and MMA roles 1 and 2, and 1 lies in no role.
- **The budget is restated** in the check, from the bounds: the rule of `Registers.budget`, kept in Python so the check
  needs no Raccoon run.
- **The proof that it fails what it should** is two mutants of `attention_a3b_mutants.py` whose expectation is
  `RegisterCheck` (`gpu/mutate.py`):
  - `softmax_starved`: the softmax warpgroups at 64 registers. It generates, since the counts fit the pool, and the
    check fails it, with the local-memory instructions in the softmax roles;
  - `pool_at_other_count`: a second split, of a pool a client created at residency 2.
- **Without the toolkit** `check.sh` prints "skipped: no CUDA toolkit" once, and skips both the check and those
  mutants; `cuda.sh true` is the probe.

## 6. The toolkit on a Mac

- **`gpu/toolkit/Dockerfile`:** Ubuntu 22.04 with NVIDIA's packages for CUDA 12.9: `nvcc`, `ptxas`, `cuobjdump`,
  `nvdisasm`, and the runtime and driver headers. It uses NVIDIA's `sbsa` repository on arm64 and `x86_64` elsewhere.
  Build it with `docker build -t raccoon-cuda:12.9 gpu/toolkit` (colima or Docker Desktop).
- **`gpu/toolkit/cuda.sh`:** runs a toolkit command on the repository, mounted at its own path, with its standard
  input. It never pulls the image, so without it the command fails at once. Compiling needs no GPU.

## 7. Today's kernels

The changes this design made (built 2026-10-01):
- **Bounds everywhere.** Every builder states its threads and residency to `Core.finish`, and `render` prints
  `__launch_bounds__(threads, r)`. The bounds lines, and A3b's barrier below, are the only changes to generated code:
  every other line of every example is byte-identical.
- **The residencies:**
  - **1 for every tensor-core kernel**, whose shared memory leaves room for one CTA per SM: A1, A2, P1, the decode,
    the GEMMs (`(256, 1)`), A3a (`(384, 1)`) and A3b (`(512, 1)`). The 256-thread kernels' budget is the 255 cap.
  - **32 for the one-warp SIMT kernels**, the append and the combine (`Core.warpResidency`, `(32, 32)`): the most CTAs
    an SM holds. A one-warp kernel waits on memory, and every resident warp hides some of the wait. The budget, 64, is
    above what either uses.
  - **1 for `tiledKernel`**, which no example uses: the budget it leaves, 64 at 1,024 threads, is the CTA's share of
    the SM's registers.
- **Spill checks for every kernel** (§5).
- **A3b.** `splitWarpgroups` is the `Registers` module's client: it divides the CTA's register pool and joins the shares.
  Its counts stay 192/72/56. The changes back already followed the join; a `__syncthreads()` now follows them (§3),
  one line in each of its two kernels. It has not run on hardware with that barrier.

**The bounds change the allocation.** Given a residency of 1, `ptxas` uses more of the budget where it had used
little. Every kernel still fits without spills; whether it is faster is a hardware question.

What `ptxas` reported at 5dbad99, before the bounds. These are CUDA 12.9 in the container, `sm_100a`, `-O2`;
every kernel's spill stores and loads are 0:

| Kernel | Threads | Bounds | Registers |
|---|---|---|---|
| `attention` (A1), `paged_attention` | 256 | none | 44 |
| `attention_causal` (A2), `paged_attention_causal` | 256 | none | 168 |
| `attention_pingpong` (A3a) | 384 | 384, 1 | 159 |
| `attention_pingpong_causal` | 384 | 384, 1 | 168, the budget exactly |
| `attention_a3b`, `attention_a3b_causal` | 512 | 512, 1 | 128 at entry; the roles at 192/72/56 |
| `paged_decode_g1`, `_g4`, `_g8` | 256 | none | 43 |
| `gemm_pair` | 256 | none | 56 |
| `tinygemm_pair` | 256 | none | 32 |
| `paged_append`, `paged_combine` | 32 | none | 32 |

What the register check reports with the bounds, the same toolkit and flags with `-lineinfo`; no kernel spills or has a
local-memory instruction:

| Kernel | Bounds | Budget | Registers |
|---|---|---|---|
| `attention` (A1), `paged_attention` | 256, 1 | 255 | 160 (44 before) |
| `attention_causal` (A2), `paged_attention_causal` | 256, 1 | 255 | 168 |
| `attention_pingpong` (A3a) | 384, 1 | 168 | 159 |
| `attention_pingpong_causal` | 384, 1 | 168 | 168 |
| `attention_a3b`, `attention_a3b_causal` | 512, 1 | 128 | 128 at entry |
| `paged_decode_g1`, `_g4`, `_g8` | 256, 1 | 255 | 161 (43 before) |
| `tinygemm` | 256, 1 | 255 | 55 |
| `tinygemm_pair` | 256, 1 | 255 | 40 (32 before) |
| `gemm_pair` | 256, 1 | 255 | 71 (56 before) |
| `paged_append` | 32, 32 | 64 | 32 |
| `paged_combine` | 32, 32 | 64 | 48 (32 before) |

A3b's SASS has no `STL` or `LDL`, so no role spills. Its count changes are `USETMAXREG.TRY_ALLOC.CTAPOOL` (192) and
`USETMAXREG.DEALLOC.CTAPOOL` (72 and 56) at the roles' entry, and back to 128 (`0x80`) after the join. So the pool
`setmaxnreg` draws on is the CTA's, which is what §3 models.

Two kernels sit at their limit:
- **A3a's causal kernel** at 168, exactly its budget. Any growth in its softmax spills, and §5 would say so.
- **A2's causal kernel** at 168. 256 threads leave it 255, so it has room.

## 8. Plan

1. **The toolkit container** (`gpu/toolkit`). Done with this document.
2. **The `Registers` module.** Residency and budgets, bounds in every builder, and split and join in place of
   `splitWarpgroups`' internals. Generated CUDA stays byte-identical except the bounds lines and the barrier after
   A3b's way back. **Done:**
   `gpu/encoding/Registers.rac`; `Core.withShare` and `Core.regsBack` are the emitters; the `RegPermit` is gone;
   the mutant `registers_over_pool`, and `checks/registers.rac` (two splits in sequence, and one under a uniform
   branch).
3. **The `ptxas` check in `check.sh`:** registers and spills per kernel, and per role from the SASS. A spill is a
   failure. **Done:** `gpu/toolkit/registers.py` (§5), and the mutants `softmax_starved` and `pool_at_other_count`.
4. **Floors and `auto`.**
5. **The other families' modules** (§2), one at a time.

## 9. Decisions

1. **Every linear resource family lives in its own sealed module**, and `Core.rac` is their client. The trusted base
   is those modules plus the control combinators.
2. **The user chooses per-role register counts**, as numbers or `auto`. The library emits every `setmaxnreg`.
3. **Shares exist only between the split and the join.** The changes happen at the split and after the join; there
   are none in the middle of a role.
4. **Every builder states its residency** and prints `__launch_bounds__(threads, r)`.
5. **A spill is a build error**, found by `ptxas -v` per kernel and from the SASS per role. A count over budget is an
   error too.
6. **The CUDA toolkit runs in a Linux container on the Mac** (`gpu/toolkit`).
7. **Every split ends with a CTA barrier after the way back**, so every warp holds the budget outside a split, and a
   kernel may split any number of times (§3).

**Open questions for the user:**
1. **How to check what stays trusted.** Today a module that owns a family cannot emit, its minting function is
   callable by any module, and Core could print a `setmaxnreg` through raw `asm` (§2, "The language limit").

   **A token only Core can mint** (the user's question): `Registers.pool` would take a linear token of Core's, so
   only Core could call it.
   - **It is the right pattern.** Core already gates emission so, with `Key`.
   - **It meets an import cycle.** `Registers` would import `Core` to name the token's type, and `Core` imports
     `Registers` for the pool and the shares. Raccoon refuses import cycles.
   - **A third module does not help.** The token's home module is then its only minter, and it can hand a token only
     to the callers of a public function. A token controls how many and with what, not who.

   **The remedies:**
   1. **Import cycles within a declared trusted group.** The user's pattern as stated: Core mints the token and calls
      `Registers` with it.
   2. **Exports to named modules.** `Registers.pool` exported to `Core` only.
   3. **Sealing shared with named modules** (say, `Registers.rac` and `Core.rac`). The module could then need the
      `Key`, emit its own instructions, and mint only for a builder.
   4. **Typed instructions** (`gpu/EVALUATOR.md`, step 1), with a `Check.rac` rule on the generated AST: every
      `setmaxnreg` is a warpgroup's entry change in a split, or a change back after its join, with counts that fit
      the pool. This checks Core's own emission, raw `asm` included, as a certificate of each kernel. No language
      change.
   5. **A layering in which only the top layer can render.** It likely needs contexts indexed by their kernel.
      Unexamined.

   The fourth is the likely route, since it needs no language change. The user decides; the language is unchanged
   until then.
