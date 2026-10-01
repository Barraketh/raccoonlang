# Registers as a modelled resource

Status: **design** (2026-10-01), not implemented, except the toolkit container of §6.

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
| `Registers` | the register file, per-warpgroup shares (§3) |
| `Tmem` | the allocation permit, regions, `Acc` |
| `Rings` | stage rings and their sides |
| `AccRings` | accumulator rings and their sides |
| `ScoreBuffers` | A1's exchange and A3's score buffers |
| `Staging` | TMA-store staging buffers and store sides |
| `Claims` | P2's claims and appends |
| `Pairs` | `CtaPair`, `Leader`, `LeaderOnly` |
| `Outputs` | `OOwn`, `TileOwn` |

**The trusted base.** What stays trusted is these modules plus the control combinators: the kernel builders, `split`,
`elect`, `branch`, `when`, the loops and `onLeader`. Their obligations are stated in `OBLIGATIONS.md` and reviewed.
That base is smaller than today's, which is all of `Core.rac`.

**Migration.** One family at a time, starting with registers (this document). Every example must still generate
byte-identical CUDA, apart from the changes §7 lists.

## 3. Supply

**What is known exactly:**
- **The register file:** 65,536 32-bit registers per SM.
- **The CTA's threads:** from its builder.
- **The kernel's residency `r`:** the CTAs it means to run per SM. Every tensor-core kernel here is 1, set by its
  shared memory; one-warp SIMT kernels may want more.
- **The allocation granularity:** 8 registers per thread.

**The uniform budget.** For a kernel that does not change counts, the budget is ⌊65,536 / (threads · r)⌋ rounded down
to a multiple of 8, and at most 255. Every builder prints `__launch_bounds__(threads, r)`, so `ptxas` never allocates
beyond it. A kernel can then never fail to launch for registers. At worst it spills, and §5 makes a spill an error.

**Per-warpgroup counts.** For a kernel whose roles need different counts (A3b: softmax 192, correction 72, the rest 56):
- **The user** chooses the counts as generation-time numbers on the role layout, or `auto` (§5).
- **The `Registers` module** owns the CTA's register file as a linear token, at the uniform budget.
- **The split** (A3b's `splitWarpgroups`):
  - consumes the file;
  - checks that the counts fit it (128 · Σ counts ≤ 65,536 at 512 threads);
  - emits each warpgroup's change as the first instruction of its branch;
  - gives each role a `RegShare(l, f, count)`. The role cannot change its share; the share is evidence of its count,
    for §4's check.
- **The join** consumes every share, emits each warpgroup's change back after the join barrier (decreases first), and
  returns the file.
- **No user code calls `setmaxnreg`.**

**Why this cannot deadlock:**
- An increase at the split waits only for decreases at the split. Those never wait, and they depend on nothing.
- An increase after the join waits only for decreases after the join. Those also never wait.
- There is no operation that changes a share between the split and the join. So a warpgroup cannot take back
  registers another warpgroup's first increase needs, which is A3b's deadlock.

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
  kernel (`cuobjdump -sass`) and attributes local-memory instructions (`STL`, `LDL`) to roles by their code ranges.
  The ranges are found from the generated source lines (`-lineinfo`) between a role's branch and its end.
- **The error** names the role, its count, and its floor.
- **The user's options** are then to raise that role's count, to lower another's that has room, or to keep fewer
  values live.

**`auto`.** Optional:
1. Start each role at its floor, rounded up to 8.
2. Give the rest of the file to the roles in proportion to their floors.
3. Compile.
4. Move registers, 8 at a time, from roles that do not spill to roles that do, until none spills or none can move.
   Each round is one `ptxas` run, 10 to 30 s for an attention kernel.
5. Cache the result by the kernel's text. A failure reports the roles' floors and the file's size.

**Where `ptxas` runs.** NVIDIA ships no CUDA for macOS, so on the Mac it runs in the container of §6. `gpu/check.sh`
runs this check when the image is present, and says it skipped the check when it is not. The hardware session runs it
too, on the box's own toolkit.

## 6. The toolkit on a Mac

- **`gpu/toolkit/Dockerfile`:** Ubuntu 22.04 with NVIDIA's packages for CUDA 12.9: `nvcc`, `ptxas`, `cuobjdump`,
  `nvdisasm`, and the runtime and driver headers. It uses NVIDIA's `sbsa` repository on arm64 and `x86_64` elsewhere.
  Build it with `docker build -t raccoon-cuda:12.9 gpu/toolkit` (colima or Docker Desktop).
- **`gpu/toolkit/cuda.sh`:** runs a toolkit command on the repository, mounted at its own path. Compiling needs no
  GPU.

## 7. Today's kernels

The changes this design makes:
- **Bounds everywhere.** Every builder prints `__launch_bounds__(threads, r)`. A1, A2, P1, the decode, the GEMMs and
  A3a get bounds; A3a already has them, at 384. This is the one change to generated code; behaviour is the same where
  the budget already held.
- **Spill checks for every kernel.** A1, A2 and P1 run 256 threads, so their budget is the 255 cap.
- **A3b.** `splitWarpgroups` becomes the `Registers` module's split and join. Its counts stay 192/72/56. Its output is
  unchanged: the changes back already follow the join.

What `ptxas` reports for today's examples at 5dbad99. These are CUDA 12.9 in the container, `sm_100a`, `-O2`;
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

A3b's SASS has no `STL` or `LDL`, so no role spills. Its count changes are `USETMAXREG.TRY_ALLOC.CTAPOOL` (192) and
`USETMAXREG.DEALLOC.CTAPOOL` (72 and 56) at the roles' entry, and back to 128 (`0x80`) after the join. So the pool
`setmaxnreg` draws on is the CTA's, which is what §3 models.

Two kernels sit at their limit:
- **A3a's causal kernel** at 168, exactly its budget. Any growth in its softmax spills, and §5 would say so.
- **A2's causal kernel** at 168. 256 threads leave it 255, so it has room.

## 8. Plan

1. **The toolkit container** (`gpu/toolkit`). Done with this document.
2. **The `Registers` module.** Residency and budgets, bounds in every builder, and split and join in place of
   `splitWarpgroups`' internals. Generated CUDA stays byte-identical except the bounds lines.
3. **The `ptxas` check in `check.sh`:** registers and spills per kernel, and per role from the SASS. A spill is a
   failure.
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
