# 2-CTA (`cta_group::2`) facts for the core

Status: facts note, 2026-10-01. Input to the 2-CTA design for `gpu/encoding/Core.rac` (branch `lemur_gpu`). No design
here beyond the A-number list of §5.

Sources, read from local copies outside the repository (paths below are relative to that copy). The commits are
those named, so each citation can be checked against the upstream repository:
- **FA4:** `fa4/flash_fwd_sm100.py` and its helpers (`pipeline.py`, `blackwell_helpers.py`, `tile_scheduler.py`,
  `interface.py`, `utils.py`, `mma_sm100_desc.py`) at Dao-AILab `616b0e8`. Paths are relative to the scratchpad's `fa4/`.
- **CuTe DSL** (FA4's pipeline base classes): `ptx/cutlass-repo/python/CuTeDSL/cutlass/pipeline/{sm100,sm90,helpers}.py`
  at CUTLASS `0b55a2f`, plus `fa4/cutlass_dsl/*.py` fetched at the same commit (`memory_tmem.py`, `cute_arch_mbar.py`,
  `cute_arch_nvvm_wrappers.py`, `cute_nvgpu_cpasync_copy.py`, `utils_blackwell_helpers.py`). The DSL's lowering to PTX is
  compiled MLIR and not visible. Where I give the PTX a DSL call emits, it is the C++ analogue's text, marked **inferred**.
- **CUTLASS C++:** `ptx/cutlass-repo/include/…` at `0b55a2f` (the commit `gpu/REFERENCE_CUTLASS.md` names).
- **PTX ISA 9.4:** `ptx/ptx.txt`, cited by section. The Layout A figures (§9.7.18.10.5.1, Figures 211–212) are images
  only and were not read.

"Inferred" marks a conclusion I drew rather than read. "Unknown" marks what the sources do not settle.

## Summary

**FA4's 2-CTA schedule** (hd 128, non-causal). A 2×1 cluster is one CTA pair, and each CTA runs the 16-warp
single-CTA program with two 128-row query tiles, so a pair covers 512 rows. Only the even CTA's MMA warp issues: M = 256
MMAs over the pair, in A3's tile-by-tile order. Each CTA loads its own Q rows, 64 keys of each K block and 64 head-dim
columns of each V block into a 6-stage ring of 16 KB, and keeps S, P and Ô for its own rows in its own TMEM at the
1-CTA column map. Softmax, correction and the epilogue run in both CTAs. Their signals arrive on barriers in the leader,
and the leader's commits multicast "S ready", "O final" and "stage free" to both. Static-persistent by default. No
cluster barrier at exit, only a TMEM-dealloc handshake.

**The five facts that most constrain a typed encoding:**
1. **Asymmetric roles, lockstep sequences.** Only the even CTA issues MMAs and commits and arms the TMA full barriers.
   Both CTAs run every other role. Each CTA's loader and the leader's MMA thread walk one tile and stage sequence, or
   the pair deadlocks.
2. **Waits are local; arrivals cross CTAs three ways.** A peer TMA's `complete_tx` on the leader's barrier, a multicast
   commit on both CTAs' barriers, and a `mapa` + `mbarrier.arrive` on the leader's (§9.7.15.16.19: `try_wait` is
   own-CTA only). TMA barriers expect both CTAs' bytes, P-ready counts both CTAs' threads (512), commit-fed barriers
   keep count 1 per CTA.
3. **TMEM is a pair resource.** One `.cta_group` per kernel makes alloc, dealloc and relinquish `::2`: collective over a
   warp in each CTA, possibly blocking until the peer joins (§9.7.18.5 Table 55). Dealloc needs a cross-CTA handshake,
   and no CTA may exit while the peer can still touch its shared memory, barriers or TMEM (§2.2.2).
4. **One address names both CTAs.** One descriptor per operand, one TMEM address for D and A, and commits to "the same
   offset". Both CTAs need identical shared-memory, barrier and TMEM layouts. PTX says only that B may lie in the peer;
   the same-offset split of A, B and D is CUTLASS's (**inferred**).
5. **The memory model covers the pair less than one CTA.** §8.9.5 orders async-to-async accesses only "by the same
   thread block", so O1/O2 do not carry over when one CTA's TMA feeds the other's MMA (**unknown**). FA4 and CUTLASS
   use `.cta`-scope remote arrives and waits, and FA4's forward kernel emits no `tcgen05.fence::*_thread_sync`.

## 1. FA4 with `use_2cta_instrs`

### 1.1 The configuration

- Selection (`interface.py` 1080–1094). 2-CTA is on for sm_10x/11x when all of these hold: not disabled, non-causal,
  not local, no split-KV, no varlen Q, no block sparsity, page size `None` or 128, hd and hd_v padded to 128 (or hd
  192), `seqlen_q > 2·tile_m = 256`, and either no GQA packing or a tile divisible by it. `FA_DISABLE_2CTA=1` turns it
  off, and so does a CUDA 12 toolkit (`utils.py` 65, 69–95: an 18% codegen regression).
- Tiles: `tile_m = tile_n = 128` (`interface.py` 355), `q_stage = 2` when `seqlen_q > 128` (385).
- **Persistence is not optional through the interface.** Dense non-causal sets `is_static_persistent = True`
  (`interface.py` 1363–1375), and CLC is off for dense non-causal (1121). So the default is
  `StaticPersistentTileScheduler` (`flash_fwd_sm100.py` 291–303). The constructor takes `is_static_persistent`, and with
  `False` it uses `SingleTileScheduler`. §1.10 says what changes.
- Cluster `(2, 1, 1)` (`flash_fwd_sm100.py` 211, 569–572), `cta_group = TWO` for the MMAs and the TMA loads (541, 639).
- Register split (tuning key `(True, False, 128, False)`, line 106): softmax 184, correction 80, others
  512 − 2·184 − 80 = 64.

### 1.2 What each CTA of the pair holds

`v = blockIdx.x mod 2` is the CTA's coordinate in the pair, and `v = 0` is the leader (`flash_fwd_sm100.py` 955–959).
This equals `%cluster_ctarank` for a `(2,1,1)` cluster tiling x (**inferred**). Work tile `m` covers 512 query rows.
Tile `s` of CTA `v` is the 128-row block `(m·q_stage + s)·2 + v` (2724, 2844).

| | Per CTA | Source |
|---|---|---|
| MMA tilers | QK: M = 256 (both CTAs), N = 128 keys, K = 128 hd. PV: M = 256, N = 128 hd_v, K = 128 keys | 207–208 |
| Q | its own 128 rows × 128 hd, for each of 2 stages: 2 × 32 KB, loaded once per tile | `sQ_layout` 576; `gQ` 1532–1538; `partition_A` |
| K stage | keys `64v … 64v+63` of the block × all 128 hd (half of N of QK), 16 KB | `tSgK = thr_mma_qk.partition_B(gK)` 1530 |
| V stage | all 128 keys × hd columns `64v … 64v+63` (half of N of PV, MN-major), 16 KB | `tOgV` 1531 |
| K/V ring | one ring, K and V alternating, `kv_stage = (224 KB − (64 + 64) KB) / 16 KB = 6` stages | 404–408 (**inferred** arithmetic, bf16 O) |
| O staging | 2 × 128 × 128 bf16 = 64 KB | 398, 574 |
| TMEM | all 512 columns. S0 at 0, S1 at 128, Ô0 at 256, Ô1 at 384. P_s overlays S_s + 64 (64 columns of packed bf16). Lanes 0–127 are this CTA's 128 rows of that tile | 351–364, 1149–1168 |
| Query tiles | `q_stage = 2` per CTA, so 4 × 128 rows per pair and per work tile | 184–185, 202–204 |

- The per-CTA halves come from the 2-SM MMA traits. A's M rows, B's N columns and C's M rows split in two halves by
  CTA: `ThrID = Layout<_2>`, A `(2,(M/2,K))`, B `(2,(N/2,K))`, C `(2,(M/2,N))`
  (`include/cute/atom/mma_traits_sm100.hpp` 1160–1184 SS, 1291–1315 TS). For M/2 = 128 the TMEM layout is "4x1": CTA
  `v`'s lanes 0–127 hold rows `128v…`, N consecutive columns (`mma_traits_sm100_frag.hpp` 192–201).
- FA4 does not read the TMEM base. It assumes column 0, because it always allocates 512 columns ("This is a fake
  tensor", 1152–1153).
- The K/V stage is half the 1-CTA stage (32 KB → 16 KB), so the same 96 KB holds 6 stages instead of 3
  (**inferred** from the same formula with `cta_group_size = 1`).

### 1.3 Who issues

- Only the leader's MMA warp issues: `if process_tile and is_leader_cta:` (1851). The peer's MMA warp only allocates
  and frees TMEM, and walks the tile loop without issuing (1321–1351).
- Instruction forms (`blackwell_helpers.py` 1292–1362, 397–620):
  - S: `tcgen05.mma.cta_group::2.kind::f16 [tmem_acc], a-desc, b-desc, idesc, p`, 8 instructions of K = 16;
  - PV: `tcgen05.mma.cta_group::2.kind::f16 [tmem_acc], [tmem_a], b-desc, idesc, p`, 8 of K = 16;
  - each asm block runs its own `elect.sync _|leader_thread, -1` and issues under `@leader_thread`;
  - one address per operand, the leader's.
- **A of PV is P in tensor memory.** The leader passes one TMEM address, P_s = S_s + 64 (1164–1168). Under
  `cta_group::2` each CTA supplies its own 128 rows from its own TMEM at that address: the TS traits split A's rows by
  CTA (`mma_traits_sm100.hpp` 1312–1313) (**inferred**: PTX does not state where A's rows come from, §3.1).
- Idesc: M = 256 is encoded as `M >> 4 = 16` in bits 24–28 (`mma_sm100_desc.py` 141–158; PTX §9.7.18.4.2).
- The MMA order is A3's, tile by tile (1851–1990). The next S_s is issued after PV_s with no barrier, by the pipelined
  pair "A reads → D writes" (comment 1933–1935).
- The PV of each tile is split at 3/4 of K (`split_P_arrive = 96`, 190–194). The first 6 K-steps are issued after
  `P_full_O_rescaled`. Then, inside the same asm block, the thread spins `mbarrier.try_wait.parity.shared::cta` on
  `P_full_lastsplit` and issues the last 2 (`blackwell_helpers.py` 538–615; `flash_fwd_sm100.py` 1907–1913).

### 1.4 The barriers

"Count" is the init count in each CTA, from the group sizes of 983–1009. Every barrier exists in both CTAs (one
`SharedStorage`, 766–783). "Used copy" is the copy that anyone waits on.

| Barrier (FA4 name) | Count | Used copy: who waits | Who arrives, and how | Tx |
|---|---|---|---|---|
| Q full, per stage (`mbar_load_Q`) | 1 | leader: MMA warp | leader's load warp `arrive.expect_tx`. Both CTAs' Q TMA `complete_tx` on the **leader's** copy (`cp.async.bulk.tensor…cta_group::2`; **inferred**, §1.6) | 2 × 32 KB = 64 KB (`tma_copy_bytes × cta_group_size`, 636) |
| Q empty, per stage | 1 | each CTA: its load warp | leader's MMA commit, multicast to both | — |
| K/V full, per stage (`mbar_load_KV`) | 1 | leader: MMA warp | leader's load warp `arrive.expect_tx`. Both CTAs' TMAs complete on the leader's copy (**inferred**, §1.6) | 2 × 16 KB = 32 KB |
| K/V empty, per stage | 1 | each CTA: its load warp | leader's MMA commit, multicast to both | — |
| S full (`mbar_S_full_P_full_O_rescaled`, full half) | 1 | each CTA: that tile's softmax warpgroup | leader's commit after `S_s`, multicast mask `0b11` | — |
| P full and O rescaled (same array, empty half) | 512 = (128 softmax + 128 correction) × 2 CTAs | leader: MMA warp | every softmax and correction thread of both CTAs, remote `mbarrier.arrive` at the leader's address (`mapa`), one per phase each | — |
| P last split (`mbar_P_full_lastsplit`, full half) | 8 = 4 softmax warps × 2 CTAs | leader: MMA warp, inline in the PV asm | one elected lane per softmax warp of both CTAs, remote arrive at the leader | — |
| O final (`mbar_O_full`, full half) | 1 | each CTA: correction warpgroup | leader's commit after the tile's last PV, multicast `0b11` | — |
| O full, empty half | 256 | none | none (no `consumer_release` on `pipeline_o_acc`; 1998–2001) | — |
| Softmax stats (`mbar_softmax_stats`) | 128 / 128 | local | local; plus a named barrier per (stage, warp) of 64 threads (1090–1101) | — |
| O to epilogue (`mbar_O_epi`) | 128 / 32 | local | local (1103–1110) | — |
| TMEM dealloc (`tmem_dealloc_mbar`) | 32 | each CTA: its MMA warp | the **peer's** MMA warp, 32 lanes, remote arrive (§1.8) | — |
| `TmemPtr` named barrier | 416 threads (MMA + 8 softmax + 4 correction warps) | local | local, used twice: alloc result, and before free | — |

Pipeline classes and masks (CuTe DSL `pipeline/sm100.py`):
- **`PipelineTmaUmma`** (Q, K/V).
  - The full barrier's count is the producer group, one thread.
  - The leader arms it with `arrive_and_expect_tx(tx_count)` and the peer does not (`is_leader_cta`; FA4 override
    `pipeline.py` 341–377; base 343–378).
  - Release is `tcgen05.commit` with `consumer_mask = producer_mask` (309). That mask ORs the A and B multicast masks
    of this CTA and its peer (101–155), which is `0b11` for a `(2,1)` cluster (**inferred** evaluation).
- **`PipelineUmmaAsync`** (S/P, O).
  - Commit mask from `_compute_tmem_sync_mask` (603–624): both CTAs of the pair.
  - The consumer arrives at `rank // 2 · 2`, the leader (626–641, 725).
- **`PipelineAsyncUmma`** (P last split).
  - The producer arrives at the leading rank (397–412, 553).
  - The consumer mask is self | peer (435–466, 557).
- `MbarrierArray.arrive` (`helpers.py` 356–401) dispatches:
  - a TCGen05Mma arrive becomes a commit with mask and `cta_group`, under `elect_one` (433–456);
  - an AsyncThread arrive becomes `mbarrier_arrive(ptr, dst_rank)`, i.e. `mapa` then `mbarrier.arrive` with scope
    **`.cta`** by default (`cute_arch_mbar.py` 414–462). The docstring says cluster scope is "formally" needed for
    cross-CTA ordering but keeps `.cta` for speed (437–441).
- The C++ analogue of the commit is `tcgen05.commit.cta_group::2.mbarrier::arrive::one.shared::cluster.multicast::cluster`
  (`barrier.h` 907–921). That the DSL emits the same is **inferred**.

### 1.5 The S-ready and P-ready handshakes

- **S ready.** The leader issues `S_s` and then `pipeline_s_p_o.producer_commit_w_index(s)` (1876, 1946). The commit
  arrives once on S full in each CTA. Each CTA's softmax warpgroup for tile `s` waits on its own copy (2467), loads S
  from its own TMEM, and computes.
- **P ready.** Per block, each softmax thread:
  1. stores 3/4 of P (`tcgen05.st`);
  2. waits `tcgen05.wait::st` (`fence_view_async_tmem_store`, `cute_arch_nvvm_wrappers.py` 1265–1308);
  3. arrives remotely on the leader's `P_full_O_rescaled[s]` (2541–2545);
  4. stores the last quarter, `wait::st`, `__syncwarp`;
  5. one lane per warp arrives remotely on the leader's `P_full_lastsplit[s]` (2547–2551).

  Each correction thread rescales Ô in its own TMEM (`tcgen05.ld/st`, then `wait::st`, 2889–2938) and arrives
  remotely on the same `P_full_O_rescaled[s]` (2706). Before its tile loop, it releases each stage once (2606–2609),
  which supplies its share of the first phase. So the leader's MMA thread waits for 512 arrivals: both CTAs' P (3/4)
  and both CTAs' rescales. Inside the PV asm it then waits for 8 arrivals: both CTAs' last quarter.
- **Fences.** FA4's forward kernel emits no `tcgen05.fence::before_thread_sync` or `::after_thread_sync` anywhere
  (`grep fence flash_fwd_sm100.py`: only `wait::st` and `fence.proxy.async.shared`). Whether the DSL inserts them
  implicitly is **unknown**. The waits come from `mbarrier_wait` with no `.sem`/`.scope`, so default `.acquire.cta`
  (`cute_arch_mbar.py` 286–313; **inferred** that NVVM keeps the default).

### 1.6 The K/V and Q pipelines

- Each CTA's load warp:
  - waits its own empty barrier;
  - if leader, arms the full barrier with both CTAs' bytes;
  - issues its own half with the `cta_group::2` TMA atom (`CopyBulkTensorTileG2SOp(cta_group)`, 639; load path
    3255–3292; `load_Q` 3210–3219).
- The barrier pointer passed is the CTA's own `full[s]`. The DSL lowers the TMA atom to `TiledTmaLoadEnum.sm_100_2sm`
  (`cute_nvgpu_cpasync_copy.py` 205–212), and its PTX is not visible. The C++ atom `SM100_TMA_2SM_LOAD_2D`
  (`copy_sm100_tma.hpp` 45, 78–102) issues
  `cp.async.bulk.tensor.2d.cta_group::2.shared::cluster.global.mbarrier::complete_tx::bytes` with the barrier address
  ANDed with `0xFEFFFFFF`, "so that the transaction bytes will update CTA0's barrier". That FA4 completes on the leader's
  copy is **inferred** from that analogue and from only the leader arming.
- There is no TMA multicast: `tma_partition(…, 0, make_layout(1), …)` ("no multicast", 1556–1569).
- **Release.** After the leader's MMAs consume a stage, `pipeline_kv.consumer_release` issues one multicast commit,
  which arrives on `empty[s]` in both CTAs (count 1 each). K_i is released after both tiles' `S_i`, and V_{i−1} after
  both tiles' `PV_{i−1}` (1879, 1920–1923, 1949, 1990). Q is released at the end of the tile (1956–1957).
- Load order per tile: K₀, Q₀, Q₁, V₀, then K_i, V_i (1626–1661).
- **Fresh barriers.** Producers start at parity 1 on fresh empty barriers: `q_producer_phase = 1` (1500), and the
  `make_pipeline_state(Producer)` phase is 1 (`pipeline.py` 86–95; CuTe `helpers.py` `make_pipeline_state`). FA4 relies
  on a parity-1 wait on a fresh barrier succeeding (`MODELS.md` §1.2).

### 1.7 Initialization

1. Every pipeline is created with `defer_sync=True`. `MbarrierArray.mbarrier_init` initializes every array from warp
   0's elected lane (`helpers.py` 330–354). The TMEM dealloc barrier is initialized by the MMA warp's elected lane,
   followed by `mbarrier_init_fence` (`memory_tmem.py` 283–301, called from the allocator constructor,
   `flash_fwd_sm100.py` 973–981).
2. `pipeline_init_arrive(cluster_shape_mn=cta_layout_vmnk, is_relaxed=True)` (1131) runs, in every thread,
   `fence.mbarrier_init.release.cluster` then `barrier.cluster.arrive.relaxed` (`helpers.py` 1147–1169). The code's
   comments on the two branches are swapped: "relaxed" is commented "Fences memory operations".
3. `pipeline_init_wait(cluster_shape_mn=…)` (1206) is `barrier.cluster.wait` (`helpers.py` 1173–1188). Whether the DSL
   adds `.aligned` is **unknown** (`cluster_arrive_relaxed(aligned=None)`, `cute_arch_nvvm_wrappers.py` 1040–1072).
   This matches the PTX example "Release local barrier state via generic proxy" (§9.7.15.4).
4. **TMEM allocation.**
   - After the cluster wait, the MMA warp of each CTA runs
     `tcgen05.alloc.cta_group::2.sync.aligned.shared::cta.b32 [tmem_holding_buf], 512` (`tmem.allocate`, 1324;
     `memory_tmem.py` 466–507).
   - The address goes to each CTA's own `tmem_holding_buf`, at the same offset in both (same `SharedStorage`).
   - Each CTA learns its base by `wait_for_alloc`, a named-barrier `arrive_and_wait` over the 416 threads (509–520),
     then a shared load (`retrieve_ptr`, 522–537).
   - Softmax and correction warps do the same (1384–1385, 1429–1430).
   - FA4 then ignores the value and uses column 0 (1152).

### 1.8 Teardown

- **Load warp.** `pipeline_kv.producer_tail` waits every K/V stage's empty barrier in its own CTA
  (`PipelineAsync.producer_tail`, `sm90.py` 338–356). Then one more Q empty wait (1697–1701). These waits observe the
  leader's last release commits, which are also the commits of the MMAs that read this CTA's shared memory.
- **MMA warp.** `relinquish_alloc_permit` (`cta_group::2`), then the `TmemPtr` named barrier `arrive_and_wait`, which
  waits for this CTA's softmax and correction warps to finish their loops (1348–1351, 1421, 1457). Then
  `tmem.free` (`memory_tmem.py` 601–660), in which:
  1. all 32 lanes `mapa` + `mbarrier.arrive` (`.cta` scope) on the **peer's** dealloc barrier;
  2. they wait parity 0 on their own;
  3. they run `tcgen05.dealloc.cta_group::2 … 512`.
- **No tails for the MMA side.** FA4 has no producer tail for `pipeline_s_p_o` or `pipeline_o_acc` (1998–2001). The
  correction warps' last release of `P_full_O_rescaled` is one phase ahead of the MMA's last acquire, so 256 remote
  arrivals (both CTAs) land on the leader's barrier and are never waited on.
- **No cluster barrier before exit, no `mbarrier.inval`.**
- Whether the peer's final remote arrivals are guaranteed to land before the leader exits is **unknown**. They precede,
  in each peer thread's program order, its named-barrier arrive. That precedes the peer MMA warp's remote arrive on the
  leader's dealloc barrier, which the leader waits for before it deallocates and exits. The chain is named barrier plus
  `.cta`-scope remote arrives.
- The epilogue warp ends with `cp.async.bulk.wait_group.read`, not a full wait (3134–3148).

### 1.9 The epilogue

Each CTA stores its own 128 rows of each tile from its own TMEM:
- the correction warpgroup reads Ô (`tcgen05.ld`) after its own `O final` wait (2757), scales, and writes `sO`
  (`correction_epilogue`, 2941–);
- the epilogue warp TMA-stores `gO` sliced to `mma_tile_coord_v` (2654, 3127–3148);
- `epi_tile = (m_block_size, hd_v)` is "per-CTA (not full 2CTA) since each CTA writes its own O portion" (573–574).

### 1.10 What persistence changes

- **Static persistent** (FA4's default):
  - grid = `min((SMs/2)·2, 2·tiles)` CTAs, x only (`tile_scheduler.py` 403–413);
  - the cluster's first tile is `%clusterid.x`, advancing by `%nclusterid.x` (`cluster_dim()` is `nclusterid`,
    `cute_arch_nvvm_wrappers.py` 453–463; scheduler 392–434);
  - both CTAs of a pair compute the same tile sequence from `%clusterid` (**inferred**: lockstep by construction);
  - barrier phases carry across tiles; Q is reloaded per tile after its release (1956–1957);
  - the first PV of a tile waits on the correction warps' release from the previous tile's epilogue (comment
    1897–1899);
  - `O final` is needed because the softmax signal does not imply that the next tile's first S has completed
    (1980–1985).
- **Non-persistent** (`is_static_persistent=False` and no CLC, so `SingleTileScheduler` with `use_cluster_idx`):
  - `num_block = ceil(seq / 512)`, grid x = `2·num_block` (713, `tile_scheduler.py` 283–300);
  - the tile is `%clusterid` (275–280), one tile per cluster;
  - the barrier protocol is unchanged.

### 1.11 Paged K/V (for later)

- 2-CTA allows paging only with page size 128 = `n_block` (`interface.py` 1088) and TMA K/V.
- Each CTA reads `mPageTable[batch, n_block]` itself and loads its half of that page (1622–1661,
  `tXgX[None, 0, page_idx]` 3291–3292).
- So both CTAs read the same page-table entry independently (**inferred**: no exchange between them).

## 2. CUTLASS 2-SM GEMM (C++)

The kernel is `include/cutlass/gemm/kernel/sm100_gemm_tma_warpspecialized.hpp` (K). The pipelines are in
`include/cutlass/pipeline/sm100_pipeline.hpp` (P100) and `sm90_pipeline.hpp` (P90), and the arrive helpers in
`include/cutlass/arch/barrier.h` (B).

- **Leader.** `cta_coord_v = %cluster_ctarank mod 2`, and the leader is `cta_coord_v == 0` (K 425–430). Only the
  leader runs `collective_mainloop.mma` and commits the accumulator (K 762–772).
- **Mainloop pipeline `PipelineTmaUmmaAsync`.**
  - Full: count 1 (P100 559–573). Armed only by the leader's elected load lane (`is_leader`, K 465) with
    `TmaTransactionBytes`, which is both CTAs' A and B bytes. The comment reads "Only one thread issues the TMA and
    updates the barriers in a 2SM MMA, adjust bytes accordingly" (`sm100_mma_warpspecialized.hpp` 237–240; arming
    P90 530–541).
  - Both CTAs' TMAs complete on the leader's copy via the cleared peer bit (`copy_sm100_tma.hpp` 45, 78–102).
  - Empty: count `cx/ax + cy/ay − 1`, which is 1 for a 2×1 cluster (P100 565–570).
  - Release: `umma_arrive_multicast_2x1SM(empty[s], block_id_mask_)` (P100 740–761, B 907–921), with
    `calculate_multicast_mask<kRowCol>` (P100 55–91). For 2×1 that mask is both CTAs. One elected lane issues the
    commit.
- **Accumulator pipeline `PipelineUmmaAsync<…, AtomThrShape 2×1>`.**
  - Full: count 1. The leader commits with `umma_arrive_multicast_2x1SM(full[s], tmem_sync_mask_)`, where the mask is
    both CTAs of the pair (`calculate_umma_peer_mask`, P100 94–113, 151–161, 260–270).
  - Each CTA's epilogue waits on its own full barrier.
  - Empty: count `2 · NumEpilogueThreads = 256` (K 529–530).
  - Release: every epilogue thread of both CTAs runs `umma_arrive_2x1SM_sm0`, i.e.
    `mbarrier.arrive.shared::cluster.b64 _, [addr & 0xFEFFFFFF]`. That is the leader's copy, with no `mapa`, default
    `.release.cta` (B 966–980; P100 272–277). It runs after the last `tcgen05.ld` and `tcgen05.wait::ld`, with no
    `tcgen05.fence::before_thread_sync` (`sm100_epilogue_tma_warpspecialized.hpp` 884–890).
  - Only the leader's MMA waits on the empty barrier (`producer_acquire`, `sm100_mma_warpspecialized.hpp` 678).
- **Initialization.**
  - Each pipeline's `init_barriers` is run by a designated warp (`initializing_warp`, K 467, 531). Every thread then
    runs `fence.mbarrier_init.release.cluster` (B 771–783).
  - `pipeline_init_arrive_relaxed` is `barrier.cluster.arrive.relaxed.aligned` (K 580; P90 1395–1403;
    `cute/arch/cluster_sm90.hpp` 51). The masks are computed in between (K 605–606).
  - `pipeline_init_wait` is `barrier.cluster.wait.aligned` (K 615; P90 1382–1390; `cluster_sm90.hpp` 69).
  - Producers start at phase 1 (`make_producer_start_state`, P90 270–277).
- **TMEM.**
  - `Allocator2Sm` (`cute/arch/tmem_allocator_sm100.hpp` 146–229): `tcgen05.alloc/dealloc/relinquish_alloc_permit
    .cta_group::2`.
  - Its documented preconditions: "Both CTAs _must_ provide the exact same dst_ptr", "The 2 warps from participating
    CTAs have the same logical warp ID", one fully active warp, the same warp for every allocation (153–166, 186–196).
  - The MMA warp of each CTA allocates 512 columns, `__syncwarp`s, and arrives on a named barrier with the epilogue
    warps. The epilogue `arrive_and_wait`s, then reads the address from shared memory (K 726–731, 869–874).
- **Producer tails.**
  - `load_tail` → `producer_tail`: waits every stage's empty barrier in its own CTA (`sm100_mma_warpspecialized.hpp`
    633–641; P90 466–473). This "Prevents early exit of producer blocks in Cluster" (P90 462–463).
  - Accumulator: the leader only, after the loop, `accumulator_pipeline.producer_tail` waits every accumulator stage's
    empty barrier, i.e. both CTAs' epilogue releases (K 786–790; P90 1147–1152).
- **TMEM handshake before dealloc.** `ClusterBarrier tmem_dealloc`, count `NumMMAThreads = 32`, initialized in each
  CTA by the MMA warp (K 559–566).
  1. Relinquish (K 784).
  2. The leader runs its accumulator `producer_tail`.
  3. The follower's 32 lanes arrive on the leader's barrier: `mapa` + `mbarrier.arrive.shared::cluster`, default
     `.release.cta` (B 494–513; K 794).
  4. The leader waits on its own (K 795), then its 32 lanes arrive on the follower's (K 796).
  5. The follower waits on its own (K 795).
  6. Both run `tcgen05.dealloc.cta_group::2` (K 804).

  So the follower deallocates only after the leader has seen both epilogues release every accumulator, and the leader
  only after the follower's MMA warp has finished. There is no cluster barrier at exit.
- **Fences.** CUTLASS emits no `tcgen05.fence::after_thread_sync` after the full-barrier wait. That is already noted
  for 1-SM in `REFERENCE_CUTLASS.md` §6 and is unchanged for 2-SM.

## 3. PTX 9.4 semantics

### 3.1 `tcgen05.mma.cta_group::2`

- **Issue.** "Issue from a single thread from the CTA-Pair". When the current CTA issues, the peer "should be active
  and should not have exited" (§9.7.18.5 Table 55). Either CTA may issue. Even-issues is a CUTLASS/FA4 convention.
- **Pair.** Two CTAs whose `%cluster_ctarank` differ only in the last bit form a pair. "Even" means last bit 0
  (§9.7.18.5.1, §9.7.18.5.2).
- **Operands.**
  - The operation "is performed on the Tensor Memory of the executing thread's CTA and its peer CTA" (§9.7.18.10.10.1).
  - B is "in Shared Memory of the current CTA and optionally in peer CTA" (§9.7.18.10). A is "in either Tensor
    Memory or Shared Memory", and the text does not say whose for the second half of M.
  - That one descriptor addresses the same offset in both CTAs, and that A's rows 128–255 come from the peer, is
    **inferred** from CUTLASS (single descriptor per operand; `mma_traits_sm100.hpp` A/B/C layouts). The PTX text does
    not state it (**unknown** in PTX).
- **D and tensor-memory A.** M = 256 with `::2` is Layout A, datapath "4x1", lane alignment 0 (§9.7.18.10.5 table,
  §9.7.18.10.5.1; the figures are images). Each CTA's TMEM holds its 128 rows at the same column address
  (**inferred**, CUTLASS `mma_traits_sm100_frag.hpp` 192–201).
- **Shapes** for `kind::f16`, `::2`, dense: M ∈ {128, 256}, N = 16…256 in steps of 16, K = 16 (§9.7.18.2.1 Table 48).
- **Idesc.** M field bits 24–28 = M >> 4 (§9.7.18.4.2).
- **Disable-output-lane** has 8 elements for `::2` and 4 for `::1` (§9.7.18.10.10.1).
- **Shared-memory accesses** are async proxy and outside the pipelining rules (§9.7.18.6.5).

### 3.2 `tcgen05.alloc`, `dealloc`, `relinquish_alloc_permit` `.cta_group::2`

- One warp in each CTA of the pair must execute it, collectively. "The first warp to perform the operation could block
  until the second warp in the Peer CTA also performs the operation" (§9.7.18.5 Table 55; §9.7.18.7.1).
- The issuing warp "must make sure that peer CTA is launched and its warps eventually participate" (§9.7.18.7.1).
- **Address.** Alloc writes it into the issuing CTA's own shared memory at `dst`, which must be in the `.shared::cta`
  window (§9.7.18.7.1). So each CTA's warp gets the address in its own `dst`. Whether the two addresses are equal is
  **unknown** in PTX. CUTLASS requires equal `dst_ptr` (§2).
- **Dealloc.**
  - "Issuing warp and peer CTA warp must synchronize Tensor Memory accesses before attempting to collectively
    deallocate", and dealloc may block until the peer's warp joins (§9.7.18.7.1).
  - Tables 56–57 (§9.7.18.5): "it suffices to ensure that there are no concurrent Tensor Memory accesses from the Peer
    CTA"; warps may exit right after dealloc.
  - Ordering a cluster barrier and dealloc differently in the two CTAs can hang, because dealloc may or may not block.
  - All TMEM must be deallocated before the kernel exits (§9.7.18.1.2).
- Ownership of an exclusive `::2` allocation is joint (§9.7.18.7.1). Relinquish forbids later alloc by the CTA
  (§9.7.18.7.1).

### 3.3 `tcgen05.commit.cta_group::2.mbarrier::arrive::one.shared::cluster.multicast::cluster [b], ctaMask`

- **Tracks** all prior asynchronous `tcgen05` operations with `.cta_group::2` issued by the executing thread: `mma`,
  `cp`, `shift` (§9.7.18.12.1, §9.7.18.6.2.1.1). These include their accesses to the peer's TMEM and shared memory
  (**inferred**: the operation is one instruction).
- **Arrives.** On completion, one arrive-on of count 1, "the scope of the arrive-on operation is the cluster scope". It
  goes to the barrier at the same offset in each CTA whose `%cluster_ctarank` bit is set in `ctaMask` (16-bit by
  default) (§9.7.18.12.1).
- **Address.** `b` must be in the `.shared::cluster` window. A `.shared::cta` address is in that window (§5.1.7).
- **Proxy.** It accesses the barrier through the generic proxy (§9.7.18.12.1).
- **Fence.** It implicitly performs `tcgen05.fence::before_thread_sync` (§9.7.18.6.4.2).
- Whether the multicast arrivals are simultaneous is **unknown** (not stated). No pair orders two commits
  (§9.7.18.6.2), as for `::1`.

### 3.4 `tcgen05.ld` / `st` / `wait` and the fences, in a `::2` kernel

- **Own CTA only.** "The threads of the CTA can perform the loads and stores to the Tensor Memory of the CTA"
  (§9.7.18.8). A warp "can access only 1/4 of the Tensor Memory of the current CTA" (Table 55). So each CTA reads only
  its own TMEM. Warp `w mod 4` gets lanes 32·(w mod 4)… (§9.7.18.8.1). `ld`/`st`/`wait` have no `.cta_group`.
- **Fences across CTAs.**
  - `tcgen05.fence::before/after_thread_sync` "compose with execution ordering instructions across a thread scope"
    (§9.7.18.11.1), including mbarrier instructions (§9.7.18.6.3).
  - The canonical cross-thread patterns use `mbarrier.try_wait.relaxed.cluster` and `mbarrier.arrive.relaxed.cluster`
    with the fences (§9.7.18.6.4.4, Examples 1–2).
  - Nothing in §9.7.18.6 restricts the threads to one CTA.
  - So a peer's `tcgen05.ld` after the leader's MMAs is ordered by: leader `mma`; multicast commit (implicit
    `before_thread_sync`, cluster-scope arrive); the peer's wait on its own copy; `tcgen05.fence::after_thread_sync`;
    `ld` (**inferred** from Example 2 extended across CTAs).
- **Opposite direction** (the peer's `st` before the leader's MMA): `st`; `wait::st`;
  `tcgen05.fence::before_thread_sync`; remote arrive; the leader's wait; `fence::after_thread_sync`; `mma`
  (**inferred** from Example 1 across CTAs, with `st` for `ld`).
- **Pipelines.** Instructions issued by different warps are never pipelined (§9.7.18.6.2).

### 3.5 `cp.async.bulk.tensor` with `.cta_group::2` and multicast

- **Barrier.** With `::2`, "the mbarrier object mbar can be in shared memory of either the same CTA as the shared memory
  destination dstMem or in its peer-CTA". With `::1` it must be in the destination's CTA (§9.7.10.28.5.3). A remote
  barrier requires `.dst = .shared::cluster` ("using .shared::cta … will not signal the remote barrier", ibid.).
- **Peer address.** PTX documents `mapa` for mapping an address to another CTA (§9.7.10.26, §5.1.7). CUTLASS's AND
  with `0xFEFFFFFF` is undocumented in PTX (**unknown**, as `REFERENCE_CUTLASS.md` §2 already says). The ISA's own
  example passes a `[peerMbar]` (§9.7.10.28.5.3, Examples).
- **Bytes.** Each copy performs one complete-tx of the bytes it copied, on completion, with `.release` at `.cluster`
  scope (ibid.). So the leader's barrier receives both CTAs' copies' bytes. Its expect-tx must be their sum. A peer's
  complete-tx may precede the leader's expect-tx, and the tx-count may go transiently negative (§9.7.15.16.6;
  `MODELS.md` §1.2 table range).
- **Multicast** (`.multicast::cluster`, `ctaMask`). The same box goes to the same offset in each destination CTA.
  - With `::1` each destination's barrier at mbar's offset is signalled.
  - With `::2` the signal goes "either to the destination CTA or its peer-CTA based on the `%cluster_ctarank` parity
    of the shared memory where the mbarrier object mbar resides" (§9.7.10.28.5.3).
  - FA4 and a 2×1 CUTLASS GEMM use no multicast (§1.6; `REFERENCE_CUTLASS.md` §3).
- **Proxy.** The barrier is accessed through the generic proxy, and completion carries an implicit generic-async proxy
  fence (§9.7.10.28.5.3, §9.7.10.28.2).

### 3.6 `mbarrier` at `.shared::cluster` addresses, and `mapa`

- **Support** (§9.7.15.16.11):
  - `arrive`, `arrive_drop`, `expect_tx` and `complete_tx` are supported on `.shared::cluster` addresses;
  - "other mbarrier operations": not supported. That includes `init`, `inval`, `test_wait` and `try_wait`.
- **Waits are local.** `try_wait`/`test_wait` take only `.shared{::cta}`: "If the address … does not fall within the
  address window of .shared::cta … undefined" (§9.7.15.16.19). This confirms that waits cannot target a remote
  barrier.
- **Remote arrive** (§9.7.15.16.16):
  - form: `mbarrier.arrive{.sem.scope}.shared::cluster.b64 _, [addr]{, count}`, which cannot return a state (`_`
    mandatory);
  - `.sem` defaults to `.release`, `.scope` to `.cta`, and the two "must be specified together";
  - `.relaxed` gives no ordering;
  - the ISA's example is `mbarrier.arrive.release.cta.shared::cluster.b64 _, [remoteAddr32]` after `mapa`;
  - multicast arrive (`.multicast::cluster::32b`) is sm_107f+ only (ibid., Target ISA Notes), not sm_100a.
- **Wait defaults.** `.acquire.cta` (§9.7.15.16.19). The acquire guarantees are phrased for "the participating threads
  of the CTA" (ibid.). Whether a `.cta`-scope pair synchronizes an arrive from another CTA is **unknown**; the CUDA
  guide's cluster example uses `sem_release, scope_cluster` for the remote arrive (CUDA Programming Guide §4.12.3,
  `cudapg/async-copies.txt` 2088, 2100).
- **`mapa.shared::cluster.u32 d, a, rank`** gives the address in CTA `rank` corresponding to `a` (§9.7.10.26).
- **Peer must exist.** The executing CTA must ensure the peer's shared memory exists and that the peer "hasn't exited
  before completing the shared memory operation" (§2.2.2).

### 3.7 Cluster barrier, init fence, special registers

- **`barrier.cluster.arrive{.release|.relaxed}{.aligned}` / `barrier.cluster.wait{.acquire}{.aligned}`** (§9.7.15.3):
  - wait blocks until all **non-exited** threads of the cluster have arrived;
  - each thread arrives once per phase;
  - the barrier re-arms automatically;
  - arrive defaults to `.release` and wait to `.acquire`;
  - `.relaxed` gives no ordering for prior accesses;
  - `.aligned` requires the whole warp to execute the same instruction;
  - the instructions also wait for the non-exited threads of the executing warp.
- **`fence.mbarrier_init.release.cluster`** applies to the thread's prior `mbarrier.init`s on `.shared::cta` objects
  (§9.7.15.4). The ISA's pattern for publishing barriers to the cluster is `mbarrier.init`;
  `fence.mbarrier_init.release.cluster`; `barrier.cluster.arrive.relaxed` (§9.7.15.4, Examples).
- **A pattern nobody emits.** The same examples show "Acquire remote barrier state via async proxy":
  `barrier.cluster.wait.acquire; fence.proxy.async::generic.acquire.sync_restrict::shared::cluster.cluster`. Neither
  CUTLASS nor FA4 emits this proxy fence. A `cta_group::2` TMA that signals a peer's barrier does not need it
  (resolved, 2026-10-01): the TMA accesses its mbarrier through the generic proxy (§9.7.10.28.5.3), so the barrier
  state the cluster barrier publishes is generic-proxy state.
- **Special registers:**
  - `%cluster_ctarank`: rank in the cluster across dimensions, `0 ≤ … < %cluster_nctarank` (§10.16, §10.17);
  - `%clusterid` / `%nclusterid`: the cluster's id in the grid and the grid's cluster count (§10.12, §10.13);
  - `%cluster_ctaid` / `%cluster_nctaid`: per dimension (§10.14, §10.15);
  - `%is_explicit_cluster` (§10.11).

### 3.8 One `.cta_group` per kernel (A29)

- The wording, in §9.7.18.7.1, §9.7.18.10.10.1, §9.7.18.12.1, §9.7.18.9.2 and §9.7.18.9.3: "All tcgen05 instructions
  within a kernel must specify the same value for the .cta_group qualifier."
- `tcgen05.ld/st/wait/fence` carry no `.cta_group`.
- `cp.async.bulk.tensor`'s `.cta_group` is not a `tcgen05` instruction, so the rule does not reach it (**inferred**).

### 3.9 Pipelined pairs with `::2`

- The pairs are stated per instruction with "(same N)", from the same warp. The ones that matter (§9.7.18.6.2):
  - `tcgen05.mma.cta_group::N (A and metadata reads) -> tcgen05.mma.cta_group::N (D writes) (same N)`;
  - `(C reads) -> (D writes)` and `(D writes) -> (D writes)`, both with "same N and accumulator address and shape";
  - `mma -> commit (same N)` (§9.7.18.6.2.1.1).
- So A33 extends to `::2` for MMAs issued by one thread. Its application to the A reads and D writes in the **peer's**
  TMEM is **inferred** (the pair names instructions, not CTAs). FA4 relies on it (§1.3).

### 3.10 Ordering async-proxy accesses across the pair

- Proxy-preserved base causality orders X before Y if they are "performed to the same address, using the same proxy,
  and by the same thread block" (or both generic, or aliases with an alias fence) (§8.9.5).
- **1-CTA.** `MODELS.md` O2 uses the same-thread-block clause for "MMA read, then TMA refill write".
- **2-CTA.**
  - The refill is issued by the CTA that owns the stage, while the reading MMA is issued by the leader.
  - Symmetrically for O1, the peer's TMA write is read by the leader's MMA.
  - The ISA text gives no clause for async-to-async across thread blocks (**unknown**).
  - TMA completion implies a generic-async proxy fence (§9.7.10.28.2). That covers generic readers, not an
    async-proxy reader issued by another CTA.
  - CUTLASS and FA4 rely on the barrier chain alone.
- **Async operations and program order.** They are ordered after prior instructions of the issuing thread, but a
  `cp.async.bulk` complete-tx "does not transitively establish ordering with respect to prior instructions" (§8.9.1.1).

## 4. Launch

- **Runtime launch.** CUTLASS launches clusters with `cudaLaunchKernelExC` and attribute
  `cudaLaunchAttributeClusterDimension` (`include/cutlass/cluster_launch.hpp` 166–176, 248, 294). It first sets
  `cudaFuncAttributeNonPortableClusterSizeAllowed` (143). Its check is `cluster.x·cluster.y·cluster.z ≤ 32` and
  **grid divisible by the cluster in every dimension** (102–112). FA4 launches through the DSL with
  `cluster=(2,1,1)` (`flash_fwd_sm100.py` 864–869). Its grids are even by construction (§1.10).
- **Compile-time alternative.** `__cluster_dims__(x, y, z)` on the kernel (CUDA guide example,
  `cudapg/async-copies.txt` 2047), i.e. PTX `.reqnctapercluster`: "runtime will use the specified values for configuring
  the launch if the same are not specified at launch time". A different explicit value fails (§11.7.1). So a plain
  `cudaLaunchKernel` launches a `__cluster_dims__(2,1,1)` kernel as clusters (**inferred** from §11.7.1).
- **Not in the local copy.** The local CUDA guide copy has no section on cluster launch rules, so the divisibility rule
  and the portable maximum cluster size (8) are not read there (**unknown** locally; the divisibility rule is CUTLASS's
  check).
- **Shared memory.** At about 224 KB per CTA, one CTA fits per SM. A pair needs two co-scheduled SMs. Co-residency is
  the hardware's (clusters "run concurrently", §2.2.2).

## 5. Our gaps

### 5.1 Existing items the pair extends or contradicts

| Item | Existing | Relation |
|---|---|---|
| Launch | A17 (`cudaLaunchKernel`), I6 | extends: cluster dimensions and divisibility |
| Init visibility | A7 ("then a CTA barrier"), `MODELS.md` §1.2 Init visibility, O6 | contradicts for the pair: a CTA barrier does not publish barriers to the peer. The setup's arrivals (phase-0 completions) need `.release.cluster`, or a non-relaxed `barrier.cluster.arrive`, to be covered (`MODELS.md` §1.2 already says so) |
| Arrive / wait | A6, `MODELS.md` §1.2 Arrive (`.shared::cta` only), §1.7 ("remote barriers unused") | extends: remote arrive; waits stay local |
| Negative tx | `MODELS.md` §1.2 "A negative tx … In these protocols it does not happen" | contradicts: the peer's complete-tx can precede the leader's expect-tx |
| TMA | A9, `MODELS.md` §1.3 (copy completes on `b` in its own CTA) | extends: `b` in the peer; `cta_group::2` form; expect = sum over the pair |
| MMA | A11, A23 (`cta_group::1`, M = 128, Layout D), A24 (B MN-major LBO 16384 for N = 128), A27, `MODELS.md` §1.4 MmaIssue | extends. Layout A instead of D. B per CTA is N/2 = 64, so V's descriptor changes (H2 again). The `Mma` reads and writes span two CTAs |
| Commit | A12, `MODELS.md` §1.4 CommitFire (one Arrive) | extends: Arrive on the set of masked CTAs' barriers |
| Pipelined pair | A33 | extends to `::2` and the peer's TMEM |
| TMEM ld/st handoffs | A13, A14, A19, A20, A21, M9, M13, O3, O4 | extends across CTAs (`.cluster`-scope arrive and wait, as in the ISA's patterns) |
| Async-to-async ordering | `MODELS.md` O1, O2 (§8.9.5 "same thread block") | contradicts: the clause does not apply across the pair |
| TMEM allocation | A10, S4 ("allocated once per CTA"), `withTmem` | extends: a pair allocation, collective and possibly blocking. The address is read in each CTA. Dealloc needs a cross-CTA handshake |
| One `.cta_group` | A29; `ATTENTION.md` §7.1 ("attention uses `cta_group::1` throughout") | A29 holds. §7.1's sentence no longer holds for a 2-CTA attention kernel, and the group must be a kernel-level index |
| Teardown | A8, A38, M7, M15, I8, `MODELS.md` §6 2-CTA item | extends: a CTA's `inval`, close and exit must follow every remote arrive, complete-tx and commit aimed at it, and the peer's last use of its shared memory and TMEM |
| Roles | M3, M6, M10, M11 | extends: role branch on rank parity (uniform). Stage and phase registers must agree across CTAs (lockstep) |
| Row affinity | M12, `storeO` | extends: a thread's global row is `rank·128 + 32·(w mod 4) + lane` within the M = 256 tile |
| Fresh-barrier wait | `MODELS.md` §1.2 | unchanged. FA4 and CUTLASS rely on parity-1 on fresh barriers; we avoid it with setup arrivals |

### 5.2 New assumptions (proposed A40+)

Final numbers in `OBLIGATIONS.md` §3, after P2 took A40–A42: A40–A44 here are A43–A47 there, A45 is A48, A46 A49,
A47 A50, A48 A51, A49 A52, A50 A53, A51 A55, and A52 A54; A56 (one CTA per SM) is new.

| # | Assumption | Source |
|---|---|---|
| A40 | A kernel launched with cluster dimensions `(2,1,1)`, by `cudaLaunchKernelEx` with `cudaLaunchAttributeClusterDimension` or by `__cluster_dims__(2,1,1)`, runs as clusters of two co-scheduled CTAs. The grid's x must be a multiple of 2. The two CTAs of a cluster have `%cluster_ctarank` 0 and 1 and form one CTA pair, rank 0 even. | PTX §2.2.2, §9.7.18.5.1, §10.16, §11.7.1; CUTLASS `cluster_launch.hpp` 102–112, 166 |
| A41 | `barrier.cluster.arrive.aligned` (`.release`) then `barrier.cluster.wait.aligned` (`.acquire`) by every thread of both CTAs orders all their prior memory accesses before all later ones, across the cluster. With `.relaxed` arrive, only accesses released by a prior fence are covered. | PTX §9.7.15.3 |
| A42 | `mbarrier.init`; `fence.mbarrier_init.release.cluster`; `barrier.cluster.arrive.relaxed`; `barrier.cluster.wait` makes every CTA's initialized barriers usable by remote arrives, multicast commits and peer TMAs. | PTX §9.7.15.4 (Examples), §9.7.15.3; CUTLASS K 580–615 |
| A43 | `mapa.shared::cluster.u32` then `mbarrier.arrive.release.cluster.shared::cluster.b64 _, [a]` performs one arrive-on on the peer's barrier, with release at cluster scope. A `try_wait.parity.acquire.cluster` on the barrier's own CTA that observes the phase synchronizes with it. No thread waits on a remote barrier. | PTX §9.7.10.26, §9.7.15.16.11, §9.7.15.16.16, §9.7.15.16.19; CUDA guide §4.12.3 (cluster scope) |
| A44 | `cp.async.bulk.tensor.2d.cta_group::2.shared::cluster.global.mbarrier::complete_tx::bytes [dst], [map, …], [b]`, with `dst` in the issuing CTA and `b` the even CTA's barrier (by `mapa`), writes `dst` and performs one complete-tx of the box's bytes on `b`, release at cluster scope. A complete-tx may precede the expect-tx within a phase. | PTX §9.7.10.28.5.3, §9.7.15.16.6 |
| A45 | `tcgen05.mma.cta_group::2.kind::f16` with M = 256, issued by one thread of the even CTA, reads A rows 0–127 and B columns 0 to N/2−1 from that CTA's shared memory, and A rows 128–255 and the rest of B from the odd CTA's shared memory at the same descriptor addresses. It writes D rows 0–127 and 128–255 to the even and odd CTA's TMEM, lane = row mod 128, at the same column address. With A in TMEM, each CTA supplies its own 128 rows at the same address, packed as A23. | PTX §9.7.18.10, §9.7.18.10.10.1, §9.7.18.2.1 Table 48, §9.7.18.10.5; the split only in CUTLASS `mma_traits_sm100.hpp` 1160–1184, 1291–1315 and `…_frag.hpp` 192–201: medium |
| A46 | `tcgen05.commit.cta_group::2.mbarrier::arrive::one.shared::cluster.multicast::cluster [b], m` arrives once (count 1, cluster scope) on the barrier at `b`'s offset in each CTA of `m`. It does so after every earlier `cta_group::2` MMA of the issuing thread has completed, including its accesses to the peer's shared memory and TMEM, and it performs `tcgen05.fence::before_thread_sync`. The arrivals are not assumed simultaneous. | PTX §9.7.18.12.1, §9.7.18.6.2.1.1, §9.7.18.6.4.2 |
| A47 | `tcgen05.alloc/dealloc/relinquish_alloc_permit.cta_group::2` are executed by the same-numbered warp in each CTA of the pair, collectively, and may block until both have. Alloc writes the TMEM address into each CTA's own `dst`, and the two addresses are equal. Dealloc requires that neither CTA's TMEM is accessed concurrently. | PTX §9.7.18.5 Tables 55–57, §9.7.18.7.1; equality only CUTLASS `tmem_allocator_sm100.hpp` 159–166: medium |
| A48 | A33 holds for `cta_group::2`: one thread's MMA reading A in TMEM is ordered before a later MMA of the same thread writing D at those columns, in both CTAs' TMEM. | PTX §9.7.18.6.2 ("same N") |
| A49 | `tcgen05.fence::before_thread_sync` and `::after_thread_sync` compose with cluster-scope mbarrier arrives and waits across the pair as within a CTA. That is, A13, A20 and M13 hold when the writer and the waiter are in different CTAs of the pair, given `.cluster` scope on both ends. | PTX §9.7.18.6.3, §9.7.18.6.4.4, §9.7.18.11.1 (no CTA restriction): inferred |
| A50 | An async-proxy write to a CTA's shared memory (a TMA by either CTA) and an async-proxy read of it by an MMA issued in the other CTA are ordered by the barrier chain of O1 and O2 with no proxy fence, as if by one thread block. | not in PTX (§8.9.5 covers only "the same thread block"); CUTLASS and FA4 rely on it: **low-medium; a hardware experiment and an NVIDIA question** |
| A51 | A CTA does not exit, deallocate TMEM or invalidate a barrier while the peer may still access its shared memory or barriers (remote arrive, complete-tx, commit, MMA operand reads) or its TMEM. The pair's last such accesses are ordered before by waits or by a cluster barrier. | PTX §2.2.2, §9.7.18.5 Table 55 (`::2` row) and Tables 56–57, §9.7.15.16.13 |
| A52 | `tcgen05.ld`/`st` in a `cta_group::2` kernel access only the executing CTA's TMEM, with the warp-quadrant lanes of A14 and A19. | PTX §9.7.18.8, §9.7.18.8.1, §9.7.18.5 Table 55 |

### 5.3 Open items the design must settle

- **Peer barrier address.** `mapa` (documented) or CUTLASS's bit-24 clear (undocumented). A44 takes `mapa`.
- **Scope of remote arrives and waits.** FA4 and CUTLASS use `.cta`. The ISA examples and the CUDA guide use
  `.cluster`. A43 and A49 take `.cluster`. The cost is unmeasured (the DSL comment says it is "measurably slower",
  `cute_arch_mbar.py` 437–441).
- *Resolved:* **the async-generic proxy fence** after `barrier.cluster.wait` for remote barrier state (§9.7.15.4
  example) is not needed: a TMA accesses its mbarrier through the generic proxy (§9.7.10.28.5.3; §3.7).
- **Unwaited remote arrivals at exit.** FA4's last correction release, and CUTLASS's last accumulator release before
  the leader's tail: A51 requires each to be waited on or ordered by a cluster barrier.
- **Which CTA issues.** PTX allows either (§3.1). A45 fixes the even one.
