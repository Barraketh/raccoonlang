# GPU library: CUTLASS as the performance reference

Status: research note, 2026-09-30. It records how CUTLASS's Blackwell (sm100) GEMM does what our persistent GEMM
(`DESIGN.md` §6) does, what that implies for the library's discipline (`OBLIGATIONS.md`), what to change first, and the
commands for the next hardware session (§8). We benchmark against open-source code only; cuBLAS is not a reference.

**Source read.** CUTLASS at commit `0b55a2f691d69981583568fd9eb69687b1f0de8a` ("update 4.8 release", 2026-09-23),
BSD-3. Paths below are relative to its root; line numbers are at that commit. PTX semantics are cited by instruction
name from the PTX ISA (the online edition is 9.4; CUDA 12.9 ships an earlier one, whose section numbers differ).
Where we state what hardware does beyond what the CUTLASS source shows, it is our reading, and "unknown" means we do
not know.

**The problem.** C (M×N, f32, row-major) = A (M×K, bf16, row-major) · Bᵀ, B N×K bf16 row-major. In CUTLASS's terms
A is row-major (`t`), B is column-major K×N (`n`), D is row-major (`t`), C is absent (`void`): layout `tnt`. The
profiler instantiates this exact problem (§8.4).

## 1. Summary

| | Ours (`persistent_gemm.rac`) | CUTLASS, 2-SM 256×256×64 (its usual large-GEMM configuration) |
|---|---|---|
| MMA | `tcgen05.mma.cta_group::1.kind::f16`, 128×128×16, one elected thread | 2-SM `cta_group::2`, 256×256×16 per instruction, leader CTA's MMA warp |
| Tile per CTA | 128×128 | 128×256 (half of a 256×256 pair tile) |
| Cluster | none | ≥ 2×1 (the pair); the builder offers 2×2, 4×1, … with TMA multicast |
| Stage | 32 KiB (A 16 + B 16), 6 stages | 32 KiB per CTA (A 128×64 + half of B, 128×64), 6 stages |
| Bytes loaded per output element | 2·K·2 / 128 = K/32 | K/64 (half), less again in L2 reads with multicast |
| Accumulators | 2 × 128 columns | 2 × 256 columns (all 512) |
| Epilogue | `tcgen05.ld.32x32b.x8` + `wait::ld`, scalar row stores | `tcgen05.ld.32x32b.x32`, `st.shared.v4` into 2 swizzled 128×32 f32 buffers, TMA store |
| Scheduler | static persistent grid, row-major (grouped being added) | cluster launch control (CLC): full grid, each CTA cancels unlaunched clusters to take their tiles |
| Warps | 8: TMA, MMA, 2 idle, 4 epilogue | 8: MMA, scheduler, TMA, epilogue-load (idle without C), 4 epilogue |
| `setmaxnreg` | no | no (only in the ptr-array and transform kernels) |

Ten lines on what CUTLASS does differently:

1. It pairs two SMs: one `tcgen05.mma.cta_group::2` computes a 256×N tile from A rows in both CTAs and B columns split
   across both, so each SM loads half the B it multiplies with. Bytes per FLOP halve at the same stage size.
2. It uses N = 256 per instruction and per CTA, so a tile is 128×256 per SM and all 512 TMEM columns hold 2 accumulators.
3. With clusters larger than the pair, it multicasts A along the cluster's N mode and B along its M mode, so L2 reads
   drop further; shared-memory fills per SM do not.
4. Every cross-CTA signal is an mbarrier operation at a cluster address: TMA completes bytes on the leader CTA's
   barrier, `tcgen05.commit…multicast::cluster` arrives on barriers in several CTAs, epilogue threads of both CTAs
   arrive on the leader's barrier.
5. The epilogue stages 128×32 f32 subtiles in two 16 KiB swizzled shared buffers and writes them with TMA stores
   (`cp.async.bulk.tensor`), coalesced whole lines, instead of per-thread scalar stores.
6. It frees the accumulator after the last TMEM load of a tile, before any global write completes, so the next
   tile's MMAs overlap the stores.
7. It schedules with cluster launch control: the grid covers every tile, and a running CTA cancels a not-yet-launched
   cluster to inherit its coordinates, so the tile loop's trip count is data-dependent and load balance is dynamic.
8. Rasterization comes from launch order (along M or N by a heuristic) plus an optional serpentine swizzle; the
   swizzle is off by default.
9. Stage counts are computed to fill shared memory after the epilogue's buffers: 6 at our tile, 4 at 1-SM 128×256.
10. It does not use `setmaxnreg` in this kernel; 256 threads have ample registers.

## 2. Tile shapes and MMA

**Configurations for our problem.** The profiler's generator (`python/cutlass_library/generator.py`
`GenerateSM100_TensorOp_16b_UMMA_gemm`, 6912-7120, with the shape tables of `python/cutlass_library/sm100_shapes.py`
47-158) emits at its default level 86 `tnt` bf16→f32 kernels with void C: 1-SM MMA tiles 64×128, 128×128, 128×256,
2-SM MMA tiles 128×128, 128×256, 256×128, 256×256, all with K = 64 (four K = 16 instructions), each for several
clusters and for the default and stream-K schedulers. We ran the generator (§8.2) to list them. Example 70
(`examples/70_blackwell_gemm/70_blackwell_fp16_gemm.cu` 115-117) uses MMA tile 256×128 with cluster 2×2; the builder
picks 2-SM whenever the cluster's M extent is even and the tile's M is a multiple of 128
(`include/cutlass/gemm/collective/builders/sm100_common.inl` 444-477, `sm100_umma_builder.inl` 209-213).

The closest to cuBLAS-class performance in CUTLASS's own practice is 2-SM 256×256×64; §7 treats which configuration
wins on this problem as a hardware question (§8.5).

**1-SM versus 2-SM.**
- The 2-SM atom `SM100_MMA_F16BF16_2x1SM_SS` (`include/cute/arch/mma_sm100_umma.hpp` 551-590) accepts M = 128 or 256,
  N a multiple of 16 up to 256. Its layouts (`include/cute/atom/mma_traits_sm100.hpp` 1178-1184) split A's M rows
  and B's N columns in half across the two CTAs (`ThrID = Layout<_2>`, A `(2, (M/2, K))`, B `(2, (N/2, K))`), and C
  as M/2 rows × all N per CTA. So for 256×256: each CTA holds A 128×64 and B 128×64 per stage (the builder's
  `SmemShape_M/N`, `sm100_umma_builder.inl` 245-250) and its TMEM holds 128 lanes × 256 columns of the result.
- **Who issues.** Only the leader CTA (even rank in the pair, `cta_coord_v == 0`) runs the MMA loop
  (`include/cutlass/gemm/kernel/sm100_gemm_tma_warpspecialized.hpp` 427-430, 762-772). The peer's MMA warp only
  allocates and frees TMEM. Every MMA and commit is issued under a fresh `elect_one_sync()` by the whole MMA warp
  (`mma_sm100_umma.hpp` 105, 570; `include/cutlass/arch/barrier.h` 856-921); CUTLASS relies on `elect.sync` electing
  the same lane each time, since a commit covers the executing thread's MMAs.
- **How the commit reaches both CTAs.** The accumulator is committed with
  `tcgen05.commit.cta_group::2.mbarrier::arrive::one.shared::cluster.multicast::cluster` to the accumulator's full
  barrier with a mask of both CTAs of the pair (`include/cutlass/pipeline/sm100_pipeline.hpp` 94-113 and 260-270;
  `barrier.h` 907-921), so each CTA's epilogue waits on its own barrier. A stage is released the same way, with the
  mask of every CTA whose stage the MMAs read (§3).
- **TMA for a pair.** Both CTAs issue `cp.async.bulk.tensor.2d.cta_group::2…` into their own shared memory, but with
  the barrier address's peer bit cleared (`Sm100MmaPeerBitMask = 0xFEFFFFFF`, `include/cute/arch/copy_sm100_tma.hpp`
  45, 78-102), so both CTAs' bytes complete on the leader's full barrier. Only the leader's producer arms that barrier,
  with both CTAs' bytes (`TmaTransactionBytes` multiplied by the pair size, `sm100_mma_warpspecialized.hpp` 237-240;
  `is_leader` 465 of the kernel; `arrive_and_expect_tx` in `include/cutlass/pipeline/sm90_pipeline.hpp` 530-556). The
  peer's bytes may land before the leader's `expect_tx`; the phase cannot complete early because the leader's arrival
  is still pending (our reading of the PTX `mbarrier` tx-count, which may be transiently negative within a phase).
  That the cleared bit addresses the even CTA of the pair in the cluster shared window is an address-layout fact
  CUTLASS relies on; whether PTX documents it (as opposed to `mapa`) is unknown to us.

**UMMA shapes.** `kind::f16` with K = 16 per instruction (256 bits of bf16), four per 64-wide K step, the first of a
tile with the accumulate predicate off: CUTLASS sets `accumulate_ = Zero` before the loop and `One` after the first
instruction (`sm100_mma_warpspecialized.hpp` 676-707), a run-time predicate, where we peel the first K step.

**TMEM.** The MMA warp allocates all 512 columns once per CTA (`kernel` 728, freed at 804; 2-SM uses
`tcgen05.alloc.cta_group::2`, `include/cute/arch/tmem_allocator_sm100.hpp` 172-227). The accumulator stage count is
`min(4, 128·512 / (CtaM·CtaN))` (`sm100_umma_builder.inl` 261-267): 4 at 128×128 (we use 2), 2 at 128×256 and at
2-SM 256×256 (2 × 256 columns). The allocation result reaches the epilogue through a named barrier of the MMA warp
and the epilogue warpgroup (`kernel` 558, 730, 871), not a CTA barrier. At the end, the 2-SM pair runs a cluster-barrier
handshake so neither CTA frees TMEM while the other's MMAs or loads may touch it (`kernel` 783-804).

## 3. Mainloop pipeline

**Stages.** `StageCountAutoCarveout` divides what shared memory is left after the epilogue's storage and the kernel's
barriers (`sm100_umma_builder.inl` 84-99, 284-300; capacity 232448 bytes, `include/cutlass/arch/arch.h` 45; carve-out
`sm100_pipeline_carveout.inl` 45-83) by the stage size (A + B + 16 bytes of barriers). With void C the epilogue keeps
2 × 16 KiB (§4), so: 1-SM 128×128, 6 stages (ours: 6); 1-SM 128×256, 4; 2-SM 256×256, 6; 2-SM 256×128, 8. Layout: all
A stages, then all B stages, each K-major with the 128-byte swizzle atom (`sm100_common.inl` 82-140), one TMA box per
operand per stage (`sm100_mma_warpspecialized.hpp` 178-189). Ours interleaves A and B per stage; the difference is
immaterial.

**Producer (`load`, 588-629).** The whole TMA warp runs the loop: every lane waits on `empty[s]`
(`producer_acquire`), one lane arms `full[s]` with `arrive.expect_tx`, then `elect_one_sync()` issues the two TMA
loads. It peeks the next stage with `try_wait` before issuing (`producer_try_acquire`, 604, 617). The tail waits for
every stage to be released (`load_tail`, 632-641; `producer_tail`, `sm90_pipeline.hpp` 466-473), which in a cluster
also keeps the CTA alive while peers may still write into it.

**Consumer (`mma`, 651-712).** The MMA warp waits on `full[s]`, issues four MMAs, and releases the stage with a
commit; it acquires the accumulator's empty barrier once per tile before the K loop (678).

**Multicast.** For a cluster larger than the MMA's pair, A is multicast to the CTAs that share its M rows (the
cluster's N mode) and B to those that share its N columns (M mode): masks from `create_tma_multicast_mask<2>` and
`<1>` (`sm100_mma_warpspecialized.hpp` 524-546). `tma_partition` over the multicast group gives each CTA a slice of
the box to issue, which lands in every CTA of the mask. The atoms are `SM90_TMA_LOAD_MULTICAST` (1-SM) or
`SM100_TMA_2SM_LOAD_MULTICAST` (`copy_sm100_tma.hpp` 255-279), chosen from the cluster shape (`sm100_common.inl`
199-268): a 2×1 cluster with 2-SM MMA uses no multicast at all.

**Cross-CTA empty and full barriers.**
- `full[s]` (count 1, plus bytes) is armed by the CTA's own leader producer and completed by every TMA that writes the
  stage, including multicasts and the pair peer's loads.
- `empty[s]` has arrival count `cx/ax + cy/ay − 1` (`sm100_pipeline.hpp` 561-575): the number of MMA issuers (pairs)
  in the same cluster row or column, that is, every consumer whose operands this CTA's producer writes. Each consumer
  releases with `tcgen05.commit…multicast::cluster` to the mask of every CTA in its row and column (masks
  `calculate_multicast_mask<kRowCol>`, 55-91; release 742-760). So a producer refills stage s only after every
  reader of every copy it wrote has finished. All CTAs of a cluster must therefore walk the same stage sequence: the
  same tiles, the same K counts, in lockstep.
- Initialization is made visible cluster-wide by `fence.mbarrier_init.release.cluster` and a cluster barrier
  (`barrier.cluster.arrive.relaxed` / `wait`) instead of `__syncthreads` (`sm90_pipeline.hpp` 1378-1403, kernel
  578-615).

## 4. Epilogue

The configuration for void C and f32 row-major D (`include/cutlass/epilogue/collective/builders/sm100_builder.inl`):
- **Subtile.** `EpilogueTileAuto` targets 4096 elements per iteration: 128×32 f32 (980-1060, `N_perf` 1008). A
  128×256 CTA tile is 8 subtiles.
- **TMEM load.** `SM100_TMEM_LOAD_32dp32b` repeated to the subtile's width, `tcgen05.ld.32x32b.x32` (593-715): each
  thread gets 32 consecutive columns of its row. `tcgen05.wait::ld` is issued once per tile, only before releasing
  the accumulator (`sm100_epilogue_tma_warpspecialized.hpp` 884-890; `barrier.h` 982-989); the loaded registers are
  read without it. Whether PTX guarantees that is unknown to us; CUTLASS relies on it. We wait after every load.
- **Shared staging.** `StagesD = min(subtiles, 2)` (1107-1117): two 128×32 f32 buffers of 16 KiB, K-major with the
  128-byte swizzle (72-97), written with 16-byte vector stores (`AutoVectorizingCopyWithAssumedAlignment<128>`,
  718-800). Nothing for C (void C disables its load and buffers).
- **Per subtile** (`store`, 574-956; `tma_store_fn`, 766-800), all 128 epilogue threads:
  1. on the first subtile, wait for the accumulator's full barrier (864-867);
  2. `tcgen05.ld` the subtile; after the last one, `tcgen05.wait::ld` and arrive on the accumulator's empty barrier
     (881-890): the MMA warp may overwrite that buffer from here on;
  3. convert and `st.shared` into buffer `i` (913-923);
  4. `fence.proxy.async.shared::cta` by every thread, then a named barrier over the 128 threads (768-769; `barrier.h`
     787-795), so the async proxy sees the generic-proxy writes;
  5. warp 0 issues the TMA store `cp.async.bulk.tensor.2d.global.shared::cta.bulk_group` (770-772, 740;
     `include/cute/arch/copy_sm90_tma.hpp` 980-1001) and `cp.async.bulk.commit_group` (778-780), then
     `cp.async.bulk.wait_group.read 1` before the next buffer (`producer_acquire` with `always_wait`, 784-786; kernel
     491; `PipelineTmaStore`, `sm90_pipeline.hpp` 673-727), so at most one store is still reading shared memory;
  6. a named barrier (787) before any thread writes the next buffer.
  With void C, `DelayTmaStore` issues each subtile's store one iteration late (900-907, 942-945) to interleave it with
  the next subtile's loads.
- **Which thread commits and waits.** The store, commit and wait are inside `if (warp_idx == 0)` with no elect: all
  32 lanes execute them. Bulk groups are per thread, so each lane waits on its own. Whether 32 lanes issuing the same
  `cp.async.bulk.tensor` store issue it once or 32 times is unknown to us.
- **Overlap with the next tile.** The accumulator is released at step 2 of the last subtile, before its stores
  complete; with 2 accumulators the MMA warp is already filling the other one. Global writes never block the
  mainloop; only the TMEM reads do.
- **Tail.** Without C, `store_tail` does nothing (1271-1291): the kernel does not wait for the last bulk store to
  finish reading shared memory before the CTA exits. What keeps that memory valid is unknown to us (presumably the
  hardware holds a CTA's shared memory until its bulk operations complete).
- **Partial tiles.** The TMA store clips to the tensor's extent, so edge subtiles need no predication.
- The 2-SM case changes nothing here: each CTA stores its own 128 rows. Its accumulator release is 256 arrivals, all
  epilogue threads of both CTAs, on the leader's empty barrier (`consumer_release_2x1SM`, `sm100_pipeline.hpp`
  272-277; `umma_arrive_2x1SM_sm0`, `barrier.h` 966-980; count `kernel` 530).

## 5. Tile scheduler and warp roles

**Scheduler.** `TileSchedulerTag = void` selects `PersistentTileSchedulerSm100`
(`include/cutlass/gemm/kernel/tile_scheduler.hpp` 207-219), cluster launch control. `StaticPersistentScheduler` selects
`StaticPersistentTileScheduler100`, a static persistent grid like ours (292-298); the profiler's kernels use the
former or stream-K.
- **Grid.** One CTA per tile (`sm100_tile_scheduler.hpp` 203-248), clustered. A CTA starts on its own blockIdx
  (`initial_work_tile_info`, 367-371).
- **Next tile.** The scheduler warp of the cluster's first CTA issues
  `clusterlaunchcontrol.try_cancel.async.shared::cta.mbarrier::complete_tx::bytes.multicast::cluster::all.b128`
  (392-405): the hardware cancels one not-yet-launched cluster and writes its first CTA id into every CTA of this
  cluster; `query_cancel.is_canceled` / `get_first_ctaid` decode it (409-438). A failed cancel (none left) ends the loop.
- **Broadcast to roles.** `PipelineCLCFetchAsync` (`sm100_pipeline.hpp` 937-1137): 2 response slots; lanes
  `< cluster_size` of the producer arm the full barrier in every CTA; every consumer, meaning the scheduler warp, and
  in every CTA the TMA, MMA and epilogue warps' threads, reads the slot and arrives on CTA 0's empty barrier, count
  `1 + cluster·(32 + 128 + 32 [+ 32])` (kernel 501-518). Each role runs `do { … fetch_next_work … } while (valid)`
  (617-955); all roles of all CTAs see the same sequence.
- **Throttle.** The scheduler issues a query only after the TMA warp starts a new tile (`clc_throttle`, kernel
  538-552, 631-637, 690-699), so a CTA does not claim work far ahead of its data movement.
- **Rasterization.** Order comes from launch order: `RasterOrderOptions::Heuristic` picks along M if there are more N
  tiles than M tiles, else along N, by transposing the grid (`tile_scheduler_params.h` 334-357, 1877-1910;
  `possibly_transpose_grid`, `sm100_tile_scheduler.hpp` 234-248). An optional swizzle of size S (`max_swizzle_size`,
  default 0, off) groups clusters into S-wide strips traversed in serpentine order (`swizzle_and_rasterize`,
  `sm100_tile_scheduler.hpp` 697-808). The launch order of CTAs within a grid, which
  this rests on, is not something CUTLASS states; our reading is ascending linear block index.
- **Partial tiles.** Grid covers `ceil` tiles; TMA zero-fills loads and clips stores. K is always whole
  (`get_work_k_tile_count`, 500-506).

**Warp roles** (`kernel` 136-146, 234-240, 418-455), 256 threads:

| Warp | Role |
|---|---|
| 0 | MMA (leader CTA only issues), TMEM allocation and free |
| 1 | CLC scheduler (first CTA of the cluster), TMA descriptor prefetch |
| 2 | mainloop TMA producer |
| 3 | epilogue load of C (idle when C is void) |
| 4-7 | epilogue |

No `setmaxnreg`: `grep` finds `warpgroup_reg_alloc`/`dealloc` only in the ptr-array kernel
(`sm100_gemm_array_tma_warpspecialized.hpp` 927-1554) and the MMA-transform kernel (642-770).

## 6. What this implies for the library's discipline

Each mechanism, our analogue, and the typed protocol it would need. "M" and "A" refer to `OBLIGATIONS.md` §5 and §3.

| Mechanism | Our analogue | What it needs | Rules stressed |
|---|---|---|---|
| N = 256, 128×256 tile, 1-SM | `mmaShapeOk` and `boxOk` allow it; `withAccRing(…, 2, 256, …)` fits 512 columns | nothing new | none; I2 (224 KiB of 227) |
| TMA-store epilogue | none; `storeRows` stores per thread | a staging-buffer typestate and an owned bulk-group endpoint (below) | M4, M6, M7, S1, S5; new A |
| Release the accumulator after the loads | `releaseAcc` after `storeTile` | `releaseAcc` right after the last `tcgen05.ld` + `wait::ld`; the stores then use registers and shared memory only | M4 (already fits: `AccFull` → loads → release) |
| One wait per subtile | `wait::ld` per 8 columns | wider loads, one wait | none |
| Cluster launch, cluster barriers | none | `Group.cluster`: every CTA runs the kernel; `barrier.cluster.arrive`/`wait` as the join for rings that span CTAs | M3, I7, I8, A7 |
| TMA multicast | none | a ring spanning a cluster (below) | M4, M6, M11, S3, A6, A9 |
| 2-SM MMA | none | a pair-scoped TMEM and accumulator (below) | S4, M6, A10-A12 |
| CLC scheduler | `forTiles`, trip count from a pure expression | a broadcast ring whose items are tiles; ownership from the hardware (below) | M5, M11, S5; new A |
| Grouped rasterization | being added | stays a pure function of the tile index | M10 |
| `setmaxnreg` | none | not needed here | (M3 if ever used) |

**A staging buffer for TMA stores.** Shared buffers written by the epilogue's threads and read by the async proxy.
Typestate per buffer, like `Tile` (`DESIGN.md`, SIMT tiles): `empty` → each thread `st.shared` its part → `written` →
(`fence.proxy.async.shared::cta` by every writer, then the group's named barrier) → `published` → one thread issues
`cp.async.bulk.tensor` and `commit_group` → `inFlight` → that thread's `wait_group.read n` → (named barrier) →
`empty`. What it stresses:
- **M6.** Bulk groups are per thread: the thread that commits must be the one that waits. The issuing endpoint must be
  taken by one elected thread of the epilogue warpgroup and kept across the tile loop, as `takeProducer` does for the
  ring, while the buffer's writes are the whole warpgroup's.
- **M5.** "At most S − 1 groups in flight" must be a fixed state: wait with the constant `wait_group.read (S − 1)`
  after every commit, as CUTLASS does, so the loop body's state type does not count groups.
- **M7 and close.** Before the kernel ends (or a ring closes and its storage is reused), `wait_group.read 0`; unlike
  CUTLASS we should not rely on the unknown in §4's tail.
- **S5.** `TileOwn` is consumed by the stores that cover the tile's boxes. That TMA stores clip to the tensor and
  write each in-box element once is a new platform assumption (as A9 is for loads). So is the proxy fence: generic
  writes followed by `fence.proxy.async` and a barrier are visible to a later bulk read. Neither is in A1-A18.

**A ring spanning a cluster (multicast, 2-SM).** Our ring is per CTA: one `Producer`, one `Consumer`, `empty[s]` with
one arrival. With multicast, filling stage s in CTA i writes into stage s of every CTA in its row or column, so the
producer's `Slot` must mean "stage s is free in every CTA I write into"; CUTLASS gets that by counting every such
consumer's release on `empty[s]` (§3). In types: a cluster ring whose per-CTA endpoints share one stage index sequence;
a release by consumer c arrives in every CTA of c's row and column (one commit, several barriers); a fill arms only
the own CTA's `full[s]` and expects bytes from several producers. What it stresses:
- **M6 and M11.** Stage and phase registers must agree across CTAs, not just within one thread. Lockstep follows from
  identical trip counts in every CTA of the cluster. Today a trip-count mismatch deadlocks; across CTAs it still
  deadlocks (a producer waits for a release that never comes), so M11's "deadlock, not a race" survives, provided
  every CTA's tile loop is the cluster's (the schedule must hand whole clusters, not CTAs, their tiles).
- **S3 and A8.** A CTA's barriers and stages are written by peers. Invalidation and exit need a cluster-wide join
  first (CUTLASS's producer tail plus cluster barrier); `withRing`'s close, today `__syncthreads` plus thread 0's
  `mbarrier.inval`, must become a cluster barrier.
- **A6, A7, A9, A12.** Cross-CTA `complete_tx` before `expect_tx`; `fence.mbarrier_init.release.cluster` followed by a
  cluster barrier (A7 names only a CTA barrier); multicast and `cta_group::2` TMA variants; multicast commit. Each is
  a new or widened assumption.

**A pair-scoped accumulator (2-SM).** One elected thread in the leader CTA issues MMAs that read both CTAs' shared
memory and write both CTAs' TMEM; the commit arrives in both. Our `TmemPermit`, `Acc` and `AccRing` are per CTA and
S4 says "allocated once per CTA". A pair needs: a pair allocation (`tcgen05.alloc.cta_group::2` by one warp in each
CTA) yielding one pair accumulator whose MMA side exists only in the leader and whose epilogue side exists in both;
the leader's `AccFree` requires both epilogues' releases (count 2·128 on the leader's barrier); and a pair handshake
before freeing TMEM. `Group` must express "the leader CTA's lane" and "every CTA's warpgroup". A10-A12 need their
`cta_group::2` forms. The CTA-rank-dependent role (the peer issues no MMAs) is a branch on a uniform, per-CTA value,
which `branch` already handles (M10, the rank is uniform).

**CLC scheduling.** The tile loop becomes `do … while (response valid)`. Today every role computes the same pure tile
sequence (`for (t = blockIdx.x; t < tiles; t += gridDim.x)`), so agreement is by construction and S5 (each tile
written once) follows from the static partition. With CLC:
- Agreement becomes a protocol: a broadcast ring (single producer in CTA 0, every role of every CTA consumes every
  item). A role that skipped an item would read the next tile's coordinates: a different trip count, which deadlocks
  (M11), but also different tile coordinates in lockstep with the others, which our types do not rule out today. The
  broadcast endpoint must hand each role the same item sequence, for instance by making the tile a value read only
  through the ring's `Ready` token and each role's loop consume exactly one item per iteration.
- The trip count is data-dependent. `Fixed` (M5) is unaffected, since loop bodies are generated once whatever the trip
  count. The peeled first iteration of our K loop is unchanged.
- S5 moves to the platform: each tile is either launched or returned by exactly one successful `try_cancel`. That is
  an assumption about `clusterlaunchcontrol` (PTX), not a property of our code; `TileOwn` would be minted from a
  response.
- M10: the response is read from shared memory written by the async proxy and is uniform per cluster; it needs its
  own grain rule.
- The launcher (I6) launches every tile's cluster, not `min(tiles, SMs)` CTAs.

**`setmaxnreg`.** Not needed at this design point. If a role ever needs more registers (a fused epilogue), it is
`.sync.aligned` over a warpgroup, so M3 must see the role as an aligned warpgroup; our warpgroup 0 mixes the TMA
warp, the MMA warp and two idle ones, which could decrease together.

**Where we are stricter than CUTLASS**, deliberately: one elect for the whole MMA loop (M6) rather than a fresh
`elect.sync` per instruction; `tcgen05.fence::before_thread_sync` before releasing an accumulator where CUTLASS relies
on `wait::ld` alone; a producer tail and invalidation on every ring. None of these costs measurable time. Also
stricter, and not yet measured: `tcgen05.fence::after_thread_sync` after the consumer's wait on a full stage, before
its MMAs (`await`; CUTLASS has none, DeepGEMM does); and arrivals at initialization that complete phase 0 of every
barrier a producer waits on first, so producers start at phase 0 instead of waiting at parity 1 on a fresh barrier
(`MODELS.md` §1.2).

## 7. Prioritized changes

The measurements (B200, 8192³, 1.10 TFLOP per GEMM; 1 ms is 1100 TFLOP/s):

| Variant | Time | Reading |
|---|---|---|
| Ours | 1.19 ms | |
| without epilogue stores (row-major order) | 0.909 ms | the scalar stores cost 0.28 ms |
| grouped (G = 16) | 0.955 ms | row-major order wastes 0.24 ms, probably in L2 misses on B |
| grouped, without epilogue stores | 0.695 ms | the scalar stores cost 0.26 ms in grouped order |
| grouped, without stores and MMAs | 0.622 ms | data movement alone; 17.2 GB of stage fills (4096 tiles × 4 MiB) at 27.6 TB/s |
| MMA floor | about 0.49 ms | at the nominal dense bf16 rate of about 2.25 PFLOP/s (not measured) |

The mainloop is bound by data movement at 128×128: 0.622 ms > 0.49 ms. Whether the bound is L2 bandwidth, the SMs'
fill rate, or DRAM misses that grouping removes is not separated by these runs (§8.6 has the run that separates them).
Expected times below scale the data-movement floor by bytes moved, and are estimates, not measurements.

1. **TMA-store epilogue** (being added). Two 128×32 f32 staging buffers (32 KiB; at 128×128 still 6 stages:
   6 × 32 KiB + 32 KiB fits in 227 KiB), `tcgen05.ld.32x32b.x32` and one `wait::ld` per subtile, accumulator released
   after the last load. Expected: most of the 0.26 ms store penalty goes; grouped time approaches the grouped
   "without stores" time, which should be at or below 0.695 ms. The biggest single gain, and a prerequisite for the
   others, since a 128×256 tile doubles the output per tile. Settled by our own run.
2. **Grouped rasterization** (being added): measured 1.19 → 0.955 ms. Keep; retune G after items 1 and 3, since larger
   tiles change the working set. Hardware: sweep G.
3. **1-SM 128×256 tiles.** Bytes per output fall by a quarter (tile loads (128 + 256)·K·2 for 32768 outputs instead
   of (128 + 128)·K·2 for 16384): data movement about 0.75 × 0.622 ≈ 0.47 ms, at the MMA floor. The library allows it
   today: B box 64×256, `mmaShapeOk` N = 256, accumulator ring 2 × 256 columns, 4 stages of 48 KiB plus 32 KiB of
   staging (224 KiB). Expected 0.55-0.65 ms with item 1. Open: whether a 1-SM MMA at N = 256 sustains full rate
   (each SM reads 12 KiB of shared memory per 128×256×16 MMA, against 8 KiB per SM for the 2-SM form); settled by the
   profiler's `128x256x64_1x1x1_1sm` against `256x256x64_2x1x1_2sm` (§8.5). The cheapest large step.
4. **2-SM 256×256 with a 2×1 cluster.** Bytes per output halve relative to ours (0.31 ms of data movement), so the
   kernel becomes MMA-bound; this is CUTLASS's own choice for large problems. Expected near the MMA floor, 0.50-0.55
   ms. Costs the most library work: cluster groups, the cluster ring, the pair accumulator (§6). Whether it beats
   item 3 is the hardware question above; do it if the gap is more than a few percent.
5. **Multicast (clusters 2×2, 4×1, or 1-SM 1×2).** Reduces L2 reads, not shared-memory fills. Helps only if the bound
   is L2 bandwidth rather than per-SM fill rate. Settled by the profiler sweep: `256x256_2x1x1` against `2x2x1` and
   `4x1x1`, and `128x256_1x1x1` against `1x2x1` (§8.5). Same library work as item 4, plus multicast masks.
6. **Stage count.** CUTLASS fills shared memory: 6 at 128×128 (as we do), 4 at 128×256, 6 at 2-SM 256×256. Nothing to
   change beyond computing the maximum that fits once the staging buffers exist. Low expected effect once the loop is
   MMA-bound; our own sweep (4 against 6 at 128×128) would show latency sensitivity. Hardware.
7. **Scheduler.** CLC balances load dynamically; a static persistent grid with a good order loses at most the tail
   wave's imbalance (at 128×128, 4096 tiles over 148 SMs is 27.7 per SM; at 128×256, 13.8) and whatever clock skew
   between SMs does. Expected: a few percent at most at 8192³; it matters more for shapes that fill a wave badly.
   Heavy on the discipline (§6). Last. The profiler's raster-order and swizzle sweep (§8.5) shows how sensitive
   CUTLASS is to order; its stream-K variants show the value of balancing.
8. **Minor.** Peek the next stage with `try_wait` before issuing (CUTLASS's `try_acquire` / `try_wait` tokens); prefetch
   the tensor maps (`prefetch.tensormap`); a named barrier rather than `__syncthreads` for the TMEM address. Each small.

## 8. The next hardware session

For `nvidia/cuda:12.9.1-devel-ubuntu22.04`, driver 595, no profiler counters. Every block is meant to be pasted as is,
from the home directory. Times are recorded with `time`; we have not built these targets and do not know the build
time (§8.3).

### 8.1 Tools and source

```bash
apt-get update && apt-get install -y --no-install-recommends git cmake python3 make g++ ca-certificates
nvidia-smi --query-gpu=name,driver_version,clocks.max.sm,clocks.max.mem --format=csv
nproc && cmake --version && nvcc --version | tail -1
```

```bash
mkdir -p ~/cutlass && cd ~/cutlass && git init -q . && git remote add origin https://github.com/NVIDIA/cutlass.git
git fetch -q --depth 1 origin 0b55a2f691d69981583568fd9eb69687b1f0de8a && git checkout -q FETCH_HEAD && git log -1 --format='%H %s'
```

(Ubuntu 22.04's cmake is 3.22; CUTLASS needs 3.19. The generator needs Python 3 at configure time.)

### 8.2 The kernels

Eight profiler kernels, all `tnt`, bf16 inputs, f32 accumulator, void C, f32 row-major D, default (CLC) scheduler:

| Kernel suffix | MMA tile | Cluster | Question |
|---|---|---|---|
| `128x128x64_1x1x1_0_tnt_align8_1sm` | 128×128, 1-SM | 1×1 | ours, done well |
| `128x256x64_1x1x1_0_tnt_align8_1sm` | 128×256, 1-SM | 1×1 | item 3 |
| `128x256x64_1x2x1_0_tnt_align8_1sm` | 128×256, 1-SM | 1×2 (A multicast) | item 5, 1-SM |
| `256x128x64_2x1x1_0_tnt_align8_2sm` | 256×128, 2-SM | 2×1 | 2-SM at our N |
| `256x256x64_2x1x1_0_tnt_align8_2sm` | 256×256, 2-SM | 2×1 | item 4 |
| `256x256x64_2x2x1_0_tnt_align8_2sm` | 256×256, 2-SM | 2×2 (multicast) | item 5 |
| `256x256x64_4x1x1_0_tnt_align8_2sm` | 256×256, 2-SM | 4×1 (B multicast) | item 5 |
| `256x256x64_0x0x1_0_tnt_align8_2sm` | 256×256, 2-SM | set at run time | cluster sweep |

The filter below was checked by running CUTLASS's generator with it at this commit: it selects exactly these eight
(the names are prefixes of no other kernel, and no stream-K variant).

```bash
K=cutlass3x_sm100_tensorop_gemm_bf16_bf16_f32_void_f32
KERNELS="${K}_128x128x64_1x1x1_0_tnt_align8_1sm,${K}_128x256x64_1x1x1_0_tnt_align8_1sm,${K}_128x256x64_1x2x1_0_tnt_align8_1sm,${K}_256x128x64_2x1x1_0_tnt_align8_2sm,${K}_256x256x64_2x1x1_0_tnt_align8_2sm,${K}_256x256x64_2x2x1_0_tnt_align8_2sm,${K}_256x256x64_4x1x1_0_tnt_align8_2sm,${K}_256x256x64_0x0x1_0_tnt_align8_2sm"
echo "$KERNELS" | tr , '\n' | wc -l
```

`K` and `KERNELS` are used by every block below; set them again in a new shell.

### 8.3 Build the profiler with only these kernels

```bash
cd ~/cutlass && cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DCUTLASS_NVCC_ARCHS=100a \
  -DCUTLASS_LIBRARY_OPERATIONS=gemm -DCUTLASS_LIBRARY_KERNELS="$KERNELS" \
  -DCUTLASS_ENABLE_TESTS=OFF -DCUTLASS_ENABLE_CUBLAS=OFF -DCUTLASS_ENABLE_CUDNN=OFF
find build -name 'cutlass3x_sm100_*.cu' | sort
```

The `find` must list exactly the eight kernels. Then:

```bash
cd ~/cutlass && time cmake --build build --target cutlass_profiler -j"$(nproc)"
```

Expected build time: unknown. The eight kernel files compile in parallel (a CUTLASS sm100 kernel takes minutes in
nvcc); the profiler's own sources and reference kernels are the rest. Our guess is 15-40 minutes on a 32-core host;
record the real figure.

### 8.4 Run at 8192³ and 4096³

```bash
cd ~/cutlass && P=build/tools/profiler/cutlass_profiler
for S in 8192 4096; do
  $P --operation=Gemm --kernels="$KERNELS" --m=$S --n=$S --k=$S --alpha=1 --beta=0 \
     --providers=cutlass --verification-providers=device \
     --warmup-iterations=20 --profiling-iterations=100 --output=cutlass_$S.csv
done
```

The profiler appends the operation kind to the file name (`cutlass_8192.gemm.csv`). Each kernel's block on the
terminal shows `Disposition` (want `Passed`), `Runtime: … ms` and `Math: … GFLOP/s`. A summary from the CSV:

```bash
summ() { awk -F, 'function g(n){return (n in c) ? $(c[n]) : "-"}
  NR==1 {for (i = 1; i <= NF; i++) c[$i] = i; next}
  {printf "%-86s %-9s m=%-5s cluster=%sx%s raster=%-9s swizzle=%-2s %8.4f ms %7.1f TFLOP/s\n",
     g("Operation"), g("Disposition"), g("m"), g("cluster_m"), g("cluster_n"), g("raster_order"), g("swizzle_size"),
     g("Runtime"), g("GFLOPs") / 1000}' "$1"; }
cd ~/cutlass && summ cutlass_8192.gemm.csv && summ cutlass_4096.gemm.csv
```

At 4096³ the profiler rotates several copies of the operands (about 3 × L2 in all) so each run starts with a cold L2;
at 8192³ the operands already exceed that, so it uses one copy. Our harness reuses one copy. For a warm-L2 figure
comparable with ours at 4096³, add `--workspace-count=1`:

```bash
cd ~/cutlass && build/tools/profiler/cutlass_profiler --operation=Gemm --kernels="$KERNELS" --m=4096 --n=4096 --k=4096 \
  --alpha=1 --beta=0 --providers=cutlass --verification-providers=device --workspace-count=1 \
  --warmup-iterations=20 --profiling-iterations=100 --output=cutlass_4096_warm.csv && summ cutlass_4096_warm.gemm.csv
```

### 8.5 Sweep

What §7 needs, in order. The comparisons among the eight kernels in 8.4 already answer: 128×128 against 128×256
(item 3), 1-SM 128×256 against 2-SM 256×256 (items 3 and 4), 2×1 against 2×2 and 4×1, and 1×1 against 1×2
(item 5). Then:

Cluster shapes with the run-time-cluster kernel (shapes the GPU cannot place are reported as not run):

```bash
cd ~/cutlass && build/tools/profiler/cutlass_profiler --operation=Gemm --kernels="${K}_256x256x64_0x0x1_0_tnt_align8_2sm" \
  --m=8192 --n=8192 --k=8192 --alpha=1 --beta=0 --cluster_m=2,4 --cluster_n=1,2,4 \
  --cluster_m_fallback=2 --cluster_n_fallback=1 --providers=cutlass --verification-providers=device \
  --warmup-iterations=20 --profiling-iterations=100 --output=sweep_cluster.csv && summ sweep_cluster.gemm.csv
```

Rasterization and swizzle on the 2-SM 2×1 kernel and on the 1-SM 128×256 kernel (how much order matters to CUTLASS,
for item 2):

```bash
cd ~/cutlass && build/tools/profiler/cutlass_profiler --operation=Gemm \
  --kernels="${K}_256x256x64_2x1x1_0_tnt_align8_2sm,${K}_128x256x64_1x1x1_0_tnt_align8_1sm" \
  --m=8192 --n=8192 --k=8192 --alpha=1 --beta=0 --raster_order=heuristic,along_m,along_n --swizzle_size=1,2,4,8 \
  --providers=cutlass --verification-providers=device --warmup-iterations=20 --profiling-iterations=100 \
  --output=sweep_raster.csv && summ sweep_raster.gemm.csv
```

### 8.6 Our kernel in the same session

Run ours on the same machine right after CUTLASS, as `DESIGN.md` §7 does (current head of the branch, grouped order),
and the variants of the table in §7. One new variant separates the data-movement bound: **without stores and MMAs,
with grouped order**. If it falls well below 0.622 ms, part of that figure was DRAM misses that grouping removes, and
items 3-5 gain less than §7 estimates; if it stays near 0.62 ms, the bound is the fill rate or L2 bandwidth, and item 5
(multicast) tells which. Record `nvidia-smi --query-gpu=clocks.sm,power.draw,temperature.gpu --format=csv` before and
after each series; without counters, clocks are the only check on throttling.

### 8.7 Like with like

- **Layout and types match.** The profiler's `…_void_f32_…_tnt` kernels compute D (f32, row-major) = alpha · A·B with
  A bf16 row-major, B bf16 column-major K×N (our N×K row-major), f32 accumulation, and no C. With `--alpha=1` the
  epilogue's multiply by 1.0 is exact, so the output is the same product ours computes.
- **Timing matches.** Both time back-to-back launches with CUDA events around the loop, in one stream. CUTLASS's
  launch includes its grid of every tile's cluster (CLC); ours, the persistent grid. Both are whole-kernel times.
- **What differs.** Inputs: the profiler's default is uniform integers in [−4, 4]; ours are small multiples of 1/4.
  Both are exact in bf16 and have few mantissa bits; whether tensor-core power, and so clocks, depends on it here is
  unknown, so compare clocks too. L2 at 4096³: see 8.4. CUTLASS's verification runs once before timing and does not
  affect the time.
- **Not like with like:** example 70 (`70_blackwell_fp16_gemm`) is fp16, column-major C, with a float C source (which
  reserves C's staging buffers, so fewer stages) and a 256×128 2×2 configuration, and its timing loop calls
  `gemm.initialize` every iteration (`70_blackwell_fp16_gemm.cu` 416-419). As a fallback if the profiler build fails,
  it can be made bf16 with row-major C and D; it stays a cross-check, not the reference:

```bash
cd ~/cutlass && sed -i -e 's/= half_t;/= cutlass::bfloat16_t;/' \
  -e 's/LayoutC     = cutlass::layout::ColumnMajor;/LayoutC     = cutlass::layout::RowMajor;/' \
  examples/70_blackwell_gemm/70_blackwell_fp16_gemm.cu && grep -n 'Element[AB]    =\|LayoutC     =' examples/70_blackwell_gemm/70_blackwell_fp16_gemm.cu
cd ~/cutlass && time cmake --build build --target 70_blackwell_fp16_gemm -j"$(nproc)"
cd ~/cutlass && for S in 8192 4096; do ./build/examples/70_blackwell_gemm/70_blackwell_fp16_gemm --m=$S --n=$S --k=$S --iterations=100; done
```

### 8.8 The pair GEMM against CUTLASS

Our `gemm_pair` (`encoding/examples/gemm_pair.rac`, `encoding/TWO_CTA.md` §6 step 4) is §7's items 1–4 together:
2-SM 256×256×64 tiles, cluster 2×1, six stages of 32 KiB, two accumulators of 256 columns, a TMA-store epilogue in
128×32 subtiles through 32 KiB of staging, and a static persistent grid of one pair per two SMs, in bands of 8 tile
rows.

**The like-for-like kernel** among §8.2's eight is `${K}_256x256x64_2x1x1_0_tnt_align8_2sm`.
- **The same:** the problem (`tnt`, void C, f32 D), the MMA tile, the cluster, six stages, two accumulators, 32 KiB
  of staging.
- **Different:**
  - the scheduler: CUTLASS's CLC (§5) against our static grid (§7 item 7 expects a few percent at 8192³);
  - the order: CUTLASS's raster heuristic, swizzle off, against our bands;
  - the staging: CUTLASS's two 128×32 buffers, one TMA store each after a named barrier of the warpgroup, against our
    two 32×32 buffers per warp, each warp's lane 0 storing and waiting for its own;
  - the loads: CUTLASS's `tcgen05.ld.32x32b.x32` and one `wait::ld` per tile, against four `.x8` and a `wait::ld` per
    chunk;
  - the release: CUTLASS releases the accumulator right after the tile's last load; we release it after the last
    chunk's store is issued;
  - CUTLASS issues each subtile's store one iteration late (`DelayTmaStore`, §4), to overlap it with the next
    subtile's loads; we issue it in its own iteration, after loading the chunk before waiting for its buffer;
  - the scopes: `.release.cluster` and `.acquire.cluster` on cross-CTA barriers (`encoding/TWO_CTA.md` §7
    decision 3), where CUTLASS uses `.cta`.
- **Cross-checks:** the run-time-cluster kernel at cluster 2×1, and §8.5's raster sweep of the 2×1 kernel, which shows
  how much order matters to CUTLASS.

**Timing.** CUTLASS's `Runtime` is the mean over its profiling iterations. Our harness prints the median, the fastest
and the mean of 100 runs after 20 warm-up runs, each run between its own events. Compare means with means. Both reuse
one copy of the operands (`--workspace-count=1` below).

Here, generate the bundle, which holds every kernel's CUDA, the harnesses and the run scripts, and copy it to the box:

```bash
RACCOON=… gpu/encoding/harness/run_gemm_pair.sh gen ~/bundle
```

On the box, after §8.1–8.3, our kernel and then CUTLASS's, in one session:

```bash
cd ~/bundle && sh run_gemm_pair.sh run
```

```bash
cd ~/cutlass && for S in 8192 4096; do build/tools/profiler/cutlass_profiler --operation=Gemm \
  --kernels="${K}_256x256x64_2x1x1_0_tnt_align8_2sm" --m=$S --n=$S --k=$S --alpha=1 --beta=0 --workspace-count=1 \
  --providers=cutlass --verification-providers=device --warmup-iterations=20 --profiling-iterations=100 \
  --output=pair_$S.csv && summ pair_$S.gemm.csv; done
```

```bash
cd ~/cutlass && build/tools/profiler/cutlass_profiler --operation=Gemm --kernels="${K}_256x256x64_0x0x1_0_tnt_align8_2sm" \
  --m=8192 --n=8192 --k=8192 --alpha=1 --beta=0 --cluster_m=2 --cluster_n=1 --cluster_m_fallback=2 --cluster_n_fallback=1 \
  --workspace-count=1 --providers=cutlass --verification-providers=device --warmup-iterations=20 \
  --profiling-iterations=100 --output=pair_cluster.csv && summ pair_cluster.gemm.csv
```

`run_gemm_pair.sh run` records the SM clock before and after its timing; record CUTLASS's the same way (§8.6).
