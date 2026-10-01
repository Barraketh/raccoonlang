# Two CTAs, one pair: `cta_group::2` in the core

Status: design, not implemented (2026-10-01). The facts are in `gpu/encoding/TWO_CTA_FACTS.md`: FA4 at `616b0e8`,
CUTLASS at `0b55a2f` and PTX 9.4, each with citations. "Facts §n" below refers to that note.

## 1. Why

Large GEMMs and long-sequence attention (the prefill side of paged attention) are competitive only with `cta_group::2`.
- **CUTLASS** runs its large GEMMs as a 2-SM 256×256 tile (`gpu/REFERENCE_CUTLASS.md` §1).
- **FA4** runs non-causal attention at head dimension 128 as a 2-CTA pair whenever there are more than 256 query rows
  and no split-KV (Facts §1.1).
- **What the pair buys:**
  - one MMA computes M = 256 rows, from A rows in both CTAs and B columns split between them;
  - each CTA loads half the B it multiplies with, so a stage is half as large and the ring twice as deep.
- **The bar.** The hardware bar for prefill is a 2-CTA kernel.

## 2. The pair, in brief

- **Launch.** A cluster of two CTAs, ranks 0 and 1 (`%cluster_ctarank`). Rank 0, the leader, issues every MMA and
  commit (Facts §1.3, §2).
- **Both CTAs run every other role:** the loader, the softmax or epilogue warpgroups, and the tensor-memory
  allocation.
- **Shared memory.** Each CTA holds its own half of every stage, at the same offsets in both. One descriptor addresses
  both halves (Facts §3.1).
- **Tensor memory.** Each CTA holds its own 128 rows of every accumulator, at the same columns (Facts §1.2).
- **Waits are local; arrivals cross** (Facts §3.6):
  - the peer's TMA completes bytes on the leader's full barrier;
  - the leader's commit arrives on both CTAs' barriers at once (multicast);
  - the peer's threads arrive on the leader's barriers by `mapa` and a remote `mbarrier.arrive`.

## 3. The encoding

**The pair kernel.** A builder, `pairKernel`, generates a kernel with `__cluster_dims__(2, 1, 1)`. With that attribute
the existing launcher's `cudaLaunchKernel` launches clusters (Facts §4); the launcher only requires an even grid x.
- **Body.** The builder gives the body the usual `Ctx(l, Group.cta(w))`, run by both CTAs, and a `Pair(l)`.
  - `Pair(l)` is a sealed, unrestricted handle to the kernel's pair, and only `pairKernel` makes one.
  - Every opener of a pair resource takes it.
- **Rank.** `rank(pair)` is a uniform `Val` (`%cluster_ctarank`).
- **The CTA group.** The builder records it in the generation state. Every `tcgen05` emitter prints its `.cta_group`
  from there, and the single-CTA openers (`withTmem`, `withAccRing`) refuse to generate in a pair kernel. So a kernel
  uses one group (A29) by construction, and a CTA-group mismatch is a generation error.

**The leader.** `onLeader(e, pair, body)` emits `if (rank == 0) { … }`. The body receives `Leader(m)`, a sealed
unrestricted fact that belongs to the arm's scope `m`.
- Every pair operation that issues tensor-core work or takes a consumer endpoint requires `Leader(m)`.
- It belongs to the arm's scope, so no code outside the arm can hold it.
- The peer's MMA warp runs nothing in a pair kernel but the collective allocation, which is not a leader operation.

This is P2's pattern (`gpu/encoding/P2.md` §2): a fact about run-time data, here the CTA's rank, scoped to the branch
where it holds.

**Initialization** (one sequence for every pair resource, emitted by `pairKernel` after the body's setup):
1. `mbarrier.init` of every barrier, in each CTA;
2. the setup arrivals that complete phase 0 of every barrier a producer waits on first, as today;
3. `fence.mbarrier_init.release.cluster`;
4. `barrier.cluster.arrive` (release, not relaxed, so that it also covers step 2) and `barrier.cluster.wait`.

Until step 4, no remote arrival, multicast commit or peer TMA can reach an uninitialized barrier.

**Closing: a cluster barrier before every pair close.** A pair ring's, the pair tensor memory's and a pair exchange's
closes each emit:
1. `__syncthreads`, as today, which joins the CTA's roles;
2. `barrier.cluster.arrive` and `barrier.cluster.wait`, which join the pair;
3. the close's own instructions: `mbarrier.inval`, or `tcgen05.dealloc.cta_group::2` by the allocating warp in each CTA.

Each side's finisher has drained before its role joins (M15). So by step 2:
- every arrival aimed at a CTA from its peer has been performed;
- every TMA into it has completed;
- every MMA reading its shared memory or tensor memory has completed.

The kernel's last close is followed only by exit, and a CTA exits after the cluster barrier, so neither CTA exits
while its peer can reach it (A51 below).

This replaces CUTLASS's per-resource handshakes (Facts §2, "TMEM handshake"). It also leaves no unwaited arrivals, as
FA4's final correction release does (Facts §1.8). Every arrival is drained by its finisher, and every close follows a
cluster barrier. Both CTAs run the same closes in the same order, so a collective dealloc cannot hang behind the
peer's cluster barrier (Facts §3.2).

**Pair rings** (`withPairRing(e, pair, cfg, X, body)`). Each stage is two halves, one in each CTA, at the same offset.
Barriers exist in both CTAs; the leader's `full[s]` and both CTAs' `empty[s]` are used.
- **Producer side, one per CTA** (the loader's elected lane in each).
  - `acquire` waits the CTA's own `empty[s]`.
  - `fill` issues the CTA's half with `cp.async.bulk.tensor….cta_group::2`, completing on the leader's `full[s]`
    through `mapa(full[s], 0)`.
  - In the leader, `fill` first arms `full[s]` with both halves' bytes.
  - The half and the bytes are computed by the core from the ring's configuration. The client gives the map and the
    coordinates of the CTA's half, as today.
- **Consumer side, leader only.** `takeConsumer` needs `Leader(m)`.
  - `await` waits the leader's `full[s]`, so both halves have landed.
  - `releaseByMma` commits with `.multicast::cluster` and mask `0b11`, which arrives on `empty[s]` in both CTAs.
- **Lockstep.** The producer in each CTA and the consumer in the leader walk one stage sequence. Their counts agree by
  the same trip count, as within a CTA. A disagreement deadlocks (M11): the extra fills of a CTA wait in its producer
  tail for releases that never come, and it never reaches the cluster barrier.

**Pair tensor memory** (`withPairTmem(e, pair, permit, X, body)`).
- **Allocation.** Always all 512 columns, by warp 0 of each CTA, with `tcgen05.alloc.cta_group::2`. A 512-column
  allocation starts at column 0, so both CTAs' addresses are equal without A47's CUTLASS-only premise. FA4 does the
  same (Facts §1.2).
- **Each CTA's region.** Each CTA's `Tmem(a, 512)` is its own 128 lanes. The MMA writes both CTAs' regions at one
  address. `splitTmem` works on it as today.
- **Release.** Relinquish follows the allocation; dealloc comes after the close's cluster barrier.

**Pair accumulator ring** (GEMM) and **pair exchange** (attention's overlaid S/P buffer, `gpu/encoding/A3.md` §3).
- The leader commits "full" with mask `0b11`, and each CTA's warpgroup waits its own copy.
- The warpgroups of both CTAs arrive "empty" or "P ready" on the leader's copy, by
  `mbarrier.arrive.release.cluster.shared::cluster` at `mapa(bar, 0)`; the count is 256.
- The leader's own warpgroup uses the same remote form: `mapa(bar, 0)` in rank 0 is its own address. So the
  warpgroup's code is the same in both CTAs.
- **Rows.** A thread's tensor-memory row is its CTA's: lane `32·(warp mod 4) + lane` (M12). Its global row adds
  `128 · rank` within the M = 256 tile.

**Scopes.** Remote arrivals use `.release.cluster`, and waits on barriers that receive them use `.acquire.cluster`
(the ISA's and the CUDA guide's pattern; Facts §3.6). FA4 and CUTLASS use `.cta` for speed. Measuring the difference is
a hardware item, and `.cta` is a later, separately argued change.

## 4. Why it is safe

The pieces of `docs/SEPARATION_PILOT.md` now span two CTAs. The rules carry over with three additions.
- **A pair stage is one piece of two halves.**
  - Each CTA's producer holds its own half from `acquire` to `fill`.
  - The leader's consumer holds both halves from `await` to `releaseByMma`, through the leader's `full[s]` (both
    halves' bytes) and both CTAs' `empty[s]` (one multicast commit).
  - The round argument of the pilot's §4 holds per CTA. Each `empty[s]` has count 1 and receives exactly the leader's
    commits for stage `s`.
- **A pair accumulator or exchange buffer is one piece of two halves**: the same rows of both CTAs' tensor memory. The
  tensor cores hold both halves, or both CTAs' warpgroups hold their own.
  - The handoff to the warpgroups is one multicast commit, observed per CTA.
  - The handoff back is 256 arrivals on the leader's barrier: both warpgroups, each with `tcgen05.wait` and
    `fence::before_thread_sync` first (M13 across the pair, A49).
- **Lifetimes span the pair.** A pair resource closes only after a cluster barrier that follows both CTAs' drained
  finishers. So no access to a CTA's shared memory, barriers or tensor memory outlives it.
- **Agreement.** Every offset is computed at generation time by code that both CTAs run, so both CTAs' layouts are
  equal by construction. The tensor-memory base is column 0 (512 columns). Rank is the only per-CTA run-time
  difference, and it selects roles and rows, never addresses of pair resources. `mapa(·, 0)` names the leader's copy.

## 5. Assumptions

New, numbered when they land, so as not to collide with A3a's A39 and P2's additions. The confidence column says how
much of each comes from the PTX text alone.

| Name | Statement | Basis | Confidence |
|---|---|---|---|
| Cluster launch | `__cluster_dims__(2,1,1)` makes `cudaLaunchKernel` launch pairs. Grid x is even. Ranks 0 and 1 form one CTA pair | PTX §11.7.1, §9.7.18.5.1 | medium: launch via the attribute is inferred |
| Cluster barrier | `barrier.cluster.arrive` (release) then `wait` (acquire) by every thread of both CTAs orders all prior accesses before all later ones | PTX §9.7.15.3 | high |
| Barrier publication | init, `fence.mbarrier_init.release.cluster`, cluster barrier: barriers usable by the peer | PTX §9.7.15.4 | high |
| Remote arrive | `mapa` then `mbarrier.arrive.release.cluster.shared::cluster` arrives once on the peer's barrier; an `.acquire.cluster` wait observing the phase synchronizes with it | PTX §9.7.10.26, §9.7.15.16.16, §9.7.15.16.19 | high |
| Pair TMA | the `cta_group::2` copy writes its own CTA's half and completes its bytes on the leader's barrier; complete-tx may precede expect-tx within a phase | PTX §9.7.10.28.5.3, §9.7.15.16.6 | high |
| Pair MMA | M = 256 reads A rows and B columns from each CTA at one descriptor address, and writes D (or reads tensor-memory A) at one column address in each CTA's own lanes | PTX §9.7.18.10; the split is CUTLASS's | medium |
| Multicast commit | arrives once on each masked CTA's barrier after every earlier `::2` MMA of the thread completes, both CTAs' accesses included | PTX §9.7.18.12.1 | high (inclusion of peer accesses inferred) |
| Pair allocation | `alloc`, `relinquish` and `dealloc` `.cta_group::2` by warp 0 of each CTA, collectively. A 512-column allocation is at column 0 in both | PTX §9.7.18.7.1, §9.7.18.5 | high |
| Pipelined pair across CTAs | A33 holds for `::2`, in both CTAs' tensor memory | PTX §9.7.18.6.2 ("same N") | medium |
| Fences across the pair | `tcgen05.fence::*_thread_sync` compose with cluster-scope arrive and wait as within a CTA | PTX §9.7.18.6.3, §9.7.18.11.1 | medium (no CTA restriction stated) |
| Cross-CTA async proxy | a TMA write into one CTA's shared memory and an MMA read of it issued by the other CTA are ordered by the barrier chain alone | not in PTX (§8.9.5 is "same thread block"); CUTLASS and FA4 rely on it | **low–medium: probe it on hardware, and ask NVIDIA** |
| Own tensor memory | `tcgen05.ld/st` reach only the executing CTA's tensor memory | PTX §9.7.18.8 | high |

The `MODELS.md` changes:
- §1.2's "a negative tx does not happen" no longer holds;
- A7's "then a CTA barrier" becomes the cluster sequence above;
- O1 and O2 gain the cross-CTA case under the async-proxy assumption.

## 6. Plan

1. **Core:**
   - `pairKernel`, `Pair`, `rank`, `onLeader`/`Leader`;
   - the CTA group in the generation state, read by the `tcgen05` emitters;
   - `withPairRing`, `withPairTmem`, a pair accumulator ring;
   - the cluster-barrier closes and initialization;
   - `mapa`, remote arrive, multicast commit and the `::2` TMA as instruction templates.
   The single-CTA examples must stay byte-identical.
2. **Pair TinyGEMM** (`examples/tinygemm_pair.rac`): a 256×256 output tile per pair, each CTA 128×256. Stages are A
   128×64 plus half of B, 128×64, per CTA. The accumulator is 2 × 256 columns, and each CTA stores its own rows. It
   comes with a harness (mock-validated) and mutants:
   - a consumer outside `onLeader`;
   - a single-CTA opener in a pair kernel;
   - a pair close without the cluster barrier (refused by construction: the close emits it);
   - a fill with the wrong half.

   It settles the protocol shape, not performance: it is not persistent, and its epilogue stores scalars.
3. **Pair attention:** A3a's schedule on pair rings, a pair exchange and pair tensor memory, after A3b.
4. **For competitiveness, separately:** the TMA-store epilogue and a persistent schedule
   (`gpu/REFERENCE_CUTLASS.md` §7, items 1 and 7; `gpu/ATTENTION.md` §6). Without them neither kernel reaches
   CUTLASS's or FA4's time, whatever the MMA.
5. **Hardware probes on the first session:**
   - the cross-CTA async-proxy ordering;
   - the operand split;
   - `.cluster` against `.cta` scope on remote arrivals.

## 7. Decisions

1. **The leader is rank 0**, as CUTLASS and FA4 have it. PTX allows either CTA to issue.
2. **`mapa` for every peer address**, not CUTLASS's undocumented bit-24 clear.
3. **`.release.cluster` / `.acquire.cluster`** on every cross-CTA barrier, rather than FA4's and CUTLASS's `.cta`,
   until measured and argued.
4. **A cluster barrier before every pair close**, rather than per-resource handshakes, and no unwaited arrivals.
5. **512 columns per pair allocation**, so both CTAs' tensor-memory addresses are equal (column 0) without trusting
   CUTLASS's equal-address premise.
6. **The CTA group is a property of the kernel**, enforced at generation, rather than an index of every context
   type.
7. **`Leader(m)` is a scoped fact**, the same pattern as P2's `Claimed`.
8. **`__cluster_dims__`** rather than a cluster launch attribute in the launcher, while the attribute suffices.
