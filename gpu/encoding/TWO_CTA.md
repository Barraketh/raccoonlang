# Two CTAs, one pair: `cta_group::2` in the core

Status: steps 1 and 2 of §6 built (2026-10-01): the core's pair sections in `Core.rac`, `examples/tinygemm_pair.rac`,
`harness/tinygemm_pair_test.cu` (run against a host mock), `rejected/tinygemm_pair_mutants.py`, and `OBLIGATIONS.md`
(A43–A55, M18–M20, §6.12). Nothing has run on a GPU. §8 says what building changed. The facts are in
`gpu/encoding/TWO_CTA_FACTS.md`: FA4 at `616b0e8`, CUTLASS at `0b55a2f` and PTX 9.4, each with citations. "Facts §n"
below refers to that note.

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

**The pair kernel.** A pair kernel's launcher has the grid `Grid.pairs(x, y)`: `x` × `y` pairs, launched as `2x` × `y`
CTAs. For such a grid the printer declares `__cluster_dims__(2, 1, 1)` on the kernel, with which the existing
`cudaLaunchKernel` launches clusters (Facts §4); the grid x is even by construction.
- **Builders.** `pairStart` is every pair kernel's prologue: it sets the CTA group and reads `%cluster_ctarank` and
  `%clusterid.x` once. `pairGemmKernel` is the pair GEMM's builder on it.
- **Body.** The builder gives the body the usual `Ctx(l, Group.cta(w))`, run by both CTAs, and a `CtaPair(l)`.
  - `CtaPair(l)` is a sealed, unrestricted handle to the kernel's pair, of the kernel's own lifetime `l`, and only a
    pair builder makes one. (It is not called `Pair`, the prelude's product type.)
  - Every opener of a pair resource takes it, with a context of the same lifetime (below).
- **Rank.** `rank(pair)` is a uniform `Val` (`%cluster_ctarank`). The pair's tile index is `%clusterid.x`, the same in
  both CTAs, so it relies on nothing about which `blockIdx.x` a cluster's CTAs have.
- **The CTA group.** The builder records it in the generation state. Every `tcgen05` emitter prints its `.cta_group`
  from there, and the single-CTA openers (`withRing`, `withTmem`, `withAccHandoff`, `withAccRing`, `withExchange`,
  `withScoreBuffer`) refuse to generate in a pair kernel. So a kernel uses one group (A29) by construction, and a
  CTA-group mismatch is a generation error. All six refuse, not only the two that allocate or split tensor memory:
  `withPairTmem` hands out an ordinary `Tmem` and `Acc`, which every single-CTA protocol would otherwise accept, and a
  single-CTA ring's consumer issues commits.

**Where pair openers run.** A pair opener (`withPairTmem`, `withPairRing`, `withPairAccRing`) takes the kernel's own
context, `Ctx(l, …)` with the `CtaPair(l)` of the same `l`. A branch arm, loop body, role, split side or `onLeader` arm
has a lifetime of its own, so no pair opener can run there; the openers nest only in each other's callbacks, which
keep `l`. So every thread of both CTAs runs every opener and every close, in one order, generated once: both CTAs'
layouts and cluster barriers match by construction.

**The leader.** `onLeader(e, pair, body)` emits `if (rank == 0) { … }`. The body receives `Leader(m)`, a sealed
unrestricted fact that belongs to the arm's scope `m`, and hands back only its context.
- The endpoints that issue tensor-core work, a pair ring's consumer and a pair accumulator ring's issuing side, are
  taken only with a `Leader` (`takePairConsumer`, `takePairAccProducer`). Every MMA and commit consumes a token
  derived from them, so it runs in the arm without taking a `Leader` itself.
- It belongs to the arm's scope, so no code outside the arm can hold it.
- The peer's MMA warp runs nothing in a pair kernel; the collective allocation is warp 0's, in the kernel's spine.

This is P2's pattern (`gpu/encoding/P2.md` §2): a fact about run-time data, here the CTA's rank, scoped to the branch
where it holds.

**Initialization** (one sequence per pair protocol, emitted by its opener before its callback runs):
1. `mbarrier.init` of each of its barriers, in each CTA, by thread 0;
2. the setup arrivals that complete phase 0 of every barrier a producer waits on first, as today;
3. `fence.mbarrier_init.release.cluster`, by thread 0;
4. `barrier.cluster.arrive.release.aligned` (release, not relaxed, so that it also covers step 2) and
   `barrier.cluster.wait.acquire.aligned`, by every thread of both CTAs, in place of the single-CTA protocols'
   `__syncthreads`.

Until step 4, no remote arrival, multicast commit or peer TMA can reach an uninitialized barrier. The openers nest, so
no one point after every opener's inits and before the roles is known to a builder: each opener publishes its own
barriers, one cluster barrier each. The pair GEMM runs two.

**Closing: a cluster barrier before every pair close.** A pair ring's, a pair accumulator ring's and the pair tensor
memory's closes each follow the roles' join (the `__syncthreads` of the split inside the callback, as today), and emit:
1. `barrier.cluster.arrive` and `barrier.cluster.wait`, which join the pair (for tensor memory, between
   `tcgen05.fence::before_thread_sync` and `::after_thread_sync`);
2. the close's own instructions: `mbarrier.inval` by thread 0, or `tcgen05.dealloc.cta_group::2` by warp 0 in each CTA.

Each side's finisher has drained before its role joins (M15). So by step 2:
- every arrival aimed at a CTA from its peer has been performed;
- every TMA into it has completed;
- every MMA reading its shared memory or tensor memory has completed.

The kernel's last close is followed only by exit, and a CTA exits after the cluster barrier, so neither CTA exits
while its peer can reach it (A55).

This replaces CUTLASS's per-resource handshakes (Facts §2, "TMEM handshake"). It also leaves no unwaited arrivals, as
FA4's final correction release does (Facts §1.8). Every arrival is drained by its finisher, and every close follows a
cluster barrier. Both CTAs run the same closes in the same order, so a collective dealloc cannot hang behind the
peer's cluster barrier (Facts §3.2).

**Pair rings** (`withPairRing(e, pair, cfg, X, body)`). Each stage is two halves, one in each CTA, at the same offset.
Barriers exist in both CTAs; the leader's `full[s]` and both CTAs' `empty[s]` are used. The sides are the ring's
(`Producer`, `Consumer` and their tokens); the operations take the sealed `PairRing`, which no single-CTA operation
takes.
- **Producer side, one per CTA** (the loader's elected lane in each).
  - `acquirePair` waits the CTA's own `empty[s]`.
  - `fillPair` issues the CTA's half with `cp.async.bulk.tensor….cta_group::2`, completing on the leader's `full[s]`
    through `mapa(full[s], 0)`.
  - In the leader, `fillPair` first arms `full[s]` with both halves' bytes.
  - The bytes are computed by the core from the ring's configuration, and the half from the rank: the sealed
    `PairTile` the builder makes holds this CTA's rows of A (`row0 + 128·rank`) and of B (`col0 + bh·rank`). The
    client gives the maps and the K coordinate only, so a fill of the other CTA's half cannot be written.
- **Consumer side, leader only.** `takePairConsumer` needs a `Leader`.
  - `awaitPair` waits the leader's `full[s]`, so both halves have landed.
  - `releasePair` commits with `.multicast::cluster` and mask `0b11`, which arrives on `empty[s]` in both CTAs. The mask
    is a `.b16` register set in the instruction's own block (`mov.b16 mask, 3`), since an inline-assembly operand of
    16 bits would need a 16-bit C type the AST does not have.
- **Lockstep.** The producer in each CTA and the consumer in the leader walk one stage sequence. Their counts agree by
  the same trip count, as within a CTA. A disagreement deadlocks (M11): the extra fills of a CTA wait in its producer
  tail for releases that never come, and it never reaches the cluster barrier.

**Pair tensor memory** (`withPairTmem(e, pair, permit, done, X, body)`, `withTmem`'s callback).
- **Allocation.** Always all 512 columns, by warp 0 of each CTA, with `tcgen05.alloc.cta_group::2`. A 512-column
  allocation starts at column 0, so both CTAs' addresses are equal without CUTLASS's premise that they are (Facts
  §5.2, A47). FA4 does the same (Facts §1.2).
- **Each CTA's region.** Each CTA's `Tmem(a, 512)` is its own 128 lanes. The MMA writes both CTAs' regions at one
  address. `splitTmem` works on it as today.
- **Release.** Relinquish follows the allocation; dealloc comes after the close's cluster barrier.

**Pair accumulator ring** (GEMM, `withPairAccRing`, built) and **pair exchange** (attention's overlaid S/P buffer,
`gpu/encoding/A3.md` §3, step 3).
- The leader commits "full" with mask `0b11`, and each CTA's warpgroup waits its own copy.
- The warpgroups of both CTAs arrive "empty" or "P ready" on the leader's copy, by
  `mbarrier.arrive.release.cluster.shared::cluster` at `mapa(bar, 0)`; the count is 256.
- The leader's own warpgroup uses the same remote form: `mapa(bar, 0)` in rank 0 is its own address. So the
  warpgroup's code is the same in both CTAs.
- **Rows.** A thread's tensor-memory row is its CTA's: lane `32·(warp mod 4) + lane` (M12). Its global row adds
  `128 · rank` within the M = 256 tile, which the core takes from the `PairTile` (`storeHalf`).
- **The GEMM's epilogue** (`storeHalf`) is scalar: each thread loads its row 8 columns at a time, in a loop, and stores
  each element that lies inside C. A CTA's `HalfOwn`, linear, is the authority to write its half once.

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
    `fence::before_thread_sync` first (M13 across the pair, A52).
- **Lifetimes span the pair.** A pair resource closes only after a cluster barrier that follows both CTAs' drained
  finishers. So no access to a CTA's shared memory, barriers or tensor memory outlives it.
- **Agreement.** Every offset is computed at generation time by code that both CTAs run, so both CTAs' layouts are
  equal by construction. The tensor-memory base is column 0 (512 columns). Rank is the only per-CTA run-time
  difference, and it selects roles and rows, never addresses of pair resources. `mapa(·, 0)` names the leader's copy.

## 5. Assumptions

Numbered A43–A55 in `OBLIGATIONS.md` §3, after P2's A40–A42, in this table's order, with A55 for the exit rule of §3.
The confidence column says how much of each comes from the PTX text alone.

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
| Peer lifetime | nothing is assumed of an access to a CTA that has exited or closed the resource: every remote access precedes the close's cluster barrier | PTX §2.2.2 | — (a design choice) |

The `MODELS.md` changes:
- §1.2's "a negative tx does not happen" no longer holds;
- A7's "then a CTA barrier" becomes the cluster sequence above;
- O1 and O2 gain the cross-CTA case under the async-proxy assumption.

## 6. Plan

1. **Core** (built):
   - `pairStart`, `CtaPair`, `rank`, `onLeader`/`Leader`;
   - the CTA group in the generation state, read by the `tcgen05` emitters;
   - `withPairRing`, `withPairTmem`, a pair accumulator ring;
   - the cluster-barrier closes and initialization;
   - `mapa`, remote arrive, multicast commit and the `::2` TMA as instruction templates.
   The single-CTA examples generate byte-identical code.
2. **Pair TinyGEMM** (`examples/tinygemm_pair.rac`, built): a 256×256 output tile per pair, each CTA 128×256. Stages are
   A 128×64 plus half of B, 128×64, per CTA, in a ring of four. The accumulator ring is 2 × 256 columns, of which the
   one tile uses the first, and each CTA stores its own rows. It comes with a harness (mock-validated) and mutants:
   - a consumer outside `onLeader`, and the `Leader` handed out of its arm;
   - a single-CTA opener in a pair kernel;
   - a pair opener under `onLeader`;
   - a fill of the caller's coordinates and barrier, and one of a forged half;
   - a store of the other CTA's rows;
   - a close with each side unfinished. A close without the cluster barrier needs no mutant: the close emits it.

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
8. **`__cluster_dims__`** rather than a cluster launch attribute in the launcher, while the attribute suffices. The
   printer declares it for a launcher whose grid is `Grid.pairs`.
9. **Pair openers take the kernel's own context**, so that both CTAs run them all, in one order.
10. **The core computes each CTA's half**, for fills and stores, from the rank.

## 8. What building changed

Against the design as first written:
- `Pair(l)` is `CtaPair(l)`: `Pair` is the prelude's product type.
- `pairKernel` is split into `pairStart`, the prologue every pair kernel shares, and `pairGemmKernel`. The cluster
  shape comes from the launcher's grid, `Grid.pairs`, which the printer, `Check` and `Spec` know.
- The pair's tile index is `%clusterid.x`, not `blockIdx.x / 2`.
- Pair openers take the kernel's own context (§3, "Where pair openers run"). Without it, an opener under a branch on
  the rank would give the CTAs different layouts.
- Initialization is one sequence per opener, not per kernel, since the openers nest.
- The close emits no `__syncthreads` of its own: the roles' join precedes it.
- All six single-CTA openers refuse in a pair kernel, not only `withTmem` and `withAccRing`.
- `Leader` is required where the tensor-core endpoints are taken, not by every MMA and commit.
- The core, not the client, computes a CTA's half for fills, so a wrong half is unwritable.
- The multicast commit's mask is a `.b16` register in the template.
