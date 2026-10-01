# Two CTAs, one pair: `cta_group::2` in the core

Status: steps 1 and 2 of §6 built (2026-10-01): the core's pair sections in `Core.rac`, `examples/tinygemm_pair.rac`,
`harness/tinygemm_pair_test.cu` (run against a host mock), `rejected/tinygemm_pair_mutants.py`, and `OBLIGATIONS.md`
(A43–A56, M18–M20, §6.12). Step 4's GEMM built (2026-10-01): the persistent pair GEMM, `examples/gemm_pair.rac`, with
its harness (run against a host mock), its run script and mutants, and `OBLIGATIONS.md` (A60, M10, M18, §6.12).
Nothing has run on a GPU. §8 says what building steps 1 and 2 changed, §9 how step 4 is built. The facts are in
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
- **Rank.** The rank (`%cluster_ctarank`) is the core's: it chooses the leader's arm and each CTA's half, and no
  operation hands it to client code. An `onLeader` arm, which runs in the leader only, hands back only its context and
  writes no register declared outside it. So no loop count or branch of the client's can differ between the CTAs
  (M18).
  The pair's tile index is `%clusterid.x`, the same in both CTAs, so it relies on nothing about which `blockIdx.x` a
  cluster's CTAs have.
- **The CTA group.** The builder records it in the generation state. Every `tcgen05` emitter prints its `.cta_group`
  from there, and the single-CTA openers (`withRing`, `withTmem`, `withAccHandoff`, `withAccRing`, `withExchange`,
  `withScoreBuffer`) refuse to generate in a pair kernel. So a kernel uses one group (A29) by construction, and a
  CTA-group mismatch is a generation error. All six refuse, not only the two that allocate or split tensor memory:
  `withPairTmem` hands out an ordinary `Tmem` and `Acc`, which every single-CTA protocol would otherwise accept, and a
  single-CTA ring's consumer issues commits.
- **What the group prints.** Besides `.cta_group`, the group chooses the form of every barrier wait (`.acquire.cluster`
  in a pair kernel) and commit (multicast to both CTAs, mask `0b11`). So a pair ring's and a pair accumulator ring's
  waits, releases, commits and drains are the single-CTA operations' own code.

**Where pair openers run.** A pair opener (`withPairTmem`, `withPairRing`, `withPairAccRing`) takes the kernel's own
context, `Ctx(l, …)` with the `CtaPair(l)` of the same `l`. A branch arm, loop body, role, split side or `onLeader` arm
has a lifetime of its own, so no pair opener can run there; the openers nest only in each other's callbacks, which
keep `l`. So every thread of both CTAs runs every opener and every close, in one order, generated once: both CTAs'
layouts and cluster barriers match by construction.

**The leader.** `onLeader(e, pair, only, sides, body)` emits `if (rank == 0) { … }`. The body receives `Leader(m)`, a
sealed unrestricted fact that belongs to the arm's scope `m`, and `sides`, and hands back only its context.
- The arm captures no linear value: what it uses up, only the leader runs. It uses up only `sides`, whose evidence
  `only: LeaderOnly(S)` says they are the leader's alone: a pair ring's consumer (`leaderOnlyConsumer(ring)`), a pair
  accumulator ring's issuing side (`leaderOnlyAccProducer(accs)`), pairs of them, or nothing. A producer or the
  storing side, whose finisher each CTA must run, cannot enter it.
- The arm writes no register declared outside it (`set` refuses at generation), so nothing the leader alone computes
  reaches code both CTAs run.
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

Nested resources close one after another, each with its own cluster barrier, so the pair GEMM ends with three in a
row where the first would order what the later two need: a known small cost, not optimized.

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
  allocation starts at column 0, so both CTAs' addresses are equal without CUTLASS's premise that they are (A50). FA4
  does the same (Facts §1.2).
- **One CTA per SM.** PTX does not say whether the first warp of a `::2` allocation holds its columns while it waits
  for the peer's, so two clusters sharing two SMs could each hold one SM's 512 columns and wait for the other's. A pair
  kernel therefore asks for more than half of an SM's shared memory (`pairShared`, padding a smaller request), which
  keeps each of its CTAs alone on its SM (A56).
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

The pieces of `gpu/SEPARATION_PILOT.md` now span two CTAs. The rules carry over with three additions.
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

Numbered A43–A56 in `OBLIGATIONS.md` §3, after P2's A40–A42, in this table's order.
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
| One CTA per SM | a CTA asking for more than half of an SM's shared memory is alone on its SM, so no two clusters' 512-column allocations meet | CUDA guide (228 KB per SM); PTX §9.7.18.7.1 is silent on a waiting allocation | high |

The `MODELS.md` changes:
- §1.2's "a negative tx does not happen" no longer holds;
- A7's "then a CTA barrier" becomes the cluster sequence above;
- O1 and O2 gain the cross-CTA case under the async-proxy assumption.

## 6. Plan

1. **Core** (built):
   - `pairStart`, `CtaPair`, `onLeader`/`Leader`;
   - the CTA group in the generation state, read by the `tcgen05` emitters;
   - `withPairRing`, `withPairTmem`, a pair accumulator ring;
   - the cluster-barrier closes and initialization;
   - `mapa`, remote arrive, multicast commit and the `::2` TMA as instructions.
   The single-CTA examples generate byte-identical code.
2. **Pair TinyGEMM** (`examples/tinygemm_pair.rac`, built): a 256×256 output tile per pair, each CTA 128×256. Stages are
   A 128×64 plus half of B, 128×64, per CTA, in a ring of four. The accumulator ring is 2 × 256 columns, of which the
   one tile uses the first, and each CTA stores its own rows. It comes with a harness (mock-validated) and mutants:
   - a consumer outside `onLeader`, and the `Leader` handed out of its arm;
   - a single-CTA opener in a pair kernel;
   - a pair opener under `onLeader`;
   - a fill of the caller's coordinates and barrier, and one of a forged half;
   - a store of the other CTA's rows, and one past the tile's columns;
   - a close with each side unfinished. A close without the cluster barrier needs no mutant: the close emits it.

   It settles the protocol shape, not performance: it is not persistent, and its epilogue stores scalars.
3. **Pair attention:** A3a's schedule on pair rings, a pair exchange and pair tensor memory, after A3b.
4. **For competitiveness, separately:** the TMA-store epilogue and a persistent schedule
   (`gpu/REFERENCE_CUTLASS.md` §7, items 1 and 7; `gpu/ATTENTION.md` §6). Without them neither kernel reaches
   CUTLASS's or FA4's time, whatever the MMA.
   - **The GEMM** (built, §9): `examples/gemm_pair.rac`, REFERENCE_CUTLASS §7 items 1–4 together, CUTLASS's 2-SM
     256×256×64 configuration with a static persistent schedule. It comes with `harness/gemm_pair_test.cu` (run
     against a host mock), `harness/run_gemm_pair.sh` for the hardware session (REFERENCE_CUTLASS §8.8), and
     `rejected/gemm_pair_mutants.py`.
   - **Attention:** not built; it waits for step 3.
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
- The multicast commit's mask is a `.b16` register in the instruction's PTX block.
- The CTA group chooses the barrier waits' and commits' form as well as `.cta_group`, so the pair rings' waits,
  releases, commits and drains are the single-CTA operations, not copies with other instructions.
- `rank` is not exported: a rank-dependent trip count of the client's would deadlock the pair (review).
- A pair kernel asks for at least `pairShared` bytes of shared memory, one CTA per SM (review).
- `PairTile` records the tile's width, which `storeHalf` requires of the buffer (review); since step 4's review, in its
  type, `PairTile(l, w)`.
- Since step 4's review, an `onLeader` arm captures no linear value and is handed only leader-only sides (a pair
  ring's consumer, a pair accumulator ring's issuing side): an arm that captured a producer or the storing side could
  run its finisher in the leader alone, and the peer would close with copies or stores in flight.

## 9. Step 4 as built: the persistent pair GEMM

`Core.rac`'s section "CTA pairs: the persistent GEMM" and `examples/gemm_pair.rac`.

**The problem and the tiles.** REFERENCE_CUTLASS's `tnt` problem. A pair computes a 256×256 tile of C; each CTA loads
128 rows of A and 128 of the tile's 256 rows of B per stage, and stores its own 128 rows of the tile.

**The schedule.**
- `pairGemmPersistentKernel` reads `%nclusterid.x` besides the rank and `%clusterid.x`, and declares the single-CTA
  schedule's counts (`schedule`) for tiles of 256 × 256.
- Each pair visits the tile indices from `%clusterid.x` in steps of `%nclusterid.x`, in the band order of the
  single-CTA persistent GEMM, bands of `band` = 8 tile rows (2048 rows of A, as G = 16 at 128-row tiles).
- Both CTAs compute the sequence from values that are the same in both (A43, A60), so they visit one tile sequence by
  construction (M18). The sequence lives in `PairSched`, which only the pair loops take: the single-CTA loops' start,
  `blockIdx.x`, differs between the CTAs.
- No role's loop runs in one CTA only: an `onLeader` arm cannot capture a role's side (M20), so it can run no loop of a
  role both CTAs run; and it writes no register declared outside it, so no flag of the leader's can make code both
  CTAs run take another branch or count (M18).
- The launcher starts `2·min(SMs/2, tiles)` CTAs, as FA4's static persistent scheduler does (Facts §1.10).

**The roles** are tinygemm_pair's, inside a tile loop each (`forPairTiles`):
- each CTA's loader fills its half of one stage per K slice of every tile;
- the leader's issuer takes a free accumulator per tile, issues four MMAs of M = 256, N = 256 per stage, releases each
  stage by a multicast commit, and commits the accumulator to both CTAs;
- each CTA's warpgroup waits for its rows of the accumulator, stores them, and releases the accumulator to the
  leader. Only the epilogue's loop owns its tiles (`forOwnedPairTiles`, `HalfOwn`).

**The rings.** A pair ring of six stages of 32 KB per CTA, and a pair accumulator ring of two buffers of 256 columns,
all 512 columns. Both rings' stages and phases continue from tile to tile.

**The epilogue.** The single-CTA TMA-store epilogue, unchanged, on the pair accumulator ring:
- `forHalfChunks` loops over the 8 chunks of 32 columns of this CTA's 128 rows, the rows from the `PairTile`;
- per chunk, each warp loads its 32 rows of the chunk into registers (`loadPairChunk`), waits until its store of two
  chunks ago has read its buffer (`acquireStage`), writes the chunk to the buffer (`writeStage`), fences it to the async
  proxy (`fenceStage`), and its lane 0 stores the 32×32 box and commits it (`storeStage`); the load comes first, so it
  does not wait behind the store;
- the staging buffers are per warp: two of 4 KB each, warp q's buffer b at byte `1024 + (2q + b)·4096`, 32 KB in all,
  so a 128×32 subtile is four TMA stores, one per warp;
- the warpgroup releases the accumulator after the tile's last chunk is loaded and its store issued, before any store
  completes, so the next tile's MMAs overlap the stores;
- after its last tile, each warp's lane 0 waits for every store to complete (`finishStores`), before the pair closes.
- The TMA store clips to the matrix (A34), so the edge tiles need no guard. The launcher requires N mod 4 = 0.

**Shared memory** per CTA: the tensor-memory slot (4 bytes), the accumulator ring's barriers (32), two staging buffers
per warp (32 KB, 1024-aligned from 1024), six stages (192 KB, from 33,792), the ring's barriers (96): 230,496 bytes.
`Check.sharedSize` refuses more than 232,448 when the kernel renders.

**Per tile**, with S = K/64 stages:

| | Leader | Each CTA |
|---|---|---|
| MMAs | 4S | |
| commits | S + 1 | |
| barrier waits | S + 1 (issuer) | S (loader), 1 per warpgroup thread |
| TMA loads | | 2S |
| TMA stores, commit groups | | 32 (8 per warp) |
| `wait_group.read 1` | | 32 (8 per warp) |
| remote arrivals | | 128 (one per warpgroup thread) |

**Approximations and open points.**
- The accumulator is released after the tile's last chunk is loaded and stored to its staging buffer, not right after
  the last load: a loop body is generated once, so code that runs in the last iteration only would need a peeled last
  chunk. The difference is one chunk's buffer wait, shared-memory writes and store issue.
- Each chunk loads with four `tcgen05.ld.32x32b.x8` and one `wait::ld`; CUTLASS loads a subtile with one `.x32` and
  waits once per tile.
- A 128×32 subtile is four 32×32 stores, one per warp, each warp waiting for its own groups (`withStaging`), where
  CUTLASS stores one 128×32 box after a named barrier of the warpgroup.
- The grid assumes every pair of SMs can hold a cluster. If fewer clusters are resident, the extra pairs run their
  whole tile sequences after the others: correct, but up to twice as slow. The runtime's
  `cudaOccupancyMaxActiveClusters` tells how many are resident; the launcher does not ask it. The first run's time
  will show it, against the pairs the harness prints.

