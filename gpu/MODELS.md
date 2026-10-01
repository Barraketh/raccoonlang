# GPU library: protocol models (verification layer 2)

Status: design for review. Nothing here is implemented. It designs layer 2 of `OBLIGATIONS.md` §8: abstract models of
the asynchronous hardware the protocols use (A6, A9, A12 and the ordering facts of A6–A14), the protocols of `Gpu.rac`
as transition systems over them, the safety properties those systems must have under every interleaving of their
roles, and how to prove them in Raccoon. The models are to live in `gpu/model/` as Raccoon modules that `Gpu` imports
(`OBLIGATIONS.md` §9, decisions 2 and 3).

The models describe `Gpu.rac` as of 0767971, with two later changes to the protocols: the setup's arrivals that
complete phase 0 of the barriers a producer waits on first, so producers start at phase 0 (§1.2), and the fence after
`await`'s wait (§1.6). `lemur_gpu` has also replaced the per-element epilogue with TMA stores
through staging buffers (975f093), a protocol of bulk async-groups and proxy fences that these models do not yet
cover. §6 says how they extend to it, and V1 (§7) must start from it.

In short:
- **Models** (§1): an mbarrier is a phase bit, a pending arrival count and a transaction count; a TMA copy and a
  tensor-core operation are asynchronous events that complete at any later time; `tcgen05.commit` is an arrival that
  waits for every earlier tensor-core operation of its thread. Accesses are intervals, and the ordering facts the
  protocols need reduce to "an interval ends before the arrival that a successful wait observes".
- **Protocols** (§2): the stage ring, the accumulator handoff, the accumulator ring and the shared-tile typestate, each
  as roles (program counter and registers) plus barriers, buffers and asynchronous units, with unbounded loops,
  asynchronous completions, the drain and invalidation.
- **Properties** (§3): generation-indexed statements, stronger than race freedom. The j-th read of a stage reads its
  j-th fill, every wait's parity test agrees with the phase its side means, and the roles join quiescent.
- **Proof** (§4): exhaustive exploration by an unverified search whose result, an inductive invariant, is checked by
  a small checker proved sound once. At S = 6 the faithful model has 1.0 to 1.3 million states, about two hours of
  evaluation (§4.1). The same finite check becomes generic in S (and, less securely, in the number of buffers and
  readers) by projecting the ring onto one stage: the projection of an S-stage ring is a stuttering of the one-stage ring, which has 88 states (with
  loops that may end at any wait).
  **Recommended, provisionally:** the projection route (§4.2), with per-configuration runs of the whole ring as
  cross-checks. A proof by invariants over linear, erased permissions, if Raccoon gains them, would use the same models
  and properties (§4.4).
- **Link to the library** (§5): at layer 2 a reviewer compares the model with the emitted code (§2.6). A cheap
  syntactic checker over the emitted AST can confirm each role's barrier operations, operands and order.

Rules cite the PTX ISA, version 9.4, by section number ("PTX §…"); section numbers change between versions. §1's
citations of the `mbarrier`, `cp.async.bulk.tensor`, `tcgen05` and memory-model rules were checked against the 9.4
text, and so were the ordering facts O1–O7 (§1.6). "Unknown" marks a question the documentation does not settle, as
far as this design found. Citations elsewhere in this document that give no section number were not checked.

## 1. Semantic models

### 1.1 Setting

A CTA is a set of threads and a set of asynchronous units. Its state is:
- each thread's program counter and registers;
- the shared objects: mbarriers, and buffers (shared-memory stages, tensor-memory columns);
- each asynchronous unit's operations in flight.

A step is one instruction of one thread, or one completion of one asynchronous operation, and every interleaving of
steps is a behaviour. No fairness is assumed, so any completion may be delayed arbitrarily. An instruction is atomic
unless a rule says otherwise. A wait loop (`mbarWait`'s spin on `try_wait`) is one guarded step: it is enabled when
the test would succeed. The failed tests change no state and are not modelled.

An access to a buffer is an interval, and is tagged with its proxy:
- a synchronous access (a generic-proxy load or store) is one step;
- an asynchronous access spans issue to completion: a TMA write from issue to its `complete_tx`, an MMA's reads and
  writes from issue to its completion, a `tcgen05.ld` from issue to the thread's `tcgen05.wait::ld`. TMA and the
  tensor cores access shared memory through the async proxy.

Two accesses race when they conflict (one location, at least one a write) and their intervals overlap in some
behaviour. This is how the model reads S1 for the protocols: §1.6 says why interval disjointness in every
interleaving is ordering by the memory model, given A6–A14.

### 1.2 The mbarrier

State of barrier `b`, and one ghost:

| Field | Values | Source |
|---|---|---|
| `ph(b)` | the current phase's parity, 0 or 1 | PTX §9.7.15.16.3: the current phase |
| `pend(b)` | pending arrivals of the current phase, 0 to `count(b)` | ibid., pending arrival count |
| `count(b)` | expected arrivals per phase, 1 to 2^20 − 1 | ibid., expected arrival count, Table 43 (`.layout::v0`, the default); §9.7.15.16.12 |
| `tx(b)` | transaction count of the current phase, −(2^20 − 1) to 2^20 − 1 | ibid., tx-count; §9.7.15.16.6 |
| `n(b)` (ghost) | completed phases, a natural number: `ph(b) = n(b) mod 2` | none (definition; §9.7.15.16.5.1 numbers the phases 0, 1, 2, …) |

Rules. Each names its instruction and ISA source.

| Rule | Instruction | Effect | Source |
|---|---|---|---|
| Init | `mbarrier.init.shared::cta.b64 [b], c` | `ph = 0`, `pend = c`, `count = c`, `tx = 0`, `n = 0` | PTX §9.7.15.16.12 |
| Arrive | `mbarrier.arrive.shared::cta.b64 _, [b]`, or with a count `c` (`…, [b], c`; 1 when absent) | if `pend < c`: error (P5); else `pend −= c`; then Complete | §9.7.15.16.9; §9.7.15.16.16 (`count` within Table 43's range) |
| ArriveTx | `mbarrier.arrive.expect_tx.shared::cta.b64 _, [b], x` | `tx += x`, then Arrive (`c = 1`), as one step | §9.7.15.16.16 (`.expect_tx` performs expect-tx before the arrive-on, whose count is 1); §9.7.15.16.6.1 |
| CompleteTx | a TMA copy's completion (§1.3) | `tx −= x`; then Complete | §9.7.15.16.6.2 |
| Complete | (part of the above) | if `pend = 0` and `tx = 0`: `ph ← 1 − ph`, `pend ← count`, `n += 1` | §9.7.15.16.8 |
| Wait | `mbarrier.try_wait.parity.shared::cta.b64 P, [b], p` in a loop | enabled iff `ph(b) ≠ p`; no effect | §9.7.15.16.19: `.parity` tests the completion of the phase of parity `p`, which must be the current phase or the one immediately before it |
| Inval | `mbarrier.inval.shared::cta.b64 [b]` | if not quiescent (below): error (P4); else `b` is no longer a barrier | §9.7.15.16.13 |

The **setup** of a protocol is Init of each of its barriers followed, for each barrier a producer waits on before
anyone arrives on it (the stage ring's `empty[s]`, count 1, and the accumulator ring's `accEmpty[b]`, count 128), by
one Arrive with `c = count`, by the same thread: that completes phase 0, so the barrier starts with `ph = 1`,
`pend = count`, `tx = 0`, `n = 1`. `withRing` and `withAccRing` emit it (`Gpu.barrierCompletions`); the handoff's
barrier, which no producer waits on, gets none.

Readings and gaps:
- **Wait.** `test_wait` and `try_wait` are defined only for the current, incomplete phase, where they return False,
  and the immediately preceding one, where they return True (§9.7.15.16.19). A wait whose parity names a phase two or
  more behind has no defined result: that is the ABA question. The model gives the defined cases the hardware's
  observable meaning, success iff `ph ≠ p`, and property P3 (§3) keeps every wait of the protocols in the defined set.
- **The fresh barrier.** A parity-1 wait on a barrier that has never completed a phase names a "preceding phase"
  that does not exist, so it is outside §9.7.15.16.19's defined set. Practice relies on its succeeding at once (CUTLASS's
  `make_producer_start_state`, DeepGEMM's `wait(phase ^ 1)` on its empty barriers), but the ISA does not say so. No
  protocol here relies on it any more: the setup completes phase 0 of every barrier a producer waits on first, so
  each producer starts at phase 0 and its first wait is on the immediately preceding phase, which is defined.
- **Over-arrival.** An arrive of `c` on a barrier with `pend < c` is an error in the model (P5). PTX is silent on it;
  the CUDA Programming Guide (§4.10.2) requires an arrival only while the barrier's counter is non-zero. So it stays
  undefined. PTX does state a related rule (§9.7.15.16.5.1): in each phase, at least one `test_wait` or `try_wait` must
  return True before any arrive-on of the next phase. That is property P8 (§3).
- **A negative `tx`.** In general a complete-tx may precede its expect-tx within a phase, and the phase cannot
  complete while `pend > 0`, so the model allows it. In the single-CTA protocols it does not happen:
  `arrive.expect_tx` precedes the copies in program order. In a pair ring (`encoding/TWO_CTA.md`) it does: the peer's
  copies complete on the leader's `full[s]`, which only the leader's producer arms, so a peer's complete-tx may come
  first (A47). The phase still completes only once the leader's arrival and both halves' bytes are in, since the
  expectation is both halves' sum. The range is the ISA's. A stage is at most 2 × 64 × 256 × 2 = 65,536
  bytes (`boxOk`), within 2^20 − 1.
- **Inval.** The model requires, at `Inval(b)`: no thread waiting on `b`, no operation in flight that will arrive on
  or complete-tx on `b`, `pend = count`, and `tx = 0`. PTX is silent on arrivals or transactions pending at `inval`,
  but any `mbarrier` operation other than `init` on a location that holds no valid barrier is undefined
  (§9.7.15.16.13), so a complete-tx or a commit's arrival that lands after `inval` is undefined. The model stays
  conservative. `init` of a location holding a live barrier is undefined (§9.7.15.16.12); `init` again after `inval`
  and a `bar.cta.sync` is the ISA's own example (§9.7.15.16.13, Example 2), which confirms A8. That is outside one
  model instance: a new `withRing` is a new instance.
- **Memory order.** `arrive` has release semantics and `try_wait` acquire semantics, at CTA scope, by default
  (§9.7.15.16.16, §9.7.15.16.19: the `.sem` defaults). The protocols use them only for the generic-proxy side of the
  handoffs (§1.6).
- **Init visibility (A7).** `fence.mbarrier_init.release.cluster` then `__syncthreads` makes initialized barriers
  visible to every thread and to the asynchronous units. TMA and `tcgen05.commit` access their barrier through the
  generic proxy (§9.7.10.28.5.3, §9.7.18.12.1), so no proxy fence is needed for them. The model starts each protocol
  after that point: the setup is not interleaved with any other step. `withRing`, `withAccHandoff` and `withAccRing`
  emit exactly this prefix, the setup's arrives before the fence. `fence.mbarrier_init` covers only the prior
  `init`s, and the setup's arrive has the default `.release.cta`; within one CTA the `__syncthreads` orders it. A pair
  protocol's prefix (`encoding/TWO_CTA.md`) replaces the CTA barrier with a cluster barrier,
  `barrier.cluster.arrive.release` then `barrier.cluster.wait.acquire` by every thread of both CTAs (A44, A45): its
  release, not relaxed, also orders the setup's arrives before the peer's first remote arrival.

### 1.3 TMA bulk tensor copy

`cp.async.bulk.tensor.2d.shared::cluster.global.mbarrier::complete_tx::bytes [dst], [map, {c0, c1}], [b]`, issued by
one thread (`tmaLoad2d`):

| Rule | Effect | Source |
|---|---|---|
| Issue | adds a copy `(dst, bytes, b)` to the TMA unit's set; from now on `dst` is being written (any part, at any time) | PTX §9.7.10.28.5.3 (`cp.async.bulk.tensor`): asynchronous, completion mechanism `.mbarrier::complete_tx::bytes` |
| Land | removes the copy; its writes are done; CompleteTx(`b`, `bytes`) | ibid.: upon the copy's completion, one complete-tx whose count is the bytes copied is performed on the barrier; §9.7.15.16.6 |

`bytes` is the whole box: elements outside the tensor are zero-filled and counted (A9, `cuTensorMapEncodeTiled`). The
model does not look at the global source, which the copies only read, or at the tensor map. A shared::cta address is a
valid shared::cluster address of the executing CTA, which is what `tmaLoad2d` passes. Both copies of a fill complete
on the stage's full barrier, and the fill's `ArriveTx` expects `stageBytes(cfg) = boxBytes(a) + boxBytes(b)`. **The
model assumes that equality**: with an expectation a proper sub-sum of the copies' bytes could reach, a phase would
complete with a copy still writing (§3.2). A copy performs its complete-tx once, at its completion, with its whole
byte count (§9.7.10.28.5.3; §9.7.15.16.6: "upon completion of each of the asynchronous operations"), and that
complete-tx has release semantics at cluster scope. So a phase completes only when every copy it expects has completed,
given the equality.

### 1.4 Tensor-core operations and `tcgen05.commit`

Each thread `T` that issues tensor-core work has a queue `Q(T)` in issue order:

| Rule | Instruction | Effect | Source |
|---|---|---|---|
| MmaIssue | `tcgen05.mma.cta_group::1.kind::f16 [d], descA, descB, idesc, p` | appends `Mma(reads, writes)`: the shared-memory stage behind the descriptors, the tensor-memory columns at `d` | PTX §9.7.18.10.10.1; §9.7.18.6.1: asynchronous |
| MmaDone | (asynchronous) | removes any `Mma` of `Q(T)`: its reads and writes are done | ibid. |
| CommitIssue | `tcgen05.commit.cta_group::1.mbarrier::arrive::one.shared::cluster.b64 [b]` | appends `Commit(b)` | §9.7.18.12.1: the barrier tracks the completion of all prior asynchronous `tcgen05` operations of the executing thread whose completion is observed through an mbarrier, `tcgen05.mma`, `.cp` and `.shift` (§9.7.18.6.2.1.1), not `tcgen05.ld`/`.st` |
| CommitFire | (asynchronous) | enabled for a `Commit(b)` with no `Mma` before it in `Q(T)`; removes it; Arrive(`b`) | ibid., `.mbarrier::arrive::one`: one arrive-on, of count 1, at cluster scope, upon the completion of the tracked operations |

- **Grouping.** An MMA step issues K/16 = 4 `tcgen05.mma` with no barrier operation between them, and its commit
  covers all of them. The model folds them into one `Mma` whose interval is the union of theirs. That only widens
  intervals, so it is sound for race detection.
- **Completion order.** The model lets MMAs complete in any order, and commits fire in any order their guards allow.
  That is required, not a simplification: asynchronous `tcgen05` operations may execute and complete in an order other
  than their issue order (§9.7.18.6.2). The pipelined pairs of §9.7.18.6.2 order only accesses to operands in tensor
  memory, and §9.7.18.6.5 excludes the MMAs' shared-memory accesses from the pipelining rules. The implicitly
  pipelined pair `mma → commit` (§9.7.18.6.2.1.1) is exactly CommitFire's guard, and no pair orders two commits. So
  neither completions nor commits' arrivals are observable in issue order, and the model may not assume they are
  (§4.1 measured what that would have saved).
- **The implicit fence.** `tcgen05.commit` implicitly performs `tcgen05.fence::before_thread_sync` (§9.7.18.6.4.2,
  Example 2), which is what makes its arrival order the MMAs' accesses before the waiting thread's later operations
  (A12, A13).

### 1.5 Tensor-memory loads

`tcgen05.ld.sync.aligned.32x32b.x8` issued by a warp starts a read of its lane quadrant's columns, and the thread's
`tcgen05.wait::ld` ends every read it started (A14; PTX §9.7.18.8.3, §9.7.18.8.5). `storeRows` pairs each load with
its wait, so a thread's reads of a buffer form one interval, from the first `ld` of the tile to the last `wait::ld`.
The model's epilogue thread is `await → read → release`, with `read` that interval.

### 1.6 What "a read sees the writes" means here

The protocols rely on six ordering facts. Each turns an interval's end into something a later step in another role
can depend on:

| # | Fact | From | Used by |
|---|---|---|---|
| O1 | A TMA copy's writes are done before its complete-tx, which has release semantics at cluster scope (PTX §9.7.10.28.5.3). A thread whose wait (acquire by default) observes the phase that complete-tx helped complete sees the writes (§9.7.10.28.1.2). The tensor-core operations it issues afterwards are ordered after the wait by a `tcgen05.fence::after_thread_sync` between them (§9.7.18.6.3), which the ISA states is needed before an asynchronous `tcgen05` operation after such a wait (§9.7.18.6.4.2), and which `await` emits. In a pair ring the copy may be the peer's, writing the peer's shared memory, and the waiter the leader's thread, at cluster scope (`awaitPair`): the chain is the same, and that the leader's MMA's async-proxy read of the peer's shared memory is ordered after the peer's async-proxy write by it alone is A53. | A6, A9, A13, A47, A53 | ring: `await` → MMA; pair ring: `awaitPair` → MMA |
| O2 | An MMA's reads and writes are done before the arrival of a later commit of its thread. After a wait observing that phase, later TMA writes to its sources are ordered after its reads, with no fence (derived below). In a pair ring the commit is the leader's, multicast, and the waiter and the TMA the peer's (`releasePair` → `acquirePair` → `fillPair`): the chain is the same, across the pair at cluster scope, and its last link, the same-thread-block clause of §8.9.5, is A53. | A12, A49, A53 | ring: `releaseByMma` → `acquire` → `fill`; the drains; the pair ring's |
| O3 | After O2's wait, `tcgen05.fence::after_thread_sync` orders the waiter's later tensor-core operations and loads after the MMAs' writes (§9.7.18.6.3; §9.7.18.6.4.4, Example 2). | A12, A13 | `recvAcc`, `awaitAcc` → `tcgen05.ld` |
| O4 | A thread's `wait::ld` ends its loads. `tcgen05.fence::before_thread_sync` then `mbarrier.arrive`, observed by a wait followed by `tcgen05.fence::after_thread_sync`, orders the loads before the waiter's later MMAs (§9.7.18.6.4.4, Example 1). | A13, A14 | `releaseAcc` → `acquireAcc` → MMA |
| O5 | A thread barrier (`__syncthreads`, `bar.sync`) orders the memory accesses of the threads before it before those after it. | A2, A3 | tile typestate; init and inval; the roles' join |
| O6 | Initialized barriers are visible to every thread and unit after `fence.mbarrier_init` and a CTA barrier (§9.7.15.4: the fence applies to the thread's prior `mbarrier.init`s); a pair protocol's, to the peer's threads and units too, after a cluster barrier instead (A45). | A7, A45 | every protocol's start |
| O7 | A generic-proxy write to shared memory that an async-proxy access (a TMA store, an MMA) will read must be followed, in each writing thread, by `fence.proxy.async.shared::cta`, before the synchronization that orders it before the async operation's issue (§9.7.10.28.2; §9.7.18.6.5; CUDA Programming Guide §4.12.2.1). A generic read of what a TMA load wrote needs no fence once the load's completion is observed: the completion of a `cp.async.bulk` operation carries an implicit generic-async proxy fence (§9.7.10.28.2). A generic write after an async-proxy read, as when a staging buffer is written again after a TMA store read it, is ordered by the issuing thread's `cp.async.bulk.wait_group.read`, which waits until the group's operations have finished reading their sources (§9.7.10.28.6.2), then a warp barrier; that rests on A35. | A35, A36, A37 | none in the protocols of §2; the TMA-store epilogue (`fenceStage`, §6) |

With these, a race in the memory model's sense needs two conflicting accesses that no chain of O1–O6 orders. In the
model every such chain is realised the same way: the first access's interval ends, an arrival or complete-tx follows,
a phase completes, a wait observes it, and then the second access begins. So "conflicting intervals never overlap in
any interleaving" (the model's P1, P2, P6) implies "every conflicting pair is ordered", **provided each chain is
fenced as the table says**. That proviso is a per-role syntactic fact, not a fact about interleavings. The model takes
it as part of each role's program (§2.6), and the link checker of §5.3 can confirm it on the emitted code.

O7 is why interval disjointness is not enough by itself. A role that wrote a stage with `st.shared` and handed it to
the tensor cores through the barrier chain would satisfy P1–P5 and still race. The model therefore tags accesses with
their proxy (§1.1), and a hand-off from one proxy to the other without O7's fence is a violation. Every access to a
stage or to tensor memory in §2's protocols is async-proxy or `tcgen05.ld`, and their handoffs are async to async, so
O7 is vacuous there. It is not vacuous for the TMA-store epilogue (§6), whose generic writes of a staging buffer
`fenceStage` fences, and nothing writes with generic stores what an MMA read: the stages are written only by TMA
loads, and dynamic shared memory is never reused for another purpose within a kernel (bump allocation).

**O1 needs the fence.** `tcgen05.fence::after_thread_sync` is what orders an asynchronous `tcgen05` operation after
a prior mbarrier wait (§9.7.18.6.3). The standard memory-model mechanisms also apply to `tcgen05` instructions
(ibid.), but they say nothing of an asynchronous operation issued after a wait, and the ISA states that after such a
wait "`tcgen05.fence::after_thread_sync` is needed" (§9.7.18.6.4.2, Example 2). Every pattern of the ISA that goes
from a wait to a
`tcgen05.mma` has it (§9.7.18.6.4.3; §9.7.18.6.4.4, Example 1). So `await` emits `wait; tcgen05.fence::after_thread_sync`,
as DeepGEMM does. CUTLASS's TMA-to-UMMA pipeline omits it, and also the fences the ISA requires for O3 and O4. The
visibility half of O1 does not come from `try_wait`'s own rule for `cp.async.bulk` (§9.7.15.16.19), which covers the
copies a thread requested before a release arrive: the ring issues its copies after `arrive.expect_tx`. It comes from
the copy's complete-tx, which has release semantics at cluster scope (§9.7.10.28.5.3), and from the mbarrier-based
completion mechanism, under which the threads participating in the barrier may access the results once the phase is
complete (§9.7.10.28.1.2).

**O2 needs no fence**, by a chain the ISA states link by link:
- the plain commit arrives upon the overall completion of the MMAs it tracks, reads included (§9.7.18.12.1; contrast
  `.sync_restrict::shared::read::mma::a`, which arrives once the A operands are read and "does not signal the overall
  completion");
- the commit implicitly performs `tcgen05.fence::before_thread_sync` (§9.7.18.6.4.2, Example 2), and the producer's
  acquiring wait observes its arrival;
- a `cp.async.bulk` operation is ordered after the issuing thread's prior instructions (§8.9.1.1), here the wait;
- the MMA's read and the copy's write are both async-proxy accesses by one CTA, so base causality order between them is
  proxy-preserved without an alias fence (§8.9.5).

A generic-proxy writer in the producer's place would need `fence.proxy.async.shared::cta` after the wait (O7).

### 1.7 Left out of the models

- **Data.** Values are never modelled. A buffer's content is its ghost generation (§3), which is all the properties
  need. Functional correctness stays with the harness.
- **Addresses.** Buffers are named by stage or buffer index. That the stages are disjoint and aligned (I2, bump
  allocation) and that an address expression names the register's stage is the link of §5, not the model.
- **The global memory** the copies read and the epilogue writes (S5 is layer 1 and the typing), the tensor maps, and
  the descriptors' bits (A11).
- **Thread scheduling within a warp**, `elect.sync` and `__syncwarp` (A4, A5): a role is modelled as the one thread
  that runs it, or as the 128 epilogue threads (§2.4).
- **`try_wait`'s time limit and suspend hint**, the `.acquire`/`.release` qualifiers beyond O1–O6, `mbarrier.
  pending_count`, `arrive_drop`, `test_wait`: unused today. Remote (cluster) barriers: used by the CTA pair, not
  modelled (§6).
- **Tensor-memory allocation** (A10): `withTmem` is straight-line CTA code around the protocols. Its obligation that
  no tensor-core operation is pending at `dealloc` needs P4 of the combined system of every protocol inside it, since
  one thread's `Q(C)` holds the commits of several protocols (§3.1).

## 2. The protocols as transition systems

### 2.1 Common structure

- **Roles.** A role is a small program over the rules of §1, run by one thread (an elected lane) or, for the
  epilogue, by each of the 128 threads of an aligned warpgroup. Its registers are the ones `Gpu.rac` declares, a
  stage index and a phase bit per side, plus a program counter.
- **Advance.** `advance(st, ph, n)`: `st += 1`; if `st = n` then `st = 0`, `ph = 1 − ph` (`Gpu.advance`). It is
  local and unobservable, so it is folded into the step before it.
- **Loops.** No type mentions an iteration count, and the models do not either. Where a role's loop continues or ends
  is a nondeterministic choice. For safety, choices are unconstrained, so every trip count and every mismatch is
  covered (M11: a mismatch deadlocks and cannot race). For the deadlock check (P7, not claimed), the roles must agree:
  the leading role chooses, and the choice travels as a ghost tag with the data (on the fill of a stage, on the commit
  of a buffer). The lagging role reads the tag when its wait succeeds, so the trip counts agree by construction.
  `loopPeeled` runs at least one iteration and `forTiles` any number. The tagged models (§4.1) cover at least one fill
  and at least one tile; zero tiles, which `forTiles` allows, is covered only by the untagged models.
- **Two disciplines.** So there are two models of each protocol. The **untagged** one, where each side may end its
  loop at each of its waits, is the one safety is proved on. The **tagged** one adds P7. The explorers of §4.1 count
  both.
- **Join and teardown.** Each protocol's roles are joined by the CTA barrier of the enclosing `split` (O5). Then
  thread 0 invalidates the protocol's barriers (`invalBarriers`). The model's terminal step Join is enabled when every
  role is done. It checks quiescence (P4), then Inval of each barrier.

### 2.2 The stage ring

For `S` stages (`RingCfg.stages`), with barriers `full[s]` and `empty[s]` (count 1 each), stage buffers `stage[s]`, a
producer `P` (an elected lane of the load warp) and a consumer `C` (the elected lane of the MMA warp, the issuer).

State:
- `P`: `pc ∈ {acquire, fill, drain(i) (0 ≤ i < S), done}`, `ps < S`, `pp ∈ {0, 1}`, initially `(acquire, 0, 0)`
  (`takeProducer`);
- `C`: `pc ∈ {await, mma, commit, done}`, `cs < S`, `cp`, initially `(await, 0, 0)` (`takeConsumer`);
- the `2S` barriers (§1.2), initially as the setup leaves them: each `full[s]` in phase 0, each `empty[s]` with
  phase 0 completed (`n = 1`); the TMA set (§1.3), `Q(C)` (§1.4);
- ghosts (§3).

Steps (each one rule of §1, or an atomic group that `Gpu.rac` emits as consecutive instructions of one thread):

| Role | From | Step | To | Emitted by |
|---|---|---|---|---|
| P | acquire | Wait(`empty[ps]`, `pp`) | fill | `acquire` |
| P | fill | ArriveTx(`full[ps]`, `stageBytes`); Issue copy A into `stage[ps]`; Issue copy B; advance; choose continue or end | acquire, or drain(0) | `fill` |
| P | drain(i) | Wait(`empty[ps]`, `pp`); advance | drain(i + 1), or done after S | `finishProducer` (`drain`) |
| TMA | | Land a copy: CompleteTx(`full[s]`, its bytes) | | A9 |
| C | await | Wait(`full[cs]`, `cp`) | mma | `await` |
| C | mma | MmaIssue(reads `stage[cs]`, writes the accumulator) | commit | `mmaFirst`/`mmaNext`, `mmaFirstInto`/`mmaNextInto` |
| C | commit | CommitIssue(`empty[cs]`); advance; continue or end | await, or done | `releaseByMma`; `finishConsumer` emits nothing |
| tensor cores | | MmaDone; CommitFire | | A11, A12 |

The fill is shown as one step. In the emitted code it is three instructions: the arrive, then the two copies. The
exhaustive model keeps them separate (§4.1 counts both). Folding them is sound, because the intermediate states enable
nothing another role can observe: the arrive leaves `tx > 0`, so `full[ps]` cannot complete before the copies land.
But the folding is a reduction whose soundness needs its own argument (§4.1).

In the persistent GEMM, the issuer also runs the accumulator ring's steps between the stage ring's. For the stage
ring's properties those steps are stutters: they touch no stage-ring object, and the MMAs they emit are the ones
above. The stage ring model therefore covers both examples.

### 2.3 The accumulator handoff (TinyGEMM)

One barrier `h` (count 1), one sender, the issuer, and 128 receivers:
- the sender's last CommitIssue(`h`) (`sendAcc`) follows every MMA of the tile in `Q(C)`;
- each receiver runs Wait(`h`, 0), then `tcgen05.fence::after_thread_sync` (`recvAcc`), then its read interval
  (`storeAcc`), then done;
- the join, then Inval(`h`).

The handoff is used once per instance, so `n(h) ≤ 1` and there is no ABA. Waits change nothing, so 128 receivers
behave as one for every property. The model has one representative receiver.

### 2.4 The accumulator ring (persistent GEMM)

`bufs` buffers of `n` columns, barriers `accFull[b]` (count 1) and `accEmpty[b]` (count 128):
- the issuer as producer: `aps`, `app`, initially 0 and 0 (`takeAccProducer`), each `accEmpty[b]` with phase 0
  completed by the setup's 128 arrivals (§1.2), each `accFull[b]` in phase 0;
- the 128 epilogue threads as consumers, each with its own `acs`, `acp`, initially 0 and 0 (`takeAccConsumer`
  declares them in each thread; they stay equal only if every thread runs the same steps).

| Role | From | Step | To | Emitted by |
|---|---|---|---|---|
| issuer | tile start | Wait(`accEmpty[aps]`, `app`); fence after | K steps | `acquireAcc` |
| issuer | K steps | the stage ring's `await`/`mma`/`commit`, each MMA also writing `buffer[aps]` | commit | `mmaFirstInto`, `mmaNextInto` |
| issuer | commit | CommitIssue(`accFull[aps]`); advance; continue or end | tile start, or adrain(0) | `commitAcc` |
| issuer | adrain(i) | Wait(`accEmpty[aps]`, `app`); advance | adrain(i + 1), or done after `bufs` | `finishAccProducer` |
| thread t | await | Wait(`accFull[acs]`, `acp`); fence after | read | `awaitAcc` |
| thread t | read | start of the read interval of `buffer[acs]` … its end (last `wait::ld`) | release | `storeTile` |
| thread t | release | fence before; Arrive(`accEmpty[acs]`); advance; continue or end | await, or done | `releaseAcc`; `finishAccConsumer` emits nothing |

The 128 arrivals per phase are what is new. A fast thread may reach the next buffer, or the next round of this one,
while a slow thread is still reading. The model has `N` consumer threads with count `N`. Explicitly it is feasible
only for small `N` (§4.1), so the design reduces `N` to one representative thread (§4.2.3).

### 2.5 The shared-tile typestate (SIMT kernels)

A CTA-convergent program over one shared array per `shared` (A16: one allocation for the kernel, reused by every
iteration of an enclosing loop). The typestate `TileState` is its own transition system:

| From | Step | To | Emitted by |
|---|---|---|---|
| empty | every thread stores its own element (`v[threadIdx.x] = x`) | written | `storeMine` |
| written | `__syncthreads` | ready | `sync1`/`sync2` (`afterSync`) |
| ready | reads, any thread, any element (inside a read loan) | reading | `reads`, `sread` |
| reading | `__syncthreads` | empty | `afterSync` |
| empty, ready | `__syncthreads` | unchanged | `afterSync` |
| empty | end of the tile's authority | (released) | `release` |

Loops carry `Fixed` state (M5): the body maps one typestate to itself. So a loop is the body's word repeated any number
of times, and the program is a regular word over {store, sync, read, release}. Model: an interval is the code between
two consecutive CTA barriers. Property T (§3.4) is a regular property of that word. A2 (O5) is the only hardware fact
used.

### 2.6 The model against the emitted code

What a reviewer compares at layer 2, each row one sealed operation of `Gpu.rac` and the model steps it must emit:

| Operation | Emits | Model |
|---|---|---|
| `withRing` | thread 0: `mbarrier.init` ×2S (count 1), `mbarrier.arrive` (count 1) on each `empty + 8·s`, `fence.mbarrier_init`; `__syncthreads`; after the body, thread 0: `mbarrier.inval` ×2S. `withRing` emits no barrier before the invals: the join is the `__syncthreads` of the CTA-level `split` inside the body, which the typing forces (`ProducerDone` and `ConsumerDone` exist only inside elected lanes, which the body reaches only through splits) | Init and the setup (outside the interleaving), Join, Inval |
| `takeProducer` / `takeConsumer` | registers 0/0 and 0/0 in the elected block | initial `(0, 0)` / `(0, 0)` |
| `acquire` | wait `empty + 8·ps`, parity `pp` | P: acquire |
| `fill` | `arrive.expect_tx(full + 8·ps, stageBytes)`, TMA A to `stage(ps)`, TMA B to `stage(ps) + boxBytes(a)`, both on `full + 8·ps`; advance(ps, pp, S) | P: fill |
| `finishProducer` | S × (wait `empty + 8·ps` at `pp`; advance) | P: drain |
| `await` | wait `full + 8·cs`, parity `cp`; `tcgen05.fence::after_thread_sync` | C: await |
| `mmaFirst…`, `mmaNext…` | K/16 × `tcgen05.mma` reading `stage(cs)` | C: mma |
| `releaseByMma` | `tcgen05.commit(empty + 8·cs)`; advance(cs, cp, S) | C: commit |
| `withAccHandoff`, `sendAcc`, `recvAcc` | init count 1; commit; wait parity 0 + fence after; inval | §2.3 |
| `withAccRing` | init `accFull` count 1, `accEmpty` count 128, then one `mbarrier.arrive` of count 128 on each `accEmpty`; inval | §2.4 |
| `acquireAcc`, `commitAcc`, `finishAccProducer` | wait + fence after; commit + advance; `bufs` × (wait; advance) | §2.4 issuer |
| `awaitAcc`, `storeTile`, `releaseAcc` | wait + fence after; fence after, (`__syncwarp`, `ld`, `wait::ld`, stores) per 8 columns; fence before, arrive, advance | §2.4 thread |
| `storeMine`, `sync1`/`sync2`, `reads`/`sread`, `release` | store; `__syncthreads`; loads; nothing | §2.5 |

## 3. Properties

Stated on the states and steps of §2. They use ghost counters, which are part of the model's specification and have
no hardware counterpart:
- per stage `s`: `fills(s)`, fills started (ArriveTx); `landed(s)`, fills whose copies all landed; `reads(s)`, MMAs
  issued on `s`; `released(s)`, commits to `empty[s]` fired;
- per wait: the completion it **means**, counting waits and fills from 0. The consumer's j-th wait on `full[s]`
  means completion j + 1 (the j-th fill). The producer's j-th wait on `empty[s]` (acquire or drain) also means
  completion j + 1: completion 1 is the setup's arrive (§1.2), and completion j + 1, for j ≥ 1, the release of the
  (j − 1)-th fill. So both sides start at phase 0, and `n(empty[s]) = 1 + released(s)`.

In the finite models these counters appear only as bounded differences (`fills(s) − reads(s) ∈ {0, 1}`,
`meant − n(b) ∈ {0, 1}`). A step that would leave the bound is a violation, so the finite model is exact for them.

### 3.1 The stage ring

- **P1, no fill of a stage whose reader has not released it.** A fill of `s` (its ArriveTx) happens only when
  `fills(s) = reads(s)` and no MMA reading `s` is in `Q(C)`. At all times, no copy into `s` is in flight while an MMA
  reading `s` is.
- **P2, no read of a stage whose fill has not completed.** An MmaIssue on `s` happens only when `fills(s) = reads(s)
  + 1`, `landed(s) = fills(s)` and no copy into `s` is in flight. So the j-th read of `s` reads exactly the j-th fill,
  completely written.
- **P3, the parity each side waits on is the phase it means.** At every state and for every side at a wait on `b`
  meaning completion `k`: `n(b) ∈ {k − 1, k}`. Then the hardware test `ph(b) ≠ p` succeeds exactly when `n(b) ≥ k`,
  given the side's register `p = (k − 1) mod 2`, which P3 also requires. In particular no barrier is ever two phases
  ahead of a side that still means an earlier one (no ABA across a wrap), and no side waits on a phase that was
  skipped. Also, every copy in flight to `full[s]` belongs to the phase that expects it (P3b): a complete-tx never
  lands in a later fill's phase.
- **P4, the tail drains before invalidation.** At Join: the TMA set is empty, `Q(C)` is empty (no MMA, no commit),
  every barrier has `pend = count` and `tx = 0`, and no role is at a wait. So Inval is allowed (§1.2), and the stages
  may be reused by what follows `withRing`. That no tensor-core operation is pending at `withTmem`'s `dealloc` (A10)
  is P4 of the combined system: the issuer's `Q(C)` also holds the handoff's commit (TinyGEMM) or the accumulator
  ring's (persistent), and a protocol's own P4 speaks only of its own entries.
- **P5, no over-arrival.** No Arrive of `c` on a barrier with `pend < c`, and no CommitFire on one with `pend = 0`.
- **P8, every phase observed before the next is arrived on.** No arrive-on (Arrive, ArriveTx, CommitFire) on a
  barrier `b` with `n(b) ≥ 1`, unless some Wait on `b` has succeeded since its phase `n(b) − 1` completed (PTX
  §9.7.15.16.5.1). The protocols meet it because every arrival of a barrier's next phase is causally after a successful
  wait on its last one: the producer's ArriveTx on `full[s]` follows its wait on `empty[s]`, which observed the
  consumer's commit, issued after the consumer's wait on `full[s]` succeeded; the commit to `empty[s]` follows the
  consumer's wait on `full[s]`, which observed a fill issued after the producer's wait on `empty[s]` succeeded; and
  the first arrival after the setup's, a commit to `empty[s]`, follows the producer's first wait on `empty[s]`. The
  accumulator ring is the same with the issuer and the 128 threads for the two sides; the handoff completes one
  phase.

### 3.2 Why these, and not less

Race freedom alone (never a copy and an MMA on one stage in flight at once) would accept a ring whose consumer, after
an ABA wait, reads a stage twice without a race: it would read the old data again. P2's generation equation rejects
that, and P3 names its cause. P3 alone would accept a ring whose copies complete a phase early, for instance a wrong
expected byte count equal to one of the two boxes. P2's "no copy in flight" rejects that. That case is a failure of
the §1.3 assumption `stageBytes = boxBytes(a) + boxBytes(b)`, which the model states as an assumption and §5 links to
`Gpu.stageBytes`. P4 is the only property that sees the tail. The explorer's mutants (§4.1) are each caught by at
least one of these; the table names the first violation the explorer reports:

| Mutant (one change to the model) | Caught by |
|---|---|
| the commit may fire before the MMA it covers completes | P1 (a fill starts while the read is in flight) at S = 1 and 3; P4 first at S = 2 and 4 |
| producer starts at phase 1 | P3 at the first acquire (and it would deadlock) |
| consumer starts at phase 1 | P3 at the first await |
| the drain waits S − 1 stages | P4 |
| no drain | P4 |
| `acquireAcc` does not wait | P6 (an MMA into a buffer not yet read) |

The explorers (§4.1) predate the setup of §1.2 and did not check P8. They ran the model in which every barrier starts
fresh and each producer at phase 1, relying on the fresh barrier's parity-1 wait. That model differs from this one
only by flipping `ph` of the barriers the setup completes and the producers' phase registers, and by shifting both
the ghost `n(b)` of those barriers and the completion each producer wait means by one. That is a relabelling under
which every Wait's outcome, and so every behaviour, is the same, and P3 survives it because its two sides shift
together. So the counts of §4.1 carry over to this model without P8's ghost bit (§4.1), which adds states, and the
results above carry over with "phase 1" for the producer's mutant here standing for that model's "phase 0", provided
the explorer checked P3's bound in the form §3 now states (`meant − n(b) ∈ {0, 1}`; earlier versions of this
document had the sign reversed). V1 must run the setup and P8 as stated.

What the properties do not see:
- a ring whose registers name one stage and whose address expressions another, or whose stages overlap (§5);
- a fence missing from a chain (§1.6);
- more than one producer or consumer thread per side (M6 excludes it; the model has one of each).

### 3.3 The accumulator protocols

- **P6, the accumulator ring.** The ring's P1–P5 with buffers for stages, MMAs for fills and tensor-memory loads for
  reads:
  - no MMA writing `buffer[b]` is in flight while any thread's read of `b` is;
  - the j-th read of `b` by every thread reads the j-th tile's MMAs, all completed;
  - no MMA into `b` is issued before every one of the 128 threads released round j − 1 of `b`;
  - each wait means its phase: for the threads, per thread;
  - P4 at Join, which is also `withTmem`'s condition for `dealloc`.
- **The handoff.** Every receiver's read starts after every MMA completed; P4 and P5.

### 3.4 The shared-tile typestate

- **T.** In every interval (§2.5), a tile is either only stored, each thread its own element, or only read. A read
  happens only in an interval after one whose stores wrote every element. The authority ends (`release`) only at the
  start of an interval with no reads since the last barrier.

With M5, T is the statement that the reachable typestate words avoid store-and-read and read-before-full-store.

### 3.5 Deadlock

- **P7, no deadlock under equal trip counts.** Every reachable state in which some role is not done has an enabled
  step.

Not claimed (`OBLIGATIONS.md` §1, M11). It is checked where cheap, since a protocol that deadlocks under its own launch
contract is a bug worth finding. It needs the combined system of every protocol a role takes part in: the persistent
issuer's waits on both rings can form a cycle that neither ring alone shows. That system is large (§4.1), so P7 is
checked per configuration only, and not proved.

## 4. Proof strategy

### 4.1 Route (a): per configuration, by exhaustive exploration

**The checker.** The recommended design separates search from checking:
- the search, an ordinary depth-first exploration with a visited set, is untrusted, and returns the list `V` of
  reachable states it found;
- the checker `certify(model, V)` builds a set `T` of `V`'s states and returns true iff the initial state is in `T`,
  no `v ∈ V` is the error state, and every successor of every `v` is in `T`;
- its soundness is proved once: if `certify(model, V) = true`, then the error state is not reachable by the model's
  `Step`. The proof is induction on reachability, with the invariant "member of `T`". It needs set membership in one
  direction only (a member was inserted: `NatSets.fromInsert`'s shape), and an induction over the fold that builds `T`
  (so F11 is met once, in a small form), but no reasoning about the search, its fuel or its worklist.
- **Membership must compare states, not lossy keys.** A key collision would let `certify` accept a successor it never
  expanded. The trie's leaves must compare the states themselves by an equality proved sound, or `certify` must check
  each successor's fields against the encoding's ranges before keying it (the experiment's base-16 key is injective
  only for S ≤ 8 and arrival counts below 16, so it would collide on `accEmpty`'s count of 128);
- `[ok: Eq(Bool, certify(ring(6), search(ring(6))), Bool.true)]` then discharges by evaluation
  (`docs/PROOF_BY_EVALUATION.md` §1).

Each state is expanded twice, once by the search and once by the checker, so this doubles the work. That buys a proof
with no fuel argument and no worklist invariant, where F11 says walks with state are the expensive proofs.

**Violations are an error state.** A property violated by a step (P1, P2, P3, P5, an over-arrival, an Inval without
quiescence, P8, for which each barrier carries a ghost bit set by a successful Wait and cleared by Complete) must not
merely disable the step: in a safety check a disabled step is a deadlock, and the property would
hold vacuously. So every such rule has a second constructor, taken when its requirement fails, that leads to a
distinguished error state; the properties of §3 are then the one statement "the error state is unreachable", which is
what `certify` checks. §1.2's "requires" means this. The Python and Raccoon explorers already work this way.

**The model as a relation.** For review, each model is stated as an inductive `Step(s, t)`, one constructor per row
of §2 (and one per violation), each citing its rule. The checker runs an executable `succ(s): List(State)`, proved
complete per model: `Step(s, t) → Mem(t, succ(s))`. To keep that proof out of F2's reach (no `inspect`), each
constructor takes its guard as a Bool evidence argument, `[g: Eq(Bool, guard(s), Bool.true)]`, and `succ`
concatenates one generator per rule, each a match on that same guard. So each completeness case is an
`unlessOk`-style lemma over a variable (`proofs/NOTES.md` F2, P1). Expect about 20 rules per ring, each 10 to 30 lines of proof. F5 (no catch-all)
applies to every case split on a program counter.

**Encoding and the visited set.** A state is a struct of small naturals and lists of small naturals. Its key is the
mixed-radix number of its fields (base 16, the queue with a length prefix, so the key is injective). The set is
`Check.NatSet`'s design with a different path: the path is 20 bits of the key's residue modulo a prime, and a node
lists the keys that reach it, compared with `Nat.beq`. Membership is then correct whatever the path function, which
is the property `NatSet.rac` already exploits: no fact about paths is needed. The native `Nat.mod` and `Nat.div` keep
the path cheap, and keys of about 250 bits compare natively.

**Sizes.** Counted by a throwaway explorer (Python) of exactly the §2 models. For S = 2 to 4 the Raccoon explorer
below reproduces the counts exactly. Two loop disciplines are counted (§2.1):
- **tagged**: equal trip counts, the end chosen at a fill and carried by a ghost tag, deadlock reported. This checks
  safety and P7 together, and it is what the Raccoon experiment ran;
- **untagged**: each side may end its loop at each of its waits. This checks safety for every trip count, and it is
  the model safety is proved on (and the target of the projection of §4.2.2).

| Model | S = 1 | 2 | 3 | 4 | 5 | 6 | 8 |
|---|---|---|---|---|---|---|---|
| stage ring, faithful (§2.2, three-instruction fill, two copies, MMAs completing in any order), tagged | 56 | 780 | 6,066 | 37,088 | 199,880 | 1,000,320 | |
| edges | 68 | 1,756 | 19,284 | 151,824 | 1,003,160 | 5,962,368 | |
| the same, untagged | 88 | 1,092 | 8,136 | 48,736 | 259,840 | 1,292,736 | |
| edges | 168 | 3,044 | 29,808 | 222,144 | 1,422,800 | 8,293,056 | |
| reduced (tagged): fill and MMA-plus-commit atomic, the two copies one | | 236 | 1,206 | 4,880 | 17,200 | 55,296 | 476,672 |
| reduced, MMAs also completing in issue order (not assumed, §1.4) | | | 1,362 (a) | 5,192 (a) | 17,070 (a) | | |

(a) With the fill's arrive left a step of its own, so not comparable with the row above. The same model without
in-order completion has 1,482, 6,064 and 21,520 states, so in-order completion would save 8 to 20%.

Other reductions, each measured alone at S = 4, from 37,088: folding the two copies into one, 14,352; folding the two
copies' issue into one step and the MMA with its commit, 20,704. The one-copy reduction cannot express the wrong byte
count of §3.2, so a reduced run loses that check.

The accumulator ring alone (the stage ring abstracted to its effect, one MMA group per tile), `bufs` = 2, with `N`
epilogue threads and count `N`:

| N | 1 | 2 | 3 | 4 | 8 | 16 |
|---|---|---|---|---|---|---|
| states, threads distinct | 620 | 2,060 | 8,828 | 42,956 | | |
| states, threads symmetric (sorted) | 620 | 1,340 | | 5,096 | 39,400 | 686,248 |

Under symmetry the local growth exponent is itself rising (2.95 from N = 4 to 8, 4.12 from 8 to 16), so N = 128 would
be well over 10^9 states: out of reach. N is reduced to
one representative instead (§4.2.3).

The persistent kernel's combined system (producer, issuer, epilogue, both rings; reduced; N = 1, `bufs` = 2) has 40,878
states at S = 2, 363,760 at S = 3 and 2,617,482 at S = 4. It is needed only for P7.

**Why the space is finite.** Stage indices are below S and phases are bits. Every ghost is a bounded difference. The
queue `Q(C)` holds at most one MMA and one commit per stage, since a stage cannot be read again before its commit
fires. The TMA set holds at most two copies per stage. Loops appear only as the choice to continue.

**Measurements.** A Raccoon explorer of the tagged faithful stage ring (§2.2, 430 lines, in the style of `Check.rac`: a
struct state, lists, a hashed path trie, a depth-first search with fuel, tail-recursive) was run on the result
`Ring.explore(S)`, and on `Eq.refl(Bool.true) : Eq(Bool, isSafe(S), Bool.true)`. Machine: the Apple-silicon Mac of
the other layer-1 measurements, shared with other work at the time (CPU time is the steadier number).

| Binary | Model | S | States | Edges | Wall | CPU |
|---|---|---|---|---|---|---|
| native (GraalVM native image of 0767971) | faithful | 2 | 780 | 1,756 | 1.5 s | 1.4 s |
| native | faithful | 3 | 6,066 | 19,284 | 16.2 s | 15.8 s |
| native | faithful, as `Eq.refl` (conversion) | 3 | 6,066 | | 16.7 s | 15.8 s |
| JVM (GraalVM 21, `-Xss64m`) | faithful | 3 | 6,066 | | 12.3 s | 15.8 s |
| JVM | faithful, as `Eq.refl` | 3 | 6,066 | | 12.8 s | 16.0 s |
| JVM | faithful | 4 | 37,088 | 151,824 | 157.8 s | 107.0 s |
| native | faithful | 4 | 37,088 | 151,824 | 147.8 s | 137.2 s |
| native | reduced | 2 | 236 | 412 | 0.45 s | 0.42 s |
| native | reduced | 3 | 1,206 | 2,868 | 2.7 s | 2.7 s |
| native | reduced | 4 | 4,880 | 14,456 | 14.5 s | 14.2 s |
| native | reduced | 5 | 17,200 | 60,560 | 66.7 s | 64.6 s |
| native | reduced | 6 | 55,296 | 224,736 | 284.8 s | 262.5 s |

So the evaluator spends 2 to 5 ms per state, or 0.8 to 1.2 ms per edge, rising with S (longer lists, longer keys).
Discharge by conversion costs what evaluation costs. Extrapolating at the rising per-edge cost:
- the faithful tagged ring at S = 6 (5,962,368 edges): about 1.7 to 2 hours per run, 3.5 to 4 with the certificate
  check; the untagged one (8,293,056 edges) about 40% more;
- the reduced ring at S = 6: measured 4.4 minutes of CPU, about 9 with the certificate check;
- the combined persistent system at S = 4: about 3 hours.

A tighter encoding (the whole state in one packed Nat, fields read by native division) might gain a small factor. It
would not change the verdict.

**Verdict.** Route (a) works today for S ≤ 4 on the faithful model, and to S = 6 only on the reduced one. Each
reduction is a lemma to prove (a Lipton-style mover argument for the atomic groups, a simulation for the merged
copies). And every check of a module that states the certificate re-runs the evaluation: Raccoon keeps no proof cache
between runs. A certificate of minutes inside `Gpu`, which every client loads, is not acceptable. Stated per
configuration in a separate module that `check.sh` runs, it is. The deciding problem is that S is the client's choice
(`RingCfg`), so a per-configuration proof either fixes the S values the library accepts or runs at the client's
render.

### 4.2 Route (b): generic in S

#### 4.2.1 An invariant proved by induction

The direct route states an invariant over unbounded ghost counters and proves it preserved by every step, for every
S. The core of it:
- the producer's registers are `ps = F mod S` and `pp = ⌊F/S⌋ mod 2` after F fills, and the consumer's are the
  same in R reads;
- per stage, `released(s) ≤ reads(s) ≤ landed(s) ≤ fills(s) ≤ released(s) + 1`;
- `n(full[s]) = landed(s)` and `n(empty[s]) = 1 + released(s)` (the setup's completion);
- `Q(C)`'s entries are in stage order from the oldest unreleased stage;
- each in-flight copy belongs to the fill `fills(s)`.

Every step needs the arithmetic of `mod` and `div` across an advance. That is exactly the arithmetic `proofs/NOTES.md`
F1 and F9 found missing: native `Nat.mod`/`Nat.div` on variables do not unfold, and a struct field mentioning
`Nat.mod` of a variable is exponential to declare. It can be avoided by keeping `(round, stage)` pairs, updated by
`advance`, instead of `F mod S`. But the proof is still about 20 steps × 8 conjuncts, each a case split without
wildcards (F5), with explicit arguments throughout (F4). By the size of layer 1's proofs (2,442 lines for seven
checkers), expect 2,000 to 3,000 lines for the stage ring alone, and as much again for the accumulator ring.

#### 4.2.2 Projection onto one stage (recommended)

A better route: make the finite check generic by showing that one stage's view of an S-stage ring is a behaviour of
the one-stage ring.

**The target model.** The one-stage ring must be the **untagged** model, in which each side may end its loop at each
of its waits (the producer at an acquire, going to its drain; the consumer at an await, going to done). The tagged
model of §2.1, where the "last" choice travels with a fill, does not do: in an S-stage ring the producer's last fill
is usually of another stage, so the projection onto `s` goes from a fill tagged "continue" straight to the drain. The
review found this, with a script that projects every reachable state and edge of the S-stage ring onto each stage and
looks each up in the one-stage model. Onto the tagged one-stage model (56 states), 544 of the 780 projected states of
the tagged S = 2 ring are not reachable. Onto the untagged one (88 states), every projected state and edge of the
untagged ring is matched, at S = 2 (1,092 states, 3,044 edges) and S = 3 (8,136 states, 29,808 edges). That is
evidence, not proof, and the check is to be kept in V1 for every model that is projected.

For a stage `s`, the projection `π_s` of an S-stage state keeps:
- `full[s]`, `empty[s]`, `stage[s]`'s copies;
- the MMAs reading `s` and the commits to `empty[s]` in `Q(C)`;
- each side's program counter if its registers name `s`. Otherwise "elsewhere" is mapped to the one-stage program
  counter the side will next have at `s`: acquire (or await) if it will visit `s` again, drain if the producer is
  draining and has not yet waited on `s`, done if it has. That needs a per-stage ghost flag `drained(s)`, set by the
  drain's wait on `s`, since deciding it from the registers would need `(ps − i) mod S`;
- each side's phase register, as the parity of its next visit to `s` (R1).

The claim: **every behaviour of the untagged S-stage ring, projected by `π_s`, is a behaviour of the untagged
one-stage ring, up to stuttering.** Steps of other stages map to no step, and the rest to the one-stage ring's own
step. Safety properties are closed under stuttering, and they are per stage: P1, P2, P3 and P5 each mention one stage,
and P4 is a conjunction over stages. So they hold for every S if they hold for S = 1, and S = 1 is a finite check of
**88 states**. It also covers stages that are never filled (fewer fills than stages), since the untagged producer may
drain at its first acquire.

The claim rests on four lemmas, each generic in S and none about interleavings:
- **R1, round-robin phases.** A side's registers name `s` for the j-th time (from 0) with phase `j mod 2`. Proof: induction on the advances, with the ghost pair `(round, stage)`; `advance` either
  increments `stage` or wraps it to 0 and increments `round`, and the phase is `round`'s parity. No `div` or `mod`.
- **R2, non-interference.** A step whose side's registers name `s' ≠ s` touches no object of `s`. The one exception
  is a commit, which also waits for MMAs of other stages issued before it, and that only delays its CommitFire.
  Delay is stuttering, since S = 1 allows any delay (no fairness). Proof: by cases on the step. It needs the stages'
  barriers and buffers to be distinct (I2, §5).
- **R3, the drain covers each stage once.** The drain's S waits name each stage exactly once, each at the phase of
  that stage's next visit (R1). Proof: S consecutive advances from any stage visit every residue once, by induction
  on S with the `(round, stage)` pair, maintaining `drained`.
- **R3′, the end choice.** An S-stage side that ends its loop at a wait on `s'` projects, for every stage `s`, to the
  one-stage side ending at its next wait on `s`. This is where the untagged target is needed.

The simulation proof maps each step of §2.2 to zero or one step of the one-stage ring. The faithful ring has about 13
kinds of step, each at `s` or elsewhere, plus the end choices: about 30 cases, each an application of R1–R3′. Estimate
800 to 1,200 lines, dominated by R1, R3 and the case split. It is also the argument a reviewer would make on paper,
which is why this document recommends it.

P7 (deadlock) does not project: a stage's projection deadlocking says nothing about the whole ring, and the whole ring
being live needs all stages. It stays with per-configuration checks of the tagged models.

#### 4.2.3 The accumulator ring: one buffer, one representative thread

This is the weaker half of the route. The same projection onto one buffer reduces `bufs` to 1: R1–R3′ hold for
`aps`/`acs` as for `ps`/`cs`. Two further reductions are needed, and neither is established by this design.

**The stage ring folded away (R5).** The accumulator ring's models (the `acconly` rows of §4.1) replace the issuer's
stage-ring steps by one MMA group per tile. This is a projection too: the issuer's stage-ring waits become stutters,
and a tile's MMAs become one group whose interval covers theirs. It needs its own simulation lemma, of the size of R2.

**128 threads to one representative (R4).** Phase 0 of `accEmpty[b]` is completed by the setup's one arrive of
count 128 (§1.2), outside the interleaving; in the one-thread projection the setup arrives once, with `c = 1`. The
argument is about the phases from 1 on:
- a phase of `accEmpty[b]` needs 128 arrivals;
- no thread arrives twice on `accEmpty[b]` within one phase (R4);
- so the 128 arrivals come one from each thread, including a chosen thread `t`;
- so, projected onto `t`, `accEmpty[b]` behaves as a count-1 barrier that `t` arrives on, whose completion the other
  threads may delay. Delay is stuttering.

R4 itself is not a fact about one thread. A thread's second arrival on `b` follows its wait on `accFull[b]` for the
next round, which follows the issuer's commit of that round, which follows the issuer's wait on `accEmpty[b]`. That
wait means the right phase (P3 for the issuer) only if R4 held so far. So R4 and the issuer's P3 must be proved
together, by induction on the length of the behaviour of the 128-thread system (the first violation of either cannot
come first). And the representative's abstract completion count of `accEmpty[b]` may run one ahead of the real one,
which the transfer of P3 back to the real barrier must account for.

That makes this a simulation from the N-thread system to the one-thread system, with the pigeonhole step inside it:
400 to 700 lines, not a lemma of fifty. The finite part stays small. The untagged one-buffer, one-thread model is to
be counted in V1 (the tagged one has 62 states). The cross-check to run in V1 is the projection check of the two-thread
system (count 2) onto each of its threads, as for the stages. That both models are safe shows nothing about the
reduction.

If Raccoon gains permissions (§4.4), a counting permission (each thread holds one 128th of the buffer and gives it
back with its arrival) replaces R4 and the counting step, which is the main reason §4.4 might change the
recommendation for this protocol.

The handoff (§2.3) is the case of one buffer and one round, with waits that change nothing, so one receiver suffices
by a two-line argument.

#### 4.2.4 The shared-tile typestate

The typestate is a four-state automaton, and T is a regular property of its words. The proof is a case analysis over
four states and four operations, with M5 for loops. Tens of lines. No exploration is needed.

### 4.3 Comparison and order

| | (a) per configuration | (b) invariant | (b′) projection + finite check |
|---|---|---|---|
| covers | the S (and N, `bufs`) checked | every S | every S, `bufs`, N |
| finite part | 48,736 states (untagged, S = 4) to 1,292,736 (S = 6) | none | 88 (ring); the accumulator ring's to be counted |
| evaluation per check | minutes to hours | none | under a second |
| proof once | checker soundness, `succ` completeness | 2,000–3,000 lines per ring | checker soundness, `succ` completeness, R1–R5 and the simulations |
| brittle to | S growing; the other tracks' additions | every protocol change | protocol changes inside one stage only |
| P7 (deadlock) | yes, per configuration, where it fits | would need a variant (liveness) | no |

Recommended order (provisional, §4.4):
1. Build the models and the unverified search and checker, and run them on the faithful ring for S = 1 to 4, the
   reduced ring for S = 6, the one-stage and one-buffer models, and the mutants. This validates the models against
   intuition and against the B200 runs' coverage before anything is proved.
2. Prove the certificate checker sound and each `succ` complete.
3. Prove the stage projection (R1–R3′). That turns the 88-state check into a theorem for every S.
4. Prove the accumulator ring's reductions (R4, R5), or prove it by permissions if §4.4 lands first.
5. Keep per-configuration runs of the combined persistent system (P7) as an untrusted check outside `check.sh`'s
   default run, or drop them, since P7 is not claimed.

### 4.4 A permission-based route, and what stays

Raccoon may gain linear, erased permissions usable in proofs (tracked ghost state in the style of Verus, with
exclusivity, agreement and invariant principles). Protocol safety could then be proved by an invariant over
permissions, in the style of a concurrent separation logic, rather than by exploring configurations:
- a stage's buffer is guarded by a permission for its current generation. The fill holds it while its copies are in
  flight, the full barrier's invariant holds it from phase completion until the consumer's wait takes it, the MMAs hold
  it until the commit returns it to the empty barrier's invariant, and the producer's wait takes it back;
- each barrier carries an invariant indexed by its ghost completion count `n(b)` (§1.2), which says who holds the
  stage's permission in each phase;
- a side's register pair `(stage, phase)` agrees with a ghost round counter by an agreement principle. That is R1 of
  §4.2.2, stated as a permission instead of a projection.

What such a proof needs from this document is independent of the proof route: the rules of §1 are the atomic steps
whose specifications the permissions must meet, §2 fixes the programs to verify, and §3's properties are the theorem's
statement (P1 and P2 become "whoever accesses a stage holds its permission", P3 "each wait's specification names the
phase its invariant is indexed by"). Exclusivity gives P1 and P2 directly and makes the representative-thread argument
of §4.2.3 unnecessary: 128 arrivals, each giving back one fraction of the buffer's permission, is the standard
counting-permission pattern. The model checker would remain useful for:
- cross-checking the invariants on concrete configurations, where a wrong invariant shows up as a reachable violation
  in seconds;
- finding counterexamples while a protocol is designed (the other tracks' additions, §6);
- P7, which an invariant method for safety does not give.

The recommendation of §4.3 is therefore provisional, pending that design. V1 (the models, their properties, the
unverified checker) is needed on either route; V2 and V3 are the steps a permission-based proof would replace.

### 4.5 Raccoon limits this will hit

- **F2 (no `inspect`), F5 (no wildcard), F4 (explicit arguments).** Every `succ` completeness case and every simulation
  case splits on program counters and guards. The guard-as-argument style of §4.1 is the workaround, as `Check.unless`
  was for layer 1.
- **F11 (walks with state).** Avoided for the search by the certificate design, but met once in a small form: the
  fold that builds `T` needs its own induction ("a member of the folded set is in `V`"). The certificate check is a
  plain walk over `V`.
- **F1, F9 (native Nat).** Avoided by `(round, stage)` ghosts instead of `mod`/`div` (R1, R3).
- **Evaluation speed** (§4.1): 3 to 5 ms per state, so the faithful model beyond S = 4 is too slow for a routine check.
- **New: a definition applying the explorer to a literal and a variable does not check.** `def h (S: Nat): Bool :=
  { match Ring.explore(S, 1) returning Bool with … }` did not finish checking in 60 s with the native binary, even
  with fuel 1. Yet `def h (S: Nat): Ring.Result := Ring.explore(S, 1)` checks in 0.08 s, and so does the same match
  when the fuel is a parameter. It looks like F9's normalization into blocked matches, reached by a match on a
  partially known application (not investigated further). The workaround is to keep every argument of an
  evaluation-heavy function a parameter until the call that makes them all concrete.
- **No proof cache.** A certificate stated inside `Gpu` is re-evaluated by every client's check. Finite checks that
  take more than a second belong in separate modules, which only `check.sh` loads.

## 5. Connection to the library

### 5.1 At layer 2

The model states the protocol the library intends. The link is the table of §2.6, which a reviewer compares with
`Gpu.rac`'s emitted instructions, together with the assumptions the model makes of the code:
- a role's steps are the emitted instructions, in program order, run by one thread (M6) or by each thread of the
  aligned warpgroup;
- barrier addresses: `full + 8·stage` and `empty + 8·stage` are distinct for distinct stages and never alias a stage
  buffer (I2);
- the fill's expected bytes equal its copies' boxes (`stageBytes`, §1.3);
- each ordering chain is fenced as §1.6 says.

### 5.2 What layer 3 needs to close the gap

A refinement: every trace of the emitted kernel, projected to one protocol's instructions, is a trace of the model.
That needs:
- an operational semantics of the `Cuda` AST subset: the per-thread control flow, `elect.sync`, the `if (warp < k)`
  splits and joins, loops, and the inline assembly templates as the rules of §1;
- A1–A5 to say which threads run which block (the missing I7);
- a proof that each builder's emitted block, run by the threads its group names, produces the role's steps.

With `Ctx` carrying a proof of the code so far (`OBLIGATIONS.md` §8, layer 3), each sealed operation of §2.6 becomes
a triple whose post-state is a model state: `acquire`'s triple takes `ProducerAt` in model state "acquire" to `Slot`
in state "fill". The tokens are exactly the model's program counters, so the triples are mechanical once the
semantics exists. The hard part is the semantics of warp-level control flow, not the protocols.

### 5.3 A cheap syntactic link now

Possible now, and recommended as a separate step (V5): a checker `Check.protocols` over the emitted `Cuda.Kernel`. It
would find each protocol's instructions by their templates (`Gpu.mbarWait`, `mbarArriveExpectTx`, `tmaLoad2d`,
`mmaCommit`, `mbarArrive`, `mbarInit`, `mbarInval`, which are the library's own strings, as `Check.barrierTemplate` is),
and for each elected block (`if (flag)` after `elect.sync`) or warpgroup block, check that:
- the barrier operations have the role's shape, matched on the AST's structure rather than on a flat trace. For the
  producer: the step body `B = wait(E+8·ps, pp) arrive_tx(F+8·ps, bytes) tma(·, F+8·ps) tma(·, F+8·ps) advance(ps, pp,
  S)`; the role `decl(ps, 0) decl(pp, 0) L D`, where `L` is `loopPeeled`'s `{ B } for (i = 1; …) { B }`, possibly
  inside a tile `for` that may run zero times, and `D` is S copies of `wait(E+8·ps, pp) advance(ps, pp, S)`;
- the operands are the ring's: the base offsets `E` and `F` are the ring's barrier bases, the registers are the side's,
  `S` in the advance is the ring's stage count, and `bytes` is the sum of the boxes;
- every `wait` that precedes a `tcgen05.ld` or a `tcgen05.mma` is followed by `tcgen05.fence::after_thread_sync`;
- the inits, and the setup's arrives on exactly the barriers a producer waits on first, precede a
  `fence.mbarrier_init` and a `__syncthreads`, and the invals follow the last role's join.

What this shows: the barrier operations appear in the modelled order per role, with the modelled operands and fences
(I8 in part). What it does not show: which threads run the block (I7), that the roles' trip counts agree (not needed
for safety), and that the stage registers are not written elsewhere. The last is a simple extra scan: only `advance`'s
statements assign them. It costs one checker in `Check.rac` and one soundness proof against a `Spec` of role traces,
about the size of `Barriers.rac` (274 lines) plus the regular expression's semantics. This answers `OBLIGATIONS.md`
§9, decision 6: the AST need not record which addresses are barriers, because the templates and the operand shapes
identify them. Which threads run a block still needs groups in the AST, or layer 3.

## 6. What is left out, and the other tracks

Left out today, beyond §1.7: remote (cluster) barriers, multicast commits, 2-CTA MMAs and cluster barriers, which
`gpu/encoding`'s pair kernel uses (`encoding/TWO_CTA.md`, A43–A55) but no model covers yet; TMA multicast,
`tcgen05.st`/`tcgen05.cp`, named
barriers between roles other than the split joins, and liveness. The models extend as follows.

- **The TMA-store epilogue (`lemur_gpu`, 975f093).** Each epilogue warp writes 32 columns into one of its two staging
  buffers with generic stores (after `tcgen05.ld`), fences them with `fence.proxy.async.shared::cta` and `__syncwarp`,
  and its lane 0 issues a TMA store and `cp.async.bulk.commit_group`. Before reusing a buffer, lane 0 waits
  `cp.async.bulk.wait_group.read` (bufs − 1), and the tail waits `wait_group 0`. The model needs:
  - **bulk async-groups**, per issuing thread: a TMA store is an async-proxy read of the staging buffer (and a write
    of global memory), from issue to its completion; `commit_group` closes the thread's open group;
    `wait_group.read n` is enabled when at most `n` of the thread's groups still have reads in flight, and
    `wait_group n` when at most `n` have not completed. Sources: `cp.async.bulk.tensor` (the store direction),
    `cp.async.bulk.commit_group`, `cp.async.bulk.wait_group`. A new rule set in §1, of the size of §1.4;
  - **O7** (§1.6): the generic writes of the staging buffer are handed to the async proxy by the fence, and the
    `__syncwarp` makes the 32 lanes' writes precede lane 0's issue (O5 at warp scope);
  - the properties: no generic write of a staging buffer while a TMA store reads it (the `wait_group.read` before
    reuse), every store's source fenced, and P4 extended to "no bulk group outstanding at the join".

  This is a ring of two buffers per warp whose release is a counted wait instead of a barrier phase, so the projection
  of §4.2.2 applies with "groups outstanding" for the barrier state.

- **2-CTA MMA (`cta_group::2`).**
  - One thread of the leader CTA issues MMAs that read shared memory of both CTAs of the pair and write both CTAs'
    tensor memory.
  - `tcgen05.commit.cta_group::2…multicast::cluster` with a CTA mask arrives on the barrier at the same offset in each
    CTA of the mask.
  - Model: barriers and buffers indexed by `(cta, id)`; an `Mma` whose reads and writes span two CTAs; a `Commit` whose
    CommitFire arrives on a set of barriers, one Arrive each; TMA loads by both CTAs signalling the leader's full
    barrier (the peer's copies complete-tx on a remote barrier), so the leader's expect-tx must cover both CTAs' bytes.
  - The per-stage projection still applies: a stage is now a pair of buffers with one full barrier (in the leader) and
    one empty barrier per CTA.
  - New properties: P1/P2 over the peer's buffer, and teardown across CTAs (a CTA must not exit or invalidate while
    its peer may still complete-tx or arrive on its barriers).
  - Whether a multicast commit's arrivals are simultaneous, and how `cta_group::2` MMAs order with respect to each
    other's commits, is **unknown** to this design and must be read from the ISA's tcgen05 memory-consistency section.
- **Cluster barriers** (`barrier.cluster.arrive`/`wait`). A count barrier over the cluster's threads with phases:
  §1.2's rules with count = the cluster's threads, `.aligned` participation (S2), release/acquire at cluster scope. Used
  at init (a peer must not arrive remotely before the barrier is initialized: `fence.mbarrier_init.release.cluster` then
  a cluster barrier, which A7 already names) and at teardown (P4 extended across CTAs).
- **TMA multicast** (`.multicast::cluster` with a CTA mask). One copy writes the same box into several CTAs and
  complete-txs each one's barrier at the same offset: a copy becomes a set of `(cta, dst, bar)` targets. The refill
  hazard crosses CTAs: the producer may refill a stage only after every receiving CTA has released it. So each
  receiving CTA's consumer arrives (remotely) on the producer CTA's empty barrier, whose count becomes the number of
  receivers. That is the accumulator ring's many-arrivals situation again, and §4.2.3's representative argument (R4
  and counting) applies, with CTAs for threads.
- **Attention's barriers between the softmax and MMA roles.** Scores S written by MMA into tensor memory, read by the
  softmax warpgroups (`tcgen05.ld`); P written back (`tcgen05.st`, or shared memory) and read by the second MMA; O
  rescaled by a correction role.
  - Each edge is a ring or a handoff of the shapes here. The new instruction is `tcgen05.st` with `tcgen05.wait::st`,
    a write interval like §1.5's reads.
  - The new structure is a cycle: MMA → softmax → MMA → correction → MMA, with each role both producer and consumer.
    Per-edge projections still give safety.
  - Deadlock becomes a real risk (a cycle of waits), so P7 per configuration becomes more valuable. It remains
    unclaimed unless liveness is taken on.
  - Two softmax warpgroups ping-ponging on named barriers need A3's `bar.sync` as a count barrier (§1.2's rules
    without transactions).

Each extension is a new rule of §1 citing its source, and a new projection or representative lemma where the
structure is new. The per-stage projection is what keeps the finite checks small as these arrive.

## 7. Staged plan

| Step | Content | Size (estimate) | Needs | Uses |
|---|---|---|---|---|
| V1 | `gpu/model/Mbarrier.rac`, `Tma.rac`, `Tcgen05.rac` (§1 as data and rules); `Ring.rac`, `AccRing.rac`, `Handoff.rac`, `Tile.rac` (§2 as `Step` relations and `succ` functions, with the Bool forms of §3); an unverified search; both loop disciplines; runs on the faithful ring S = 1–4, the reduced ring S = 6, the untagged one-stage and one-buffer models, the projection checks (S = 2, 3 onto one stage; two threads onto one), and the §3.2 mutants, as `gpu/checks/` files; the TMA-store epilogue's bulk groups and O7 if V1 starts from `lemur_gpu`; PTX citations checked against the ISA text | 1,200–1,600 lines; S ≤ 3 runs in `check.sh` (seconds), S = 4 and the reduced S = 6 by hand (minutes) | nothing new; §4.5's workaround for matches on partial applications | this document |
| V2 | The certificate checker and its soundness (reachability induction, set membership one way); `succ` completeness for each model | 300 lines for the checker; 400–600 per model for completeness | evidence arguments (done); F2 and F5 workarounds | `NatSet.rac`'s lemma shapes, `Fold.rac`'s `unlessOk` |
| V3 | Projection theorems: R1–R3′ and the stage simulation; per-stage properties from the 88-state check. Result: the stage ring safe for every S | 800–1,200 lines | Nat order lemmas (no `div`/`mod`); an inductive trace relation | V2 |
| V4 | The accumulator protocols: handoff, accumulator ring with one-buffer projection, R5, the N-thread simulation with R4 and the counting step (or permissions, §4.4); the typestate lemma | 800–1,400 lines | a pigeonhole lemma over lists; an induction on behaviours | V2, V3 |
| V5 | `Check.protocols` (§5.3) on the emitted AST, and its soundness against a `Spec` of role traces | 300 checker + 400 proof | nothing new | layer 1's patterns |
| (V6) | The combined persistent system per configuration, for P7 only, outside the default `check.sh` | none new | hours of evaluation at S = 4 | V1 |

The order V1 → V2 → V3 → V4 differs from the one the brief suggested (accumulator protocols before generic S): the
projection makes the finite parts tiny, and every later protocol, including the other tracks', reuses it. V5 is
independent of V2–V4 and can go at any point after V1.

## 8. Open questions

Questions 1 to 4 are answered from the PTX ISA 9.4 text; they stay listed so that references to them keep their
numbers.

1. **O1's fence** (answered, §1.6). Without `tcgen05.fence::after_thread_sync` the ISA does not order a
   `tcgen05.mma` after a preceding wait, so `await` now emits the fence. O2 needs none: a TMA write issued after a wait
   that observed a commit is ordered after the committed MMAs' reads by the chain of §1.6.
2. **The fresh barrier's parity-1 wait** (answered, §1.2). Outside the ISA's defined set; no protocol relies on it
   since the setup completes phase 0 of every barrier a producer waits on first.
3. **Invalidation with pending state, and over-arrival** (answered, §1.2). PTX is silent on both; an operation landing
   on an invalidated barrier is undefined, and the CUDA Programming Guide forbids an arrival on a zero counter. The
   model forbids both. PTX's rule that each phase be observed before the next is arrived on is P8.
4. **Completion order of one thread's `tcgen05` operations and commits** (answered, §1.4). The ISA does not guarantee
   issue order: they may complete out of order, and no pipelined pair orders shared-memory accesses or two commits. The
   model keeps any order.
5. **Where the per-configuration certificates live**, if any are kept: a separate module per S that `check.sh` loads,
   or none once V3 lands.
6. **P7.** Should deadlock freedom under the launch contract be claimed, now that the models could check it per
   configuration? It would need the combined system, which is too large to prove by evaluation at S = 6.
7. **Which code is the target.** V1 should model `lemur_gpu` as it then is, including the TMA-store epilogue (§6), not
   0767971.
8. **The Raccoon finding of §4.5** (a match on an evaluation-heavy partial application at definition time) should be
   reproduced and reported against the kernel, like F9.
9. **The accumulator ring's reduction to one thread** (§4.2.3) is not established. Prove it (R4 with the issuer's P3,
   by induction on behaviours), or wait for permissions (§4.4)?
