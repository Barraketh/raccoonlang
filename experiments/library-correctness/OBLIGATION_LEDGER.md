# Remaining-obligation experiment

This extends the retirement experiment with library-level proofs for ownership,
communication, participation, allocation, publication, output and claims. The earlier model proofs were written directly. In the subsequent [primitive-ring continuation](RING_DESIGN.md), root designed the API, raw semantics, lowering and independent obligations; Luna at max effort wrote the checked proofs and recorded [proof friction](RING_DESIGN_FRICTION.md).

**The full theorem for every CUDA kernel produced by Core or the replacement is
still unproved.** The checked results below are universal semantic theorems;
their subjects and assumptions are stated explicitly. Most new results concern
an executable model or indexed IR. They do not establish that the existing full
cursor API, or its three client ports, implements that model.

## The communicating-endpoint result

`Endpoints.Cmd(role, before, after)` is a sealed ordinary indexed command. It
supports composition, equal-endpoint branches, and invariant-preserving loops.
Its data describes the actual code; its proposition certifies the local phase
transitions. `Endpoints.expansion` proves that expansion under arbitrary runtime
branch choices and loop counts produces a locally typed instruction stream.

`Scheduler.kernel` executes two unknown endpoint commands under an arbitrary
schedule. A producer, consumer or asynchronous-completion event may be selected
at every tick. A blocked command remains at the queue head. The two runtime loop
counts need not agree. No client supplies the joint invariant, access safety, or
a proof that its particular kernel is correct.

```text
forall producer : Cmd(producer, ready, done),
       consumer : Cmd(consumer, ready, done),
       producerRuntime, consumerRuntime, schedule,
  Audit(actualExecutedActions, initial, actualFinalState)
```

`Scheduler.everyKernel` proves this statement. `Audit` records the independently
computed raw transition at each prefix and its derived access precondition.
`Concurrent.preserve` proves the shared invariant from local typing: counters
refer to the same slot round; an asynchronous write cannot coexist with a held
consumer; reuse waits for release; producer retirement cannot skip the drain.
The executor's asynchronous flag is independent of the slot's phase label.
Changing a label alone cannot erase in-flight work.

`Scheduler.retirement` derives an empty slot and no asynchronous work when both
command queues have actually finished, then proves that the raw close preserves
the invariant. It does not assume those global facts as close preconditions.
Finite schedules can end incomplete, and disagreeing roles can block forever.
This proves safety, not progress.

`Coupled.noRace` connects that same execution to an explicit memory contract.
Producer acquisition, asynchronous issue and consumer acquisition produce
synchronization edges; writes and reads produce program-order edges. Blocked
operations produce no memory handoff. `History` proves fresh event identities,
so distinct actors' accesses are distinct events joined by a happens-before
path. The result quantifies over the same unknown clients, runtime inputs and
schedules. It orders even pairs of reads, a stronger property than needed for
one exclusively owned region.

**The synchronization edges are primitive contract assumptions.** Their intended
CUDA implementation must have the actual empty/full waits, release/acquire
semantics, and proxy/tensor fences. This model does not derive those edges from
PTX. It also represents an asynchronous write by one abstract event; it does
not model every transaction of a TMA operation. The theorem is therefore a
race-freedom theorem for this contract semantics, not yet the full CUDA S1
claim. Removing any of the three handoffs breaks the checked coupling proof.

## The primitive-library continuation

`RingLibraryProofs.everyProgram(p, pr, cr, schedule)` proves
`RingLibrary.Guarantees` for an unknown actual `Ring.Program`, independent of
any particular kernel's functional correctness. The implementation emits
`Cuda.Kernel` from the same indexed descriptions that the scheduler executes.
The aggregate contains the exact native artifact and enclosing kernel shell,
primitive audits/refinement, contract-level race freedom, individual endpoint
participation, parity trace, conditional checker soundness, setup audit, and
safe close after actual queues are exhausted.

`RingProofs.macroCorrect` derives every primitive precondition and raw transition
from the joint invariant and local action typing, for any positive byte count.
`everyExecution` lifts this over arbitrary source histories; `everyProgram`
uses the actual API/scheduler. `retirementClose` derives no pending work and
empty storage from the exhausted queues. `RingBackendProofs.compilePlan`
constrains arbitrary compiled syntax to independent native templates, while its
artifact theorem binds the actual root assembly, participants and launcher.
`RingParityProofs` proves exact issue/release bit updates and valid phase waits.

This completes the count-one, single-stage **copy-ring slice's specified
contract-level obligations**. It has one whole-box completion class, a discarded
scalar read, fixed resources, no tensor allocation, no outputs and no register
split. It does not replace Core or prove the three earlier client ports.
Hardware synchronization contracts, the printer and toolchain remain trusted;
a general CUDA/PTX execution refinement has not been implemented.

## The other universal proofs

| Module / theorem | What it proves | Boundary |
|---|---|---|
| `Regions.bounded`, `freshDoesNotAlias`, `everyAccessInBounds` | Induction over arbitrary bump allocations yields physical interval separation and allocation bounds. | Mathematical byte offsets; symbolic identity freshness, scoped capabilities, native `alignUp` and actual launch allocation are not connected. |
| `Regions.placement` | A proof-producing validator accepts only positive alignment, aligned base, non-overlap with the allocation frontier and a fitting end. | It validates proposed offsets; it does not prove the native placement algorithm. |
| `ConcurrentWorld.everyOtherResource` | Updating one resource leaves every distinct resource ID's state exactly unchanged. | Reuses the existing generic `World` proof; IDs are not yet tied to the physical regions above. |
| `Coverage.numbersAgree`, `flagsAgree`, `everyParticipant` | Uniform expressions evaluate equally; all participants execute the same collective-site trace through arbitrary nested branches/loops. | Common participant inputs and mathematical arithmetic. Exact group membership, warp votes/broadcasts, aligned warpgroups and native lowering are not proved. |
| `Geometry.injective` | Equal row-major scalar addresses with bounded columns imply equal rows and columns. | Does not identify a native thread/CTA with those coordinates, establish tile box geometry, or prove absence of C++ arithmetic wrap. |
| `Schedule.injective`, `distinctVisitors`, `repeatedVisitor`, `distinctHalves` | Arbitrary strided visits are disjoint across visitors and iterations; pair ranks below two name distinct halves. | A simpler possible schedule, not a proof of Core's band-order bijection, grid mapping, or every native store. Coverage is a separate functional property. |
| `Outputs.everyTrace` | Consuming unique write permissions yields a unique write-address trace; discarding permissions is permitted. | The trace does not assume output uniqueness. Its connection to native stores and root permission distribution remains. |
| `Publication.conserved`, `complete`, `everyChunk`, `exactlyOnce` | A fully consumed publication permission set accounts for every expected chunk written exactly once. | Publication cannot discard chunks. Actual stores, initialization and visibility require the lowering and memory contracts. |
| `Claims.everyInterleaving`, `exclusive` | For any initial decoded owner word and any finite list of one epoch's observations and CAS attempts, two successful owner IDs are equal. | Arbitrary stale snapshots are allowed. A41 supplies atomicity; 64-bit packing, owner-to-warp identity, arm confinement and once-per-owner output authority remain. Overlapping epochs are excluded. |
| `Tensor.preserve`, `accessBound`, `beforeFree`, `freshAtMostOnce` | Any locally permitted lifecycle preserves allocation state, stays within allocated columns, frees quiescently and allocates at most once. | Independent permit/allocation/asynchronous fields are tracked. Tensor load/store/MMA distinctions, native collectives, aligned windows and overlays are not modeled. |
| `Budgets.countSound`, `fitsSound`, `everySplit` | The actual `Registers.countOk` and `Registers.fits` predicates imply valid counts and the CTA register budget bound. | Split indices use the same threads/residency metadata. Hardware initial counts, per-warpgroup transitions, join, restoration and the final CTA barrier are not proved. |
| `Structural.everyRenderedProgram` | Every Core program admitted by the real structural checker satisfies existing `Spec.WellFormed`. | Precisely I1–I6's current structural subset; the specification's documented omissions still apply. |

The tensor, output and claim results quantify over execution/permission
relations. They are not yet theorems over an unknown full GPU command. The
endpoint scheduler and coupled memory result *are* source-command theorems for
their restricted IR. That difference matters when evaluating progress.

## S1–S6 ledger

| Obligation | Checked progress | Work still needed for the actual library theorem |
|---|---|---|
| S1: no races | Coupled exclusive-slot happens-before theorem, region separation, resource framing, coordinate injectivity and atomic owner exclusivity. | One common interpretation tying regions, actors, permissions and synchronization to every actual access, including asynchronous reads and global memory. |
| S2: collectives | Generic expression uniformity and identical per-participant collective traces. | Exact required participant sets and convergence for CTA, warp, aligned warpgroup, leader and warpwise code; interpretation of each native collective. |
| S3: asynchronous protocols | Concurrent ownership, completion, counters, blocked waits, drain and close; actual single-stage mbarrier setup/publication, byte accounting, phase/parity, drained invalidation and exact native kernel/template contract; complete bulk-store wait fragment. | General arrival counts, multiple stages, pair/alpha participants, distinct completion classes and full native execution refinement. The fixed ring stores parity bits rather than narrowed logical epoch counters. |
| S4: resources | Shared interval bounds; fixed ring barriers/stage bound to the actual launcher and kernel shell; tensor allocation-at-most-once, access bounds and quiescent free. | Root resources tied to launch metadata, physical shared/tensor layouts, pair allocation/lifecycle and exact native accesses. |
| S5: output | Unique permissions, row-major and strided-schedule injectivity, pair-half injectivity, publication coverage and claim exclusivity. | Root permission distribution and confinement, tile/store geometry, native coordinate arithmetic, and claims' once-per-owner authority. Existing band ordering remains unproved. |
| S6: C++ | Existing checker-soundness theorem applies universally to admitted Core programs. | Full prose claim exceeds its predicate: keyword/host-symbol exclusions and other documented omissions remain. The new IR's complete lowering/name-scope theorem is absent. |

## Discipline ledger

The M rules explain how source typing should imply the obligations; they are not
independent substitutes for the semantic theorem.

| Rule | What the experiment establishes / what remains |
|---|---|
| M1: emitter order | Endpoint expansion and the scheduler preserve command order; the old target fragment composes exact blocks. Full emitter interpretation remains. |
| M2: lifetimes/scopes | Structural checker handles generated name scopes. Fresh capability identity, scope escape and the source-to-C-scope relation remain. |
| M3: groups | Participant trace equality is proved for uniform control. Exact group identities, membership and alignment remain. |
| M4: tokens | Sealed indexed commands carry separately proved derivations; linear emitter values need not appear in propositions. Full authority/freshness interpretation remains. |
| M5: fixed state | Endpoint branches agree on their endpoints and loops preserve a phase for every runtime expansion. Full resource worlds and all callbacks remain. |
| M6: thread affinity | Producer/consumer identities are distinct in the slot/memory model. Native elected-thread registers and warpgroup affinity remain. |
| M7: quiescent reuse | Shared slot reuse follows release; pending writes cannot be read or retired. Physical reuse and asynchronous reads remain. |
| M8: construction/render | Existing structural theorem, old exact target template proof and fixed-ring exact endpoint/root assembly proof. Full Core emitted-program production and semantic interpretation remain. |
| M9: fences after joins | Memory coupling requires explicit synchronization edges; missing handoffs fail. Refinement to actual tensor fences and joins remains. |
| M10: grain | Uniform expression evaluators agree generically. Stable shared reads, input reads, votes, broadcasts and cluster inputs remain. |
| M11: FIFO/deadlock safety | Unknown typed endpoint clients cannot outrun the communicating slot, for arbitrary schedules and differing trip counts. The fixed ring additionally proves primitive bytes and native parity. General arrival counts, multiple stages and pair protocols remain. |
| M12: row ownership | Generic coordinate and schedule injectivity. Native row-affinity and permission-distribution proofs remain. |
| M13: tensor publication | Generic synchronization graph and tensor lifecycle pieces. Exact tensor-written publication/consumption refinement remains. |
| M14: complete coverage | Generic publication theorem accounts for every chunk, without discards. Native chunk stores and visibility remain. |
| M15: finishers | Unknown endpoint streams finish only in `done`; retirement derives quiescence. Full set of actual openers, sides and finishers remains. |
| M16: overlays | No overlay theorem yet. Distinct async-read classes and pipelined same-thread dependencies must be represented. |
| M17: claims | Arbitrary one-epoch atomic interleavings have exclusive owner IDs. Packing, arm confinement and root linear output authority remain. |
| M18: pair lockstep | Generic schedule/half injectivity and earlier leader framing are available. No joint two-CTA protocol, multicast accounting or cluster lifecycle theorem yet. |
| M19: pair resources | Region/layout pieces are available. Top-level spine restriction, equal peer layouts, group consistency and collective close remain. |
| M20: leader | Earlier `Frame` theorem preserves every peer predicate exactly. Full native leader authority, work and register isolation remain. |
| M21: warpwise | Global trace-uniformity proof alone is insufficient. Per-warp convergence and exclusion of whole-group protocols remain. |
| M22: alpha ring | One communicating-slot ownership theorem applies structurally. Row correspondence, 128/256 arrivals and the exact producer/consumer protocol remain. |
| M23: callback coverage | Endpoint expansion quantifies over runtime inputs rather than eager preview values. Full callback-to-IR elaboration/logical relation remains. |
| M24: registers | Generic native predicate soundness and immutable metadata indices. No full split/restore concurrency proof yet; Core's public `Registers.pool` carve-out persists. |

## What this says about the language alternatives

Ordinary dependent typing continues to work for the substantially harder shared
invariant and source/scheduler proof. It also expresses the separation,
participation, publication, resource and claim propositions. There is no checked
case here that requires a new primitive machine typing judgment.

The difficult argument is now predominantly the common semantic interpretation:
what each access means, who executes it, which hardware event orders it, and how
the protocol counters and physical layout correspond. Reflecting a typing
judgment does not supply that interpretation automatically. A new native
judgment could generate useful derivations, but its soundness would still need
the same semantic lemmas. None of this establishes that either route is
impossible or has no ergonomic benefit.

The concrete constraint encountered is proof erasure: `Stream` and `Invariant`
are propositions, and Raccoon correctly refuses to eliminate them to choose
runtime queues or instructions. Commands retain ordinary data, such as the
instruction list and next phase; their propositions justify that data. Equality
transport moves queues between proven equal phase indices. No quoting,
reflection implementation, implicit-semantics change or evaluation-strategy
change was needed. Eager evaluation is preserved.

A proof-oriented replacement should consequently have one indexed command IR,
one checked lowerer to `CudaAst`, and an elaborated imperative facade. Its root
builder should own immutable launch/resource metadata, with all permissions
and register pools derived from it. The current full cursor facade can be a
surface candidate, but its emitter must produce this IR or an equivalent
checked derivation; the port results alone do not supply one.

The count-one single-CTA mbarrier ring now has that refinement and independent
primitive audits, plus exact native assembly and parity proofs. The next
extensions are multiple stages, tensor completion and output authority, followed
by pair and alpha-ring participants. They must extend the same public library
and common interpretation rather than create detached protocol results. The
register split/restore protocol needs a similar concurrent resource proof.
These are unfinished obligations, not reasons to add a compiler judgment yet.

## Validation

Run `python3 experiments/library-correctness/run.py`, followed by `sbt validate`.
The current run passes 71/71 checks: 42 accepted modules and 29 rejected fixtures
with their exact local diagnostics. `sbt validate` passes formatting and all 936
tests. It also emits and host-syntax-checks the original retirement fragment and the
primitive-ring client, runs the defining-module representation probe, and rejects
33 mutations (16 earlier semantic mutations and 17 primitive/backend mutations).
New positive examples include blocked premature waits and drains, stale CAS
loss, reused epochs, divergent participant traces, failed placements, and a real
duplicate write trace when the initial permissions are duplicated.

None of the generated CUDA artifacts is executed on a GPU, and these host syntax checks do not compile PTX. The new obligation models
are not GPU benchmark kernels. Production compiler/library implementation is
unchanged by this continuation; earlier port/compiler changes remain in the
workspace.
