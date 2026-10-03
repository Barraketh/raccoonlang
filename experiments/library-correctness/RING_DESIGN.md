# A primitive copy-ring library

This continues the library correctness experiment at its largest missing
boundary: the previous endpoint theorem assumed synchronization at compound
operations. The new library expands those operations into mbarrier primitives
and states obligations on those primitives. Root designed the library, API,
semantics, specifications and lowering; Luna at max effort writes the proofs.

This is an implemented **single-stage, single-CTA copy-ring slice**, not a
replacement for all of Core. It emits CUDA, uses the same ordinary indexed
command descriptions that the scheduler executes, and admits arbitrary typed
clients. TinyGEMM, A3b and pair GEMM are still the acceptance tests for a complete
replacement; this slice cannot implement those kernels yet.

## Client interface

The checked client in `RingClient.rac` is:

```raccoon
def inspect: Ring.Read :=
  Ring.choose(Ring.read, Ring.then(Ring.read, Ring.read))

def program: Ring.Program := Ring.program(
  Ring.producer(Ring.repeat(Ring.fill)),
  Ring.consumer(Ring.repeat(Ring.take(inspect))))
```

`fill` acquires the empty stage and issues its TMA load. `take` waits for the
full stage, runs a description of synchronous reads, then releases the stage.
`producer` adds the final empty wait; `consumer` closes its local endpoint.
`then`, `choose` and `repeat` are typed composition, equal-endpoint branching
and state-preserving runtime loops. Their arguments are descriptions built
eagerly, rather than executions of a callback preview. The compiler expands the
same descriptions into CUDA and the semantic instruction streams.

`ProducerStep`, `ConsumerStep` and `Read` hide the common role/phase indices.
The lower level `Endpoints.Cmd(role,before,after)` remains available for
composition. The root `Program` owns a 64-thread CTA, producer thread 0,
consumer thread 32, one 64x64 bf16 tensor-map box, the physical layout and the
launcher. No callback accepts raw CUDA or an arbitrary memory access. Clients
cannot modify launch metadata separately from the program.

The current `read` describes a discarded scalar read, sufficient to exercise
the access protocol. An API for using the read value in arithmetic, tensor
operations and output still needs design and proofs. This example demonstrates
protocol ergonomics; it does not settle compute-kernel ergonomics.

For now each endpoint's nested loops use its own launch parameter (`PK` or
`CK`), and its branches use `Pflag` or `Cflag`. The semantic theorem deliberately
allows different counts, branch choices and scheduling. Mismatched clients can
deadlock. Safety does not imply progress or functional correctness.

## Authoritative layers

| Layer | Implementation | Responsibility |
|---|---|---|
| Public API | `Ring.rac` | Build checked descriptions and actual `Cuda.Kernel`; root metadata and layout. |
| Local typing | `Endpoints.rac` | Which operation each local endpoint can issue, including branch/loop endpoints. This is the existing relation, not a duplicate. |
| Arbitrary concurrency | `Concurrent.rac`, `Scheduler.rac` | Unknown endpoint programs, independent runtime inputs, blocked queues, asynchronous completion and joint ownership. |
| Raw barrier semantics | `Mbarrier.rac` | Initialization, publication, arrivals, independent expected/completed totals, completed-phase observation and invalidation. No ring invariant. |
| Primitive implementation | `RingPrimitives.rac` | Expand each source operation; relate physical barriers to the derived protocol state. |
| Semantic obligations | `RingObligations.rac` | Independent preconditions at every primitive prefix. These are conclusions of proofs, not arguments to the executor. |
| Exact native contract | `RingBackend.rac` | Independently specify the actual CUDA instruction templates, source-control mapping, setup, close and resource metadata. |
| Combined obligation | `RingLibrary.rac` | One predicate over an unknown public program and its actual execution/lowering. |
| Proofs | `RingProofs.rac`, `RingBackendProofs.rac`, `RingParityProofs.rac`, `RingLibraryProofs.rac` | Establish the implementation and obligations for unknown admitted programs. |

Sealing protects command construction. It is not itself the safety theorem.
The public selectors expose the unrestricted description and its local typing
derivation. The theorem must derive the joint invariant, primitive obligations
and native interpretation from that derivation. No per-kernel invariant or
safety proof is supplied by the client.

## Obligations in library terms

For this slice, `SafeBarrier` says:

- Initialization acts on dead storage; the init fence acts on live storage;
  publication follows the fence. Endpoint uses require publication. The sole
  unpublished arrival is by the initializing thread on its initial barrier.
- A wait names the current or immediately previous logical phase. Successful
  waits record observation, and the next phase cannot arrive before observation.
- A whole-box completion has the expected byte count for a pending issue.
  Expected and completed totals remain separate, so premature completion does
  not disappear through saturating subtraction.
- A final CTA join finds both barriers quiescent; invalidation follows that join
  and cannot erase pending transaction debt. Source closure also derives that
  the communicating stage has no asynchronous work and is empty.
- The consumer explicitly fences its generic reads to the async proxy before
  the empty arrival releases the stage for the next TMA overwrite. Its primitive
  precondition requires the full side to be usable and quiescent.

`Audit` records those facts together with the independently computed raw
transition at every prefix. It includes blocked waits; blocking grants no
ownership and does not consume the source command. `run` does not take `Safe`
as a guard. For example, raw invalidation can erase a pending barrier; the
library proof must show that it never does so.

The principal result is a refinement for arbitrary positive byte counts:

```text
Invariant(s) and LocalTyping(action,s)
  imply
  run(expand(action,s), representation(s)) = representation(step(action,s))
  and every executed primitive in expand(action,s) meets its obligation.
```

Induction lifts it to any `Concurrent.Execution`, and the existing scheduler
produces such an execution for any producer/consumer commands, runtime inputs
and schedule. Setup must establish the initial representation by its actual
primitive trace. Retirement must derive quiescence from genuinely exhausted
endpoint queues before executing join and invalidation.

The native result checks each arbitrary typed description against independent
instruction templates. Changing a full/empty address, byte count, phase
register or initialization/close order should invalidate that proof. This is
more concrete than a detached model theorem. `Shell(p)` additionally binds the actual kernel to independent root assembly, thread guards, phase initialization, parameter declarations and launcher metadata; proving only its endpoint children would leave that enclosing boundary unchecked.

## Universal theorem interface

```text
forall p : Ring.Program, pr, cr, schedule,
  RingLibrary.Guarantees(p, pr, cr, schedule)
```

`RingLibraryProofs.everyProgram` supplies this result. Its conclusions are the
exact native artifact, primitive audit/refinement of the actual execution,
contract-level memory safety, absence of endpoint collectives, native parity
trace, structural-checker soundness, setup audit, and safe shutdown when both
actual endpoint queues are exhausted. The setup establishes the representation;
the shutdown theorem derives empty storage and no pending work rather than
accepting those facts from a client. There is no kernel-specific proof argument.

`CheckSound` is conditional on the actual structural checker succeeding, as is
`Ring.render`. It does not claim the checker accepts every conceivable command
description. `ShutdownSafe` is conditional on completed queues, so an incomplete
or deadlocked schedule does not imply that invalidation can run.

The component results remain useful independently: `macroCorrect` for any
positive byte count; `everyExecution` over arbitrary locally typed concurrent
histories; `retirementClose` from exhausted queues; `compilePlan` for arbitrary
typed syntax; and the native parity agreement lemmas.

## Relation to S1–S6

| Obligation | This slice's intended argument | Remaining boundary |
|---|---|---|
| S1: races | Existing arbitrary-client ownership and happens-before proofs, with their waits/releases validated by the primitive refinement and exact templates. The input is immutable under the launch contract. | The memory interpretation still uses documented acquire/release and TMA contracts. Full Core's accesses and async classes remain outside this slice. |
| S2: participation | Two unconditional CTA synchronization sites surround individual endpoint code; `everyEndpointNoCollectives` proves arbitrary compiled endpoints contain only this slice's individual operations. | The collective completion contract still supplies the actual CTA rendezvous; progress is separate. Richer participant groups remain outside this slice. |
| S3: protocols | Actual initialization, publication, phase observation, matched bytes, empty/full protocol and drained invalidation. | One count-one stage and coalesced whole-box completion; arbitrary arrival counts, multi-stage indexing, tensor-core completion and two-CTA protocols remain. |
| S4: allocation | Root fixes barriers to `[0,16)`, stage to `[1024,9216)`, alignment to 1024 and dynamic shared bytes to 9216. | No tensor-memory allocation is exposed. A reusable layout/launch theorem is still needed as the library expands. |
| S5: output | No output primitive is exposed. | Output permissions, schedules and claims must be integrated before this is a complete GPU library. |
| S6: C++ | Actual `Check.WellFormed` is required before rendering. Fixed external names and fresh local IDs avoid client-chosen names. | The current checker/specification's known omissions remain; its existing soundness theorem establishes precisely its documented subset. |

These boundaries are part of the result. A proof for this slice must not be
reported as an S1–S6 theorem for all Core kernels or the earlier client ports.

## Platform and backend assumptions

The barrier operational contracts summarize A6–A9 of `gpu/OBLIGATIONS.md`.
Publication stands for the initializing thread's release fence followed by CTA
synchronization; join stands for completion of the final CTA synchronization.
A TMA load eventually supplies its box's bytes to its attached barrier and its
writes become visible through the completing acquire wait. Logical epochs are
ghost indices; hardware uses alternating parity. `RingParityProofs.everyKernel` proves that the native bit updates track the logical endpoint rounds for the actual arbitrary execution. `phaseWaitAgrees` proves that current-or-previous valid phase waits give the same ready result in the bit and logical models. The primitive audit establishes that phase-validity premise. A general native control-flow/PTX simulation remains outside this contract-level result.

The extra consumer proxy fence makes the generic-read-to-async-write direction
explicit before release. PTX describes proxy fences as ordering accesses across
proxies and composing with thread synchronization; see
[the official fence specification](https://docs.nvidia.com/cuda/parallel-thread-execution/#parallel-synchronization-and-communication-instructions-membar).
The model treats the fence as a barrier-state no-op with a separate memory
ordering contract. It is present in both the primitive expansion and the exact
native release template.

The platform is trusted to implement these documented operations. We do not
assume the compound ring API is safe. Exact native template proofs constrain
the lowerer to those operations. The CUDA printer, C++/PTX compiler and hardware
retain the repository's existing trust boundary. Host C++ syntax checks do not
validate PTX or execute the kernel. The scheduler interleaves source actions,
while each source action has a primitive prefix audit. It does not enumerate
all native instruction interleavings inside those actions, prove a general
CUDA-to-source trace correspondence, or model every physical TMA transaction.
The exact templates and parity lemmas supply the intended contract connection;
that remaining native simulation must not be inferred from the aggregate alone.

## Friction and the language decision

Actual proof attempts are logged in `RING_PROOF_FRICTION.md`,
`RING_BACKEND_FRICTION.md` and `RING_PARITY_FRICTION.md`; root design and integration corrections are in `RING_DESIGN_FRICTION.md`. Distinguish four
questions: whether an invariant is true, whether the API enforces its premises,
whether the language can express the proof, and how much mechanical work the
proof requires. A new typing judgment should be justified by the latter two
problems after the former two have been resolved.

One lowering issue already occurred: using fixed local IDs in repeated reads
and loops failed the real structural checker with `v3 declared twice` and
`v2 declared twice`. Passing a fresh-ID supply through composition, branches
and loops fixed it. That is ordinary compiler bookkeeping, not evidence for
reflected typing or a new state-machine judgment.

The next extensions must reuse this representation/refinement boundary:
multiple stages and round-robin phase tracking; tensor allocation and distinct
async reader/writer completion; exact publication coverage and output authority;
then register restoration, A3b's chained handoffs and pair rendezvous. Each adds
primitive effects and independent obligations, rather than taking a compound
library operation's safety as a platform axiom.

## Next acceptance milestones

1. Parameterize stage count and layout, use resource identities in the indexed
   command world, and prove framing plus round-robin phase tracking. Keep the
   actual launcher and kernel assembly in the specification.
2. Add values, arithmetic, tensor allocation, MMA completion and output stores
   to that same command description. Integrate the existing resource/publication/
   permission lemmas into universal public-program theorems. Then port TinyGEMM
   through this implementation with the library theorem applying automatically.
3. Extend that implementation for A3b's chained handoffs, register split/restore
   and pair GEMM's multicast/two-CTA rendezvous. Port both clients, measure their
   interface friction, and prove the enlarged library obligations independently
   of those clients.
4. Compare the measured proof effort with an explicitly specified Core typing
   reflection route. The current result supplies a working ordinary-dependent-
   typing baseline; it does not demonstrate that reflection or a compiler-level
   state-machine judgment could never improve the interface or proof tooling.

Each milestone should keep one API, one authoritative command/primitive
interpretation and one theorem about every admitted program. The earlier full
client ports provide concrete interface/AST comparison fixtures; their existence
alone does not connect them to these universal primitive proofs.

## Validation

`python3 experiments/library-correctness/run.py` passes 71/71 checks: 42
accepted modules and 29 intentionally rejected fixtures with exact local
proof/type diagnostics. The runner rejects 33 mutations, including 17 new
primitive-ring/backend changes. The debt mutant is well typed and ignores actual
completion; it fails the primitive proof. Other mutants cover missing bootstrap,
byte completion, phase, drain/join, addresses, map geometry, proxy fences, root
thread selection, setup/close assembly and shared-memory extent.

The actual `RingClient` emits `ring-generated.cu`, which passes the host C++
syntax check with inline PTX replaced by the repository stub. PTX compilation
and GPU execution were not tested. The original retirement artifact and the
never-launched Core representation counterexample remain separate fixtures.

The initial aggregate corpus attempt passed 70/71, then passed fully after
Luna corrected the grouped-function proof shape. A later mutation harness
attempt stopped on an unrelated unreachable-branch diagnostic; the mutant was
corrected and the final complete run passed. Those failures are recorded in
the friction logs rather than counted as successful safety checks.

`sbt validate` also passes formatting and all 936 tests (0 failures, 0 errors).
The logs for this run are `/tmp/raccoon-primitive-ring-experiment.log` and
`/tmp/raccoon-primitive-ring-validate.log`.

On October 3, the experiment work was rebased onto `codex/native-buffer-program`
at `eed468e`, including `codex/frame-composition-experiments` at `321d5b6`.
The shared lowering retains upstream's `Core.checkedKernel` accessor requiring
`Core.WellFormed` evidence alongside the experiment's `Core.kernelSyntax`. TinyGEMM's baseline fixture now
tracks the upstream definitions in `gpu/encoding/TinyGemm.rac`; the example file
imports those definitions and renders the kernel.

On this base, `sbt validate` passes formatting and all 1037 tests. The library
runner again passes 71/71 checks and rejects all 33 mutations, with the host C++
syntax checks passing. TinyGEMM passes 46/46 checks, complete AST comparisons
and byte-identical CUDA; the A3b/pair runner passes 35 fixture checks, all eight
variant AST comparisons, both byte-identical CUDA/launcher comparisons and both
lowering mutations. Logs are `/tmp/raccoon-native-rebase-validate.log`,
`/tmp/raccoon-native-rebase-library.log`, `/tmp/raccoon-native-rebase-tiny.log`
and `/tmp/raccoon-native-rebase-full.log`.

The earlier state-machine, compositional and extensible experiment runners pass
69/69, 34/34 and 37/37 checks respectively. Their logs use the same
`/tmp/raccoon-native-rebase-` prefix followed by `state-machines.log`,
`compositional-machines.log` and `extensible-machines.log`.

The preserved record reproducer still exceeds a 15-second limit on this base;
the log is `/tmp/raccoon-native-rebase-record.log`. Earlier timing observations
describe the original base. The new positivity-cache prototype remains held
aside, and this integration adds no further performance optimization.
