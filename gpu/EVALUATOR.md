# An evaluator for generated kernels

Status: **proposal with a bounded generic execution path** (updated 2026-10-03; originally 2026-10-01). Step 1, typed instructions, is built (§3). The source-only generic `Buffer.Program` path for the checked 128×128×64 one-CTA TinyGEMM workload has passed its focused API, decoder and scheduler tests, and `sbt validate` passed 1,029/1,029; two seeded benchmark runs are reported in §12. The Scala GPU-aware host-buffer prototype and its measurements in §11 are historical and were removed from the current branch; they do not measure the generic buffer executor. Earlier JVM samples point to interpreter binding/application and proof handling; native JFR samples identify polling sites rather than exclusive method costs. A source-only ring-helper fusion A/B did not establish a reliable speedup. Existing evidence supports C1 performance work on Raccoon's own evaluator, but does not quantify broad redesign savings or make the proposed evaluator v0 complete. It follows the first B200 session (`gpu/encoding/NOTES.md`,
"Hardware session"), whose failures and the hostile reviews before it share one shape: the generated code did
something other than what was meant.

## 1. The problem

**What checks a kernel today:**
- **the types:** protocols, linearity, scopes and sealing in `gpu/encoding/Core.rac`;
- **the certificate:** the structural invariants of `gpu/Check.rac` (OBLIGATIONS §4), proved sound against
  `gpu/Spec.rac`;
- **the stub compile:** the generated C++ compiled against `gpu/stub/`;
- **the mutants:** programs the core must refuse;
- **the host mocks:** C++ emulations of each kernel, run under the harnesses.

**The gap.** None of these runs the generated code. The mocks come closest, but each emulates what its kernel is
*meant* to do, written by hand next to it. So the core's own arithmetic is checked only by review and by hardware:
- addresses, rows, columns, guards;
- what a conditional block runs, and on which threads.

**What slipped through:**

| Defect | Found by | Shape |
|---|---|---|
| The append wrote 32 lanes × 8 columns of a 128-column row | hardware | the core's column arithmetic |
| The decode harness compared bf16 bits with unrounded floats | hardware | the harness, hidden by the mock |
| A3b deadlocked in `setmaxnreg` | hardware (`cuda-gdb`) | a schedule nobody reasoned about |
| A3a's causal kernel needed 184 registers for 384 threads | hardware | `ptxas`'s register allocation |
| A3a's rows came from the warp number, so a misplaced warpgroup wrote another CTA's rows | hostile review | the core's row arithmetic |
| P2's lanes recomputed the claimed page | hostile review | data flow in the core |
| `onLeader` let the peer skip its store wait | hostile review | which threads run a block |

## 2. The proposal

Two parts:
1. **Typed instructions** in the CUDA AST (`gpu/Cuda.rac`), in place of inline-assembly template strings.
2. **An evaluator** of that AST that executes generated kernels on the host and checks them as it goes. A battery of
   differential tests holds it to the hardware.

## 3. Typed instructions

Status: **built** (step 1 of §8).

**Before.** `Cuda.Stmt` covered plain C: declarations, stores, loops, branches and `__syncthreads`. Every PTX
instruction went through `Stmt.asm(template, outs, ins)`, about 35 distinct instructions at 47 sites in `Core.rac`.
- The certificate checker could not see them, beyond matching `bar.sync`'s template.
- Descriptors were integers packed by hand, then printed into strings.

**Now.** `Stmt.instr(i: Instr)`, in `gpu/Cuda.rac`. `gpu/encoding/Core.rac` emits every PTX instruction through it.
`Registers.rac` emits none. `Stmt.asm` is gone: the retired `gpu/Gpu.rac` was its last user.
- **Operands** are `Expr`s.
- **Results** are variable ids: the instruction writes the fresh variable `d`, which a `declOut` before it declares
  (`Core.written`), of the instruction's result type (`Cuda.resultType`).
- **Qualifiers** are fields of their own types: `CtaGroup`, `BarrierScope`, `Scope`, `Window`, `Arrival`, `ThreadSync`,
  `BulkWait`, `TmemWait`, `TmemShape`, `Word`, `Rounding`, `RegChange`, `SpecialReg`. A count that PTX takes as an
  immediate (`wait_group`'s, `setmaxnreg`'s, `shfl`'s lane, the multicast mask) is a `Nat`. A vector's width is its
  operand list's length (`.x8`, `.v4`).
- **Descriptors** are values with named fields:
  - `InstrDesc(m, n, transposeB)`, the MMA instruction descriptor. The printer packs it at generation
    (`Cuda.Asm.packInstrDesc`) into a 32-bit literal operand, each field cut to its bits.
  - `SmemDesc(base, lbo, step)`, a shared-memory descriptor. `base` is a run-time address, so the printer packs it
    into a C expression evaluated at run time (`Cuda.Asm.packSmemDesc`): `base`'s bits shifted and masked, or-ed with
    a 64-bit literal of the fixed fields and the encoded leading byte offset, plus the step.
- **Printing.** `Cuda.asmOf(i)` lowers an instruction to inline assembly: a template and its operands. The forms are
  CUTLASS's where it has the instruction, FA4's for `ex2Emulated`, and the core's own for the rest. `Stmt.instr`
  prints through `Cuda.Asm.text`. The printer's parts are in `Cuda.Asm`, which `open Cuda` does not open. Every
  example under `gpu/encoding/examples/` generated byte-identical CUDA across the change.

**The constructors:**

| Family | Constructors |
|---|---|
| mbarrier | `mbarInit`, `mbarInval`, `mbarArrive` (window, whose scope it releases at; `Arrival.one`/`count`/`expectTx`), `mbarWait` (scope; a spin on `try_wait.parity`) |
| barriers | `barSync`, `clusterArrive`, `clusterWait` |
| fences | `fenceMbarInit`, `fenceProxyAsync`, `tcFence` (`before`/`after`) |
| TMA | `tmaLoad` (CTA group), `tmaStore`, `bulkCommit`, `bulkWait` (`read`/`complete`, pending) |
| tcgen05 | `tmemAlloc`, `tmemRelinquish`, `tmemDealloc`, `mma` (CTA group, A as `MmaA.smem`/`tmem`, B's `SmemDesc`, `InstrDesc`), `tcCommit` (CTA group, multicast mask), `tmemLoad`/`tmemStore` (shape), `tmemWait` (`load`/`store`) |
| warp | `elect`, `shfl`, `voteAny` |
| registers | `setMaxNReg` (`inc`/`dec`, count) |
| math | `movF32`, `ex2`, `lg2`, `ex2Emulated`, `rcp` (rounding), `cvtBf16x2` |
| global memory | `ldRelaxed`, `casRelaxed` (scope) |
| cluster | `movSpecial` (`%cluster_ctarank`, `%clusterid.x`, `%nclusterid.x`), `mapa` |
| shared memory | `stShared` |

**Blocks of their own.** Some instructions print as a short PTX block, as their templates did: `mbarWait`'s spin loop,
`mma`'s predicate, `tcCommit`'s mask register, `elect`'s flag, `voteAny`'s predicates, the `cvta` of `ldRelaxed` and
`casRelaxed`. `ex2Emulated` is FA4's sequence of f32 and integer instructions. The evaluator gives each its
meaning as a unit.

**The certificate.**
- **I1, I2, I4, I5.** A statement's expressions include an instruction's `Cuda.instrExprs`: the expressions it prints
  as operands, packed descriptors included. `Spec.OwnExpr.instr` is stated over them, and `proofs/Instructions.rac`
  proves that `Cuda.asmOf` prints exactly those, in order.
- **I3.** A named barrier in 1..15 is `Instr.barSync`, the only statement that prints one (`Stmt.sync` is barrier
  0). `Check.namedBarriers` reads it.
- **I4.** Every instruction is `Spec.InRange`: the immediates its template prints, each in its range, an MMA's shape
  one of Table 48's for its CTA group, and the fields the printer packs into its descriptors fitting them (OBLIGATIONS
  I4 lists them). `Check.inRange` decides it, and the packers cut each field to its bits.
- **The proofs** gained a case for `Stmt.instr` each; `Literals.rac` proves the ranges. No statement of `Spec.rac`
  got weaker for what the core emits.

**Not yet used.** No `Check.rac` rule reads an instruction's place in the kernel. Two are now possible:
- which barrier a wait names, and which group runs an aligned instruction (I7, I8), once the AST records which threads
  run a block;
- the `setmaxnreg` placement rule of `encoding/REGISTERS.md` §9 (below).

**The `setmaxnreg` placement rule.** Every `setMaxNReg` is a warpgroup's entry change in a split, or its change back
after the join, with counts that fit the pool. What it takes now:
- **Finding them** is done: a fold over `Instr.setMaxNReg`, and the AST has no raw `asm` that could hide one.
- **The pool.** The rule needs the kernel's threads and residency. `Cuda.boundedKernel` takes them beside the kernel;
  `Kernel` would carry them.
- **The warpgroup.** The rule needs which warps run the arm a `setMaxNReg` heads. The AST does not record it. A split
  prints as `if (warp < f + k)`, so the checker could read warp ranges off such conditions, or `Stmt` could record a
  split's groups. The second is the I7 work.
- **The join.** The change back and the CTA barrier after it (REGISTERS.md §3) are statements after the branch: a
  pattern the checker matches.
- **The proof.** A `Spec` statement of the rule, and its soundness proof. The rule is about positions in the tree, as
  I3's distinctness is, so it would reuse `Spec.statements` and `Fold.blockFusion`.

## 4. The evaluator

**Where: in Raccoon** (§9, decision 3).
- **Why.** The evaluator is then the formal semantics of generated code. Tests, the hardware battery and proofs all talk
  about one definition. A typical proof states that a kernel's result equals a simple single-threaded function.
- **Input.** It reads a kernel's AST directly, a `Cuda.Kernel` value, and a launch: grid, parameters and buffers.
- **The risk is speed.** The smallest meaningful attention test is roughly 10⁷–10⁸ evaluation steps: a few CTAs of
  384–512 threads, thousands of statements per thread per key block, and about 4M multiply-adds per S product. The
  interpreter takes about 30 s to *generate* such a kernel. So §8 starts with a measurement.
- **The scalar domain is a parameter.**
  - Concrete f32 and bf16 run the tests and the battery.
  - An exact, abstract ring serves the proofs: "the kernel computes this algebraic expression" is then an equality.
    Floating-point error is a separate question with bounds; online softmax and the tensor cores' accumulation order
    make a kernel's bits differ from a naive reference's.
- **Floating point, for now:** f32 and bf16 operations are trusted builtins under the prelude's obligations, and the
  battery (§5) checks them against the hardware bit for bit.
- **Floating point, on the horizon:** a precise model of the floating-point semantics and the hardware, in Raccoon.
  The builtins then become an optimization of that model.
- **Proofs over every schedule** split in two:
  - the library's adequacy argument: a well-typed client's kernel is race-free, so its result does not depend on the
    schedule;
  - reasoning about a single, deterministic schedule.

  Proof by evaluation covers concrete inputs only; proofs for all inputs go by induction over the evaluator.

**State:**
- global buffers, typed, with their extents;
- each CTA's shared memory;
- each CTA's tensor memory, as lanes × columns of 32 bits, with its allocation;
- each barrier: phase, pending arrivals, transaction count;
- named barriers and cluster barriers;
- each thread's bulk async-groups;
- each thread's registers;
- each SM's register pool for `setmaxnreg`;
- CTA pairs.

**Execution.**
- **Warps.** A warp is the unit. A step runs one statement of one warp, its lanes in lockstep under an active mask, so
  divergence and `.aligned` instructions are explicit.
- **Scheduling.** A scheduler chooses the next warp:
  - round-robin;
  - random from a seed;
  - exhaustively at barrier points, for small configurations.
- **Asynchronous operations** (TMA copies, MMAs, commits) are queued events that complete at a time the scheduler
  chooses. This is how `MODELS.md` already describes them: issue, then a later completion step.

**Checks, on every run:**
- **Bounds:** global and shared memory; tensor memory outside an allocation.
- **Races:** happens-before from vector clocks, across thread barriers, barrier phases and commits. Two accesses to one
  element, at least one a write, with neither before the other.
- **Deadlock:** no runnable warp and no pending event.
- **Barrier misuse:**
  - a count mismatch;
  - one phase completed by arrivals meant for different phases;
  - an `.aligned` instruction under a partial mask.
- **Exit:**
  - a CTA exits with a bulk async-group pending, tensor memory allocated, or a peer's access to its memory still
    possible;
  - a barrier is invalidated while arrivals are in flight.

**Numerics:**
- **Bit-exact where PTX states the result:** integers, conversions, IEEE `add`/`mul`/`fma` with a stated rounding,
  `rcp.rn`, `cvt.rn`, and bf16 stores.
- **Bounded where it does not:**
  - `ex2.approx` and `lg2.approx`: a reference value within the documented error.
  - Tensor-core MMA: f32 accumulation in a fixed order. Probe H5 measured that the hardware's accumulation differs
    from sequential f32 within a bound, so the comparison is against that bound.

**Not modelled:**
- `ptxas`: registers, spills, instruction scheduling;
- time and performance;
- the hardware's actual schedule. The evaluator explores schedules; it does not predict them.

## 5. Held to the hardware

**A differential battery.**
- **What runs.** Small kernels per instruction family, built from the core's own emitters, run on the GPU and in the
  evaluator from the same inputs.
- **How outputs compare.** Bit for bit for the exact subset (§4), and within the documented bounds for the rest.
- **Coverage.** Every assumption of `OBLIGATIONS.md` §3 gets at least one test. Probes H1–H5 become battery tests.
- **When.** `gpu/encoding/harness/hw.sh` runs the battery in every hardware session.

**A disagreement** is either a bug in the evaluator or an assumption that does not hold. Either is worth knowing.

**FMA contraction.** By default `nvcc` contracts `a·b + c` into one FMA, which changes last bits. The library already
has an explicit `Expr.fma`. The question is whether kernels compile with `-fmad=false`, or the printer pins every
product and sum (§9).

## 6. What it would have caught

| Defect | Caught? | By |
|---|---|---|
| The append's columns | yes | the race check: lanes 16–31 of warp (b, h) write warp (b, h+1)'s elements. The last head writes the next row |
| The bf16 comparison | yes | bf16 stores round to nearest even, so the harness fails as it did on hardware |
| The `setmaxnreg` deadlock | likely | the register pool, plus a random schedule in which the correction warpgroup finishes first |
| 184 registers | no; `gpu/encoding/REGISTERS.md` catches it | `ptxas` is not modelled here. Register budgets and a spill check after `ptxas` are their own design |
| A3a's rows from the warp number | yes | a cross-CTA write-write race |
| P2's recomputed page | only with a test that writes the table during the launch | the race check |
| `onLeader`'s skipped store wait | yes | the exit check: the peer exits with a bulk group pending |
| The register channel out of `onLeader` | yes | the deadlock check |

So it would replace the hostile reviews' slowest job, tracing generated code by hand, and leave the reviews the
argument.

## 7. Relation to proving the library correct

- `MODELS.md` describes the hardware as transition systems on paper. The evaluator makes them executable, and the
  battery tests them against the hardware.
- `Spec.rac` states structural invariants only. The adequacy theorem the later proof work needs, that a well-typed
  client's kernel is race-free and its protocols complete, is stated against a semantics. The evaluator's is the
  candidate, written once more in Raccoon, or as close to it as the Raccoon statement can be kept.
- Each A-assumption becomes a test that can fail.

## 8. Plan and cost

1. **Typed instructions.** Built (§3). Every example generates byte-identical CUDA, and `Check.rac` keeps its
   proofs.
2. **A performance spike.** Execute the smallest TinyGEMM (one tile) from its checked `Cuda.Kernel` AST in Raccoon,
   first in the exact-ring domain, and report retired warp steps and scalar work with measured timings. The completed
   exact-ring tile takes about 19.8 s in the native driver and recommends interpreter performance work
   (`gpu/ROADMAP.md` C1) before expanding evaluator v0. Profiles now give JVM sampled-work guidance, while the native
   JFR profile is only a polling-site distribution; neither justifies converting a sampled share into native seconds
   saved. A matched source-level ring-helper fusion A/B tested one narrow candidate but showed no reliable speedup.
3. **Evaluator v0, in Raccoon.**
   - **Content:**
     - the exact numerics subset;
     - sequentially consistent memory with the happens-before race check;
     - asynchronous events;
     - the three schedulers.
   - **Use:** every harness runs against it at small sizes, in place of the hand-written mocks.
   - **Size:** the largest step, a few thousand lines. Most of it is the TMA box and swizzle layouts, the
     shared-memory descriptors, the tensor-memory layouts (M = 128 and M = 256, a pair's halves) and the MMA operand
     forms.
4. **The battery** in `hw.sh`. It also checks the floating-point builtins.
5. **Weak memory and the proxies.** `MODELS.md`'s ordering rules O1–O6 become checks: a read counts as ordered only
   through the fence and barrier chain those rules name. This is where the evaluator says most that hardware runs
   cannot, because a missing fence often works on hardware.
6. **Proofs against the evaluator.**
   - First, functional correctness over the exact domain, on one schedule.
   - Then the library's adequacy argument (`docs/proposals/SAFETY_PROBLEMS.md` §1).
7. **On the horizon:** a precise model of floating point and the hardware, in Raccoon.
8. **Only if speed stalls:** a fast twin in Scala or C++, differentially tested against the Raccoon evaluator on small
   cases. The Raccoon evaluator stays the reference.

### TinyGEMM spike: one generated tile in the exact-ring domain (2026-10-02)

**Status: the bounded spike is complete; its result recommends C1 performance work before evaluator v0.** This is a
bounded execution experiment, not evaluator v0 and not a hardware-equivalence claim. It runs the generated `Tiny.kernel` AST
after `Core.checkedKernel` supplies its existing `WellFormed` evidence. The kernel and the `prepare`, `run`, and
extraction closures are created in one checked module environment so nominal `Cuda` families stay identical. The
preparation path validates the actual launcher parameters, tensor-map declarations, launch requirements and evaluated
dimensions; unsupported shapes or map encodings are rejected instead of being inferred from parameter names.

The supported launch is exactly one CTA for `M = N = 128`, `K = 64`: 256 threads in eight 32-lane warps. Its Raccoon
inputs are deterministic, coordinate-dependent elements of `Z/257`. The ring domain makes every product and sum exact;
the BF16 input maps and F32 output map determine element widths, swizzled addresses and descriptor checks, not floating-
point values. Loading/checking the module, constructing the AST, preparing each seed's inputs, extracting results and
the independent indexed reference calculation all happen outside the timed `run` invocation. Each run constructs fresh
shared, tensor and output storage. The host oracle computes all 16,384 results by ordinary indexed matrix
multiplication in `Z/257`; it does not interpret or replace the generated kernel.

`WarpMachine` interprets the actual AST's reached expression and statement subset. Each warp carries 32-lane register
vectors, initialization masks, an active mask, and nested branch/loop frames. Branches split and later reconverge lane
masks; the `for` stop is the AST's exclusive bound. Unknown expressions or instructions fail explicitly. The scheduler
is one deterministic round-robin warp order. TMA and tensor-core requests capture evaluated operands in a FIFO event
queue; queued work is completed in order when no warp can retire another statement. A successful AST statement
retirement increments `warpSteps`; blocked waits do not. Event completions and ring-scalar operations have separate
counters. The source assigns warp 0 to the producer, warp 1 to the MMA issuer, warps 2 and 3 to idle roles, and warps 4–7
to the epilogue. Fuel bounds execution and a stalled machine reports deadlock.

The data layer consumes only evaluated requests and owns no kernel traversal or scheduling. It resolves input/output
maps against the checked launcher's actual `MapEncoding`s and bounds every byte access by the declared dynamic shared
extent. It models the two 64-by-128 BF16 TMA input boxes, the four-stage shared ring, its encoded shared-memory
descriptors, and the generated 128-byte swizzle when reading operands. The four emitted `tcgen05.mma` instructions are
executed separately: each uses its own descriptor-selected 16-wide K slice, accumulator address, shape and accumulate
flag. There is no fused K=64 host shortcut. Each instruction performs 128×128×16 ring multiplies and additions, for
exact totals of 1,048,576 multiplications and 1,048,576 additions across the four instructions. The epilogue uses the
actual tensor-memory address and issuing warpgroup quadrant; each 32-column chunk and warp issues four `.x8` loads at
column offsets 0, 8, 16 and 24, then writes its addressed 32×32 F32 staging tile with TMA. Output coverage checks
reject overlaps and omissions before the host extracts the final matrix.

The expected successful-run counters are four MMA instructions, 64 tensor-memory loads, 16 TMA stores, and 88 queued
event completions (two input TMA loads, four MMAs, two commits, 64 tensor-memory loads and 16 stores). TMA transfers
account for 32,768 input bytes plus 65,536 output bytes. The scalar counters are 1,048,576 multiplications and the same
number of additions. Each run retires 1,251 AST statements. At the native median this is about 63.2 retired statements
per second; the 2,097,152 ring operations are measured separately, not expanded into synthetic warp steps.

The control layer tracks nine mbarrier locations used by this kernel (four ring-full, four ring-empty and one
accumulator handoff), plus the emitted named/CTA barriers. Arrival and expected transaction-byte completion advance a
barrier phase; waits observe the completed phase without consuming it, so multiple epilogue warps can wait on the same
handoff. TMA arrivals and tensor-core commit events retain the barrier phase captured at issue. Tensor-memory load
results remain deferred until a successful full-warp `tcgen05.wait::ld`. The reached aligned operations enforce their
required full-warp masks, while per-thread side-effect operations are accepted only for one active lane.
`setMaxNReg` is rejected as unsupported because this spike does not model the SM register pool.

Focused source fixtures mutate the generated AST rather than substituting a GEMM body. They include a valid descriptor
mutation that repeats one K slice and must complete with a matrix different from the independent oracle, alongside
invalid descriptors and output offsets, out-of-bounds shared storage, partial aligned/load-wait masks, unsupported
instructions (including `setMaxNReg` register-pool behavior), missing TMA bytes, missing bulk commit, fuel exhaustion
and non-quiescent exit. The host run compares two asymmetric input seeds against the oracle. Integrated validation
passed all 964 tests, including those cases.

Source checking initially exhausted a 2 GiB JVM heap while repeatedly traversing shared environment/value DAGs. An
invocation-local materialization memo and visited-node reference traversal were added to avoid repeating that work. The
earlier failing check and the current clean Tiny API source check are from different source snapshots, so they do not
establish a source-check speedup. In the final native driver run, API loading and checking took 11.551 s before timing; this setup and input preparation,
output extraction and oracle checking are outside the timed `run` invocation.

**Validation:** `sbt scalafmtAll` passed and reformatted three Scala sources. The final post-register-pool-fix
`sbt validate` passed all 964 tests, including the `unsupported-regpool` mutation, which requires `setMaxNReg` to fail
explicitly. The TinyGEMM two-seed/reuse test took 56.702 s and the mutation suite took 20.992 s. Logs are preserved at
`target/performance/tinygemm-spike/scalafmt.log` and `target/performance/tinygemm-spike/validate-regpool-fix.log`.

**Limits of this spike.** This is an exact-ring model for the reached one-CTA TinyGEMM shape only. Its memory/events are
sequentially consistent and FIFO; there is no race detector, vector-clock happens-before relation, alternate or
exhaustive schedule, or weak-memory model. `fenceMbarInit`, `fenceProxyAsync` and `tcFence` are ordering no-ops in this
abstraction, so absent or moved fence mutations are not detected. `tcgen05.relinquish` checks full-warp participation
without modeling permit bookkeeping, and `setMaxNReg` fails explicitly because register-pool effects are unsupported.
`bulkWait.read` conservatively
waits for full TMA-store event completion; it does not separate read-complete from store-complete or model general bulk
groups. Floating-point/BF16 rounding, hardware MMA behavior, TMA outside the validated maps/shape, other kernels,
clusters, and general CUDA are not covered. This spike does not establish the planned 10⁷ warp-step target or complete
the differential GPU battery.

**Preliminary JVM result:** the first bounded end-to-end run completed for both asymmetric seeds and matched all 16,384
outputs per seed to the independent host oracle. Each run retired 1,251 warp statements and reported the expected 88
event completions, 98,304 TMA bytes, 1,048,576 scalar multiplies and adds, four MMAs, 64 tensor-memory loads and 16 TMA
stores. These are one-sample JVM timings with no warmup; source API load/check took 8.700 s outside the timed
invocations. Input preparation, output extraction and oracle validation are also outside the timer. The raw run is
`target/performance/tinygemm-spike/tiny-jvm-one-sample-3.log`.

| Seed | Timed `run` invocation | Retired warp steps/s |
|---:|---:|---:|
| 17 | 10.815150292 s | 115.67 |
| 83 | 10.801340000 s | 115.82 |

The step rate counts successfully retired warp statements only; scalar MMA work is reported separately and is not
expanded into synthetic warp steps.

The JVM samples above are preliminary and are not a controlled JVM-versus-native comparison: they use one sample per
seed without warmup, while the native run below uses one warmup and three samples.

**Final native result:** the post-register-pool-fix executable completed one warmup and three timed samples for each
seed. All eight invocations matched all 16,384 outputs to the independent exact-ring oracle, with complete coverage and the expected
1,251 warp statements, 88 event completions, 98,304 TMA bytes, 1,048,576 multiplies and additions, four MMAs, 64
tensor-memory loads and 16 stores. The timed region is only `Interpreter.evalApply(run, prepared)`; source API
load/check, input preparation, output materialization and oracle validation are outside it.

| Seed | Three timed samples (s) | Median (s) | Retired statements/s | Scalar ring ops/s |
|---:|---|---:|---:|---:|
| 17 | 19.775651416, 19.928258375, 19.774071792 | 19.775651416 | 63.26 | 106,047.18 |
| 83 | 19.745183875, 19.956359708, 19.801870834 | 19.801870834 | 63.18 | 105,906.76 |

The final API load/check took 11.551 s before timing. The benchmark process took 175.74 s wall, 174.49 s user CPU plus 0.84 s system CPU, with
652,509,184 bytes maximum resident set and 640,534,592 bytes peak footprint. These process figures include startup,
module load/check, warmup, all timed calls and untimed validation; they are not per-invocation memory measurements.

The measured code/test snapshot is parent `617c4c8bab2ef39053f5d121f51e4acfef71993a` plus the files identified by
SHA-256 fingerprint `6fd62c1e64c6d30a9fa764d7100ee0b50112129b8241982b91a03898462cbb9b`. Its file/path manifests are
`target/performance/tinygemm-spike/fingerprint-code-test-final-files.sha256` and
`target/performance/tinygemm-spike/fingerprint-code-test-final-paths.txt`. The tested executable
`target/performance/tinygemm-spike/raccoon-tinygemm-spike-regpool-fix` has SHA-256
`aff445682ee3ba34b7d9d82021e380cf04c6230426f67b387c33933432befbb0`. The raw benchmark and build logs are
`target/performance/tinygemm-spike/tiny-native-regpool-fix-default.log` and
`target/performance/tinygemm-spike/native-build-regpool-fix.log`. The final native artifact integrity manifest is
`target/performance/tinygemm-spike/native-artifact-hashes-regpool-fix.sha256` (SHA-256
`fef79366b68b52fe33fd3d94d94c11d451a9cc323c2c1d429b877cc756a07a48`); the pre-fix binary and logs are preserved
separately in `target/performance/tinygemm-spike/native-artifacts-pre-regpool.sha256` (SHA-256
`7a50ce97efd08cac0e01632ff0472713c7f2157bf99f3d681a169b1fdc139e54`).

The executable was built with the default optimized native settings: GraalVM Native Image Oracle GraalVM 21.0.12+7.1
and Java 21.0.12+7-LTS, macOS arm64 (`armv8-a`), Apple clang 17.0.0, O2, Serial GC, four image threads, a 3 GiB
image-build heap, and default assertions (no assertion-suppression flags). Reproduce the build and benchmark with:

```sh
MAIN_CLASS=com.raccoonlang.TinyGemmSpikeBenchmark OUTPUT_DIR=target/performance/tinygemm-spike \
  OUTPUT_NAME=raccoon-tinygemm-spike-regpool-fix \
  scripts/build-graal-native.sh --parallelism=4 -J-Xmx3g
target/performance/tinygemm-spike/raccoon-tinygemm-spike-regpool-fix --warmups 1 --samples 3
```

The actual tile takes about 19.8 s in the native driver while performing 2,097,152 exact-ring scalar operations and
retiring 1,251 warp statements. This supports prioritizing interpreter performance work (C1) before expanding
evaluator v0. The profile follow-up below narrows likely interpreter costs but does not predict savings from a broad
redesign. Do not extrapolate this MMA-heavy tile rate to attention or the proposed 10⁷-step target.

### Profile follow-up: interpreter attribution (2026-10-02)

These profiles use the same checked one-CTA `M=N=128, K=64` exact-ring kernel and seeds as the bounded spike above.
They sample one timed `run(prepared)` evaluation per seed after two warmups. Recording setup/control, module setup,
input preparation, output extraction and the independent oracle are outside the reported invocation; JFR sampling
overhead occurs during the timed evaluation. The timed call includes construction of its one-element argument vector.
The profiles confirm that generic interpreter and environment work deserves attention, but they do not provide a
component-level speedup estimate.

| JVM attribution group | Seed 17 | Seed 83 | Rough budget after normalizing to unprofiled JVM median |
|---|---:|---:|---:|
| Disjoint direct leaves: `Env.bindRuntimeLocals`, `Env.containsLocal`, `Env.runtimeValueOrNull` | 136/611 (22.26%) | 149/659 (22.61%) | 2.447 s / 2.487 s |
| Disjoint direct leaves: `Value.canonicalizeProof`, `Env.assertCanonicalProof` | 62/611 (10.15%) | 55/659 (8.35%) | 1.115 s / 0.918 s |
| Inclusive unique-method union: argument/type reconstruction (`Interpreter.residualArguments`, `VPi.constructorResultType`, `Projection.project`) | 178/611 (29.13%) | 197/659 (29.89%) | 3.202 s / 3.288 s |
| Inclusive unique-method union: binding/proof checks (`Env` leaves above plus proof canonicalization/assertion) | 242/611 (39.61%) | 243/659 (36.87%) | 4.354 s / 4.055 s |

The JVM profiles contain 611 and 659 evaluator-thread CPU samples over 10.262 s and 10.230 s recordings. The first
two rows are disjoint leaf samples; the latter rows count a method at most once per stack and overlap with each other
and with the leaf rows. The rough seconds multiply each share by the corresponding unprofiled JVM medians (10.993 s
and 10.998 s); they are sampled-work budgets, not realizable savings or hard ceilings for a whole-method refactor.
About 81% of stacks reach the 64-frame limit, which censors deeper inclusive callers. Weighted JVM allocation
sampling estimates 30.31 GB and 30.18 GB allocated during the two recorded evaluations. The largest sampled sites
include `Env.bindRuntimeLocals` (6.58/4.02 GB), `Vector.iterator` (3.23/3.21 GB),
`BinderOps.instantiateFullRuntime` (2.65/2.94 GB), and `Interpreter.residualArguments` (2.35/3.26 GB). These are
sampling estimates, not retained memory. Top-level JVM GC pauses total 313 ms and 285 ms in the two recordings.

Native attribution is different and must not be compared numerically with the JVM leaf table. Every raw evaluator
sample shares the same leading nine frames; its first frame is `RecurringCallbackTimer.invokeCallback` inside a
recurring-callback/safepoint envelope. The corrected analyzer removes the verified eight-frame prefix and its one
verified terminal safepoint frame (nine frames total); generated SVM frames after it remain visible. Beneath that prefix,
`Env.bindRuntimeLocals` is the first application frame in 85.25% and 84.74% of evaluator-thread samples, while
`ValueKey.packed` is first in 4.82% and 5.20%. This is a polling-site distribution,
not exclusive time inside those methods: do not multiply 85% by native wall time or compare it with JVM leaf shares.
The native recordings contain 2,115 and 2,116 evaluator samples over 20.519 s and 20.600 s; around 81% of their
stacks also reach the 64-frame limit. The JFR-enabled timed samples were 20.537 s and 20.614 s, versus JFR-disabled
single-run calibrations of 19.759 s and 19.752 s, an observed difference of about 0.78 s and 0.86 s (roughly 4%).
The calibration and profile runs used different warmup counts, so this is not an isolated causal estimate of JFR
overhead. Native JFR produced no weighted allocation samples. Its top-level GC pause records sum to 1.131 s and
1.111 s; all 664 and 839 distinct GC ids match, with 7 and 8 extra pause records sharing those ids and no unmatched
records. The native async sample is unsymbolized and provides no independent Java-method attribution.

The first source-level A/B candidate was a narrow test of `TinyDevice.dotRows`: each actual K16 MMA executes
16,384 outputs × 16 scalar iterations, and the four emitted MMAs total 1,048,576 ring multiply-add iterations.
Replacing the two `Ring.mul`/`Ring.add` applications and their nested normalization with the equivalent single
`Nat.mod(Nat.add(acc, Nat.mul(a, b)), 257)` expression would remove two Raccoon helper applications and one
`Nat.mod` application per scalar iteration while preserving exact `Nat.mul`/`Nat.add` behavior and the measured
scalar counters. The matched native comparison below did not establish a reliable speedup; the source-call reduction
does not imply that the entire Env sampled budget is attributable to those helpers.

The JVM samples give three more specific, overlapping opportunities to test, not savings forecasts. Compiling checked
runtime local references to frame/slot addresses and reducing activation-binding metadata targets the roughly 2.45–2.49 s
direct Env-leaf budget; it must preserve lexical captures, lifetime scope, and proof checks. Specializing cached closed
implicit projections and constructor-result types by checked owner/type parameters targets the 3.20–3.29 s inclusive
argument/type reconstruction union; cache keys and invalidation must preserve unresolved metavariables, refinement
dependencies, nominal owner identity and materialized-environment semantics. A fast canonical-proof classification
for validated non-propositional packed data targets
the 0.92–1.12 s direct proof-leaf budget, while retaining canonicalization assertions and every proof,
unresolved-metavariable and evidence case. One narrow proof-path candidate is to let `canonicalizeProof` rely on the checked immutable
`VPacked` construction invariant: its private constructor already requires `tpe.synDeps.isEmpty` and a
non-propositional type, although `canonicalizeProof` currently rechecks the proposition classification. Any fast
return must keep binding assertions and all proof, unresolved-metavariable and evidence handling intact; the sampled
proof group includes other value shapes,
so it cannot be credited wholesale to `VPacked`. These rough JVM budgets overlap, include callees and sampling noise,
and are not hard ceilings or expected gains. The native first-visible `ValueKey.packed` share suggests separately
testing packed-key cost without weakening canonical keys. Source inspection also finds 16,384 output-cell stores,
each performing two persistent
`Memory.set` updates. At depth 14, that is about 458,752 copied tree branches plus leaves. The final
`allOutputCellsValid` pass makes 32,768
indexed gets; a paired traversal could visit about 65,534 nodes in the two complete trees rather than roughly 491,520
lookup nodes. These are source-structure counts, not measured time budgets. Batching or tree traversal might reduce
structural work, but there is no timing attribution for either path. Any batching must retain per-cell bounds,
coverage, overlap, value and layout checks. These candidates follow from source structure and profile guidance only;
each needs its own exact-output A/B before it can support a performance claim.

The candidate and restored source fingerprints, full timing samples, sampler-overlap exclusion, and restoration check
are documented in `native-fusion-ablation-protocol.md` (SHA-256
`7dc205f7a87b292757e68338ae8d0acba92bbc48520eb25413351565d5e42952`); the source fingerprints are also recorded in
`profile-source-fingerprints.txt` (SHA-256
`280bac0003c1ed21b26f667ba4bfa01451db63c1fe9ed6c52ff5bc566c0cae06`). The checksum-verified profile artifact
manifest includes both files.

The raw recordings, analyzer outputs, settings and baseline binary are preserved in
`target/performance/tinygemm-profile/`. The kernel/interpreter source is baseline commit
`b2c6e742883b8128d9c2b8da01de066885d40f40`; the profiling-only host harness adds JFR recording controls outside the
timed call. The native profile executable was built on macOS arm64 (`armv8-a`) with GraalVM Native Image 21.0.12+7.1,
O2, default ML-inferred PGO, Serial GC, four image workers, a 3 GiB image heap and `--enable-monitoring=jfr`. JFR settings are in
`profile.jfc`: Java execution samples are configured at 10 ms, native method samples at 20 ms, and allocation
sampling at the medium setting. Attribution summaries are `jvm-profile-attribution.txt` and
`native-profile-attribution-corrected.txt`; the latter supersedes the earlier `native-profile-attribution.txt`.
JFR reported no data loss; the native recordings had no weighted object allocation samples.

The profile provenance hashes are:

| Artifact | SHA-256 |
|---|---|
| `TinyGemmSpikeBenchmark.scala` profile harness | `ee79e28fe4c3425f109c58b3c5f441b93eb3f4ea49e2e0bef84b30aab2852988` |
| `raccoon-tinygemm-jfr` native executable | `876b1be1cae0960745f01a285ed28b68b8f287a26dc87faa5384da6d64657ded` |
| `profile.jfc` | `6fc5bd1ac1cde8aacd004f0a0be6a43de314e096dfc880a4582836f6fa91e64c` |
| `jvm-profile-attribution.txt` | `0a91dca699226b7d8b699f6713856567055c1801588179983421ff4c84cb3276` |
| `native-profile-attribution-corrected.txt` | `b54ade4194558ed9894765a3c11fcfff301fd93e19b9bcecc515b386daa35ce6` |
| JVM seed 17 raw recording | `d6d9ea15d75867e9fd942dcbc742e59c3488a1fe2b2eeb8cfb6ff60690f30850` |
| JVM seed 83 raw recording | `b0738395ff2c3a41b18dcd5e563288c66a4ebf4d70e46f7081bc4492b083eda6` |
| Native seed 17 raw recording | `2a1fc27ace9fc0c0328c96b48367d1c90ed8c21222f0199b5d1b34914af47776` |
| Native seed 83 raw recording | `d99d304e264ddc546ae025aa3c995ebc1d8a10fadde0987363ab8fbbb0f57d96` |
| `jvm-jfr-2warmups-1sample.log` | `7ffff317a1d56993370b6604b5eb0fa119fecb32894bcb76e17e39b74550e234` |
| `native-jfr-2warmups-1sample.log` | `44f8875ac7a71c2c7f0496a569550484880ec3cc5d841021a742e3fd77f00238` |
| `native-jfr-disabled-calibration.log` | `565d3256ba3045abccb1acbd2833e8f7acce1ff1a5f5b09316a3ceac93f8f469` |
| `native-build-jfr.log` | `2d30982179ee7cb30b59c57801b7beb9db87436f70d0825bbd17e00294ce65ac` |

The complete 36-file, checksum-verified profile artifact manifest is
`target/performance/tinygemm-profile/profile-artifacts-final.sha256` (SHA-256
`9dbcfda1f367af878e99f2b2ec9d2edc87d43261a8327e76f153d4e7d0cd5392`).

Reproduce the JVM profile and its unprofiled baseline from the repository root with:

```sh
sbt -batch -no-colors compile graalvmNativeImageClasspath
mkdir -p target/performance/tinygemm-profile/jvm-recordings target/performance/tinygemm-profile/native-recordings
cp /Library/Java/JavaVirtualMachines/graalvm-21.jdk/Contents/Home/lib/jfr/profile.jfc \
  target/performance/tinygemm-profile/profile.jfc
java -Xmx2g -ea -cp "$(cat target/graalvm/classpath.txt)" com.raccoonlang.TinyGemmSpikeBenchmark \
  --warmups 2 --samples 3
java -Xmx2g -ea -cp "$(cat target/graalvm/classpath.txt)" com.raccoonlang.TinyGemmSpikeBenchmark \
  --warmups 2 --samples 1 \
  --jfr-dir target/performance/tinygemm-profile/jvm-recordings \
  --jfr-settings target/performance/tinygemm-profile/profile.jfc
```

Rebuild and reproduce the native profile with:

```sh
MAIN_CLASS=com.raccoonlang.TinyGemmSpikeBenchmark OUTPUT_DIR=target/performance/tinygemm-profile \
  OUTPUT_NAME=raccoon-tinygemm-jfr scripts/build-graal-native.sh --parallelism=4 -J-Xmx3g \
  --enable-monitoring=jfr
target/performance/tinygemm-profile/raccoon-tinygemm-jfr --warmups 1 --samples 1
target/performance/tinygemm-profile/raccoon-tinygemm-jfr --warmups 2 --samples 1 \
  --jfr-dir target/performance/tinygemm-profile/native-recordings \
  --jfr-settings target/performance/tinygemm-profile/profile.jfc
```

The source-only candidate and restored baseline used the same native executable, JFR disabled, one warmup and three
timed samples per seed. Every invocation matched the exact-ring oracle and the expected counters. The table gives
per-seed timed invocation medians; the earlier seed 83 baseline is shown only as context because an asynchronous
sampling diagnostic may have overlapped its final sample.

| Loaded Raccoon source | Seed 17 median (s) | Seed 83 median (s) | Notes |
|---|---:|---:|---|
| Initial baseline (`TinyDevice.rac` SHA-256 `a32737aadc9e21b159031bbc3318e62284f49d78bf24eaeac0d32b796da3ff16`) | 19.611470542 | 19.802249875 | Seed 17 is clean; seed 83 is contaminated context and excluded from comparison. |
| `dotRows` fused candidate (source SHA-256 `fa96be8a80b405dbd623c362d3acb9b0df5a7e74843bd1a57a0ecd5c61311e91`) | 20.086442292 | 20.373352333 | Nominally 4.69% and 1.23% below the subsequent restored baseline. |
| Restored baseline (`TinyDevice.rac` SHA-256 `a32737aadc9e21b159031bbc3318e62284f49d78bf24eaeac0d32b796da3ff16`) | 21.074847791 | 20.628011208 | Same original source and executable as the initial baseline. |

The seed 17 restored-baseline median is 7.46% slower than its earlier clean baseline median; the candidate is 2.42%
slower than that earlier baseline despite looking 4.69% faster than the later repeat. Seed 83's candidate is only
1.23% below its clean restored repeat, and its earlier baseline value is excluded. The same-source drift is larger
than the apparent candidate benefit, so this experiment is inconclusive and does not support retaining or prioritizing
the fusion for speed. Exact outputs and counters passed for both source variants. The preserved original executable
`raccoon-tinygemm-jfr` has SHA-256
`876b1be1cae0960745f01a285ed28b68b8f287a26dc87faa5384da6d64657ded`; the candidate and restored logs are
`native-fusion-candidate-1warmup-3samples.log` (SHA-256
`3d277733450d2263c4ffe8885d8a83839fba3e5ef52621251cc9bf9dbb4aec3d`) and
`native-fusion-restored-baseline-1warmup-3samples.log` (SHA-256
`5522826df10754d65d60502aa87cb91f09b141d1722193acf041be0aa0931d36`). The initial baseline log is
`native-baseline-jfr-disabled-1warmup-3samples.log` (SHA-256
`7dd8968560919f3b6eb55b2f3c26c9a32aaedefe2c3109b50d98ba3bca727549`); its seed 83 median is not used as a clean
comparison. The candidate patch is preserved as
`tinydevice-dotrows-fusion-ablation-applicable.patch` (SHA-256
`2f923a657fd64cd4e6735e33dc583bb57e97207034f70414a43bda30adb46fd6`), and `TinyDevice.rac` was restored byte-for-
byte to the baseline source before this report update.

### Historical checkpoint: prepared execution frames for the checked TinyGEMM evaluator (2026-10-02)

An opt-in `PreparedEval.prepare` compiles a checked, data-valued Core lambda into immutable plans. The session uses
numeric local addresses and reusable value slots for parameters, recursive peers, lets and match fields. Its loop
keeps application arguments and non-tail continuations in reusable banks and reuses the current frame for tail Core
calls. All-explicit Core calls copy arguments directly between slots. Ref, application, block, match and literal nodes
use this tier; Pi, lambda creation, scope and other nodes run through the ordinary interpreter after materializing a
fresh, ordered immutable `Env` at the whole-term boundary. Escaping closures, dependent Pi values, stuck matches and
deferred evidence therefore hold no reusable slot arrays. Native applications retain their existing generic path.
Preparation is explicit and tied to the exact checked lambda and its captured context; `Interpreter.evalApply` remains
the default. `TinyGemmSpikeBenchmark --prepared-frames` switches only the timed `run(prepared)` call and still runs the
same checked Raccoon source, kernel AST, output oracle and counters.

The stage-1 checked constructor-plan commit `90d6da9` is the parent of this frame comparison. Both JVM modes used the
same compiled candidate, Oracle GraalVM 21.0.12, `java -Xmx2g -ea`, two warmups and three timed samples per seed.
They ran sequentially without concurrent heavy work. Values below are timed `run(prepared)` evaluations in seconds;
source loading, preparation and output validation were outside the timer. The samples are unpaired, so these numbers
show an observed workload win rather than a causal allocation breakdown.

| Seed | Generic samples; median | Prepared samples; median | Observed median change |
| --- | --- | --- | ---: |
| 17 | 9.588, 9.554, 9.585; **9.585** | 8.145, 7.868, 7.822; **7.868** | −17.9% |
| 83 | 9.504, 9.525, 9.409; **9.504** | 7.982, 8.088, 8.023; **8.023** | −15.6% |

Every invocation in both modes passed the exact 16,384-cell Z/257 oracle and expected counters: 1,251 warp steps,
88 asynchronous completions, 98,304 TMA bytes, 1,048,576 multiplies and adds each, four MMA instructions, 64 tensor
memory loads and 16 stores. `sbt validate` passed 976 tests, including differential checks for nested closure capture
identity and reuse, recursive and mutual calls, deferred evidence, neutral matches, dependent Pi captures and fallback.
The final additional same-thread reentry test passed in the focused 10-test frame suite.
JVM allocated bytes and native-image performance had not been measured at this checkpoint; the matched follow-up is
below. The
[generic](../target/performance/reusable-eval-frames/jvm-generic.log),
[prepared](../target/performance/reusable-eval-frames/jvm-prepared.log) and
[validation](../target/performance/reusable-eval-frames/validate.log) logs are saved in ignored `target/performance`;
their hashes and source provenance are in
[provenance](../target/performance/reusable-eval-frames/provenance.txt).

### Historical checkpoint: unboxed checked Nat intermediates in prepared frames (2026-10-02)

The prepared evaluator now carries nonnegative Nat values as `Long` or `BigInt` payloads through its reusable slots
and a local result register. The exact validated Nat type is the slot discriminator; an ordinary `Value` has no Nat
type entry. A slot caches an immutable `VPacked` on its first generic read, and escaping closures, dependent work,
matches and unsupported applications use the ordinary boxed path. Tail calls stage arguments before frame reuse.
Only `Packed.nativeOp` can issue an operation capability, attached to its exact published native lambda after the
trusted declaration has been checked. Application requires that owner identity, an enabled native operation, and
the caller's exact validated Nat layout. Small `Nat.add/sub/mul/div/mod` operands use exact Long equations; overflow
and BigInt operands use the original native path. Small `Nat.beq/ble/blt` operands return the existing validated Bool
constructors. Printed names, copied or materialized lambdas, and hand-built Pis cannot enter the specialized path.
Proof canonicalization and deferred evidence checks remain at generic binding and boxing boundaries.

The final source passed `sbt validate` (**984/984**) and the focused scalar/frame suite (**17/17**), including
overflow, BigInt, zero division/modulus, disabled native operations, nominal-context and owner guards, deferred
evidence, closure capture and tail-frame reuse. All TinyGEMM warmups and samples used the actual checked Raccoon
kernel, passed the exact 16,384-cell Z/257 oracle, and produced 1,251 retired steps, 88 completions, 98,304 TMA
bytes, 1,048,576 scalar multiplies and adds each, four MMAs, 64 tensor-memory loads and 16 stores. API checking,
preparation, extraction and oracle checks remained outside the timed invocation.

The matched JVM comparison ran final frozen scalar source against committed frame-only source with Oracle GraalVM
21.0.12, `java -Xmx2g -ea`, two warmups and three timed samples per seed, serially. Times are seconds; the small
observed differences are within the range seen across adjacent frame controls.

| Seed | Frame-only samples; median | Scalar samples; median |
| --- | --- | --- |
| 17 | 7.974, 7.850, 7.906; **7.906** | 7.847, 7.800, 7.806; **7.806** |
| 83 | 7.976, 7.892, 7.878; **7.892** | 7.844, 7.799, 7.873; **7.844** |

Three native images were built from frozen `c659977`, committed frame-only `683d2ce`, and the final scalar source
using the same Oracle GraalVM 21.0.12 command flags: `--parallelism=4 -J-Xmx3g --enable-monitoring=jfr -ea`.
The new c659 image is a matched control; the older image without explicit `-ea` remains historical evidence only.
Each native run used two warmups and three timed samples per seed, no JFR during timing, and ran alone. The frame and
scalar binaries were measured in both orders. The matched c659 control was rebuilt and run separately **after** those
two pairs; its median is repeated in the first two rows for comparison, not as an interleaved third run. Per-seed
median seconds are:

| Run order | Seed | c659 generic | Frame-only prepared | Scalar prepared | Scalar vs frame |
| --- | --- | ---: | ---: | ---: | ---: |
| Frame → scalar | 17 | 20.448 | 13.652 | 13.280 | −2.7% |
| Frame → scalar | 83 | 20.464 | 13.626 | 13.283 | −2.5% |
| Scalar → frame | 17 | — | 13.843 | 13.201 | −4.6% |
| Scalar → frame | 83 | — | 13.826 | 13.309 | −3.7% |

The combined plans, frames and scalar source is about 35% faster than the matched c659 native control on this
one-tile exact-ring workload. The isolated scalar contribution is modest but repeats in both native run orders.
Whole-process peak RSS varies in direction across orders, so these runs do not establish an RSS reduction.

Per-seed JVM JFR recordings used the same checked source, `profile.jfc` (10 ms Java sampling), two warmups and one
recorded timed sample, with the harness-reported evaluator thread IDs 40 and 53. Full 128-frame export found no
recorded truncated stacks (maximum depths 31–32) and no `jdk.DataLoss`. Weighted `ObjectAllocationSample` estimates
for the timed evaluator thread were **15.54/15.12 GB** frame-only and **10.94/10.37 GB** scalar (seeds 17/83), about
30% lower in this sampled comparison. The frame-only `Vector.tabulate` allocation leaf accounted for an estimated
4.81/5.84 GB; scalar's largest remaining allocation leaves were `Interpreter.residualArguments` (2.19/1.67 GB) and
`PreparedEval.applyApplication` (1.43/1.75 GB). Top-level GC pause durations summed to 0.130/0.126 s frame-only
and 0.102/0.099 s scalar. These are JFR estimates from separate samples, not exact allocation counters.

The scalar evaluator's **exclusive CPU leaf** samples were `PreparedEval.run` 279/220 of 660/606, proof
canonicalization 46/44, residual arguments 24/20, and an implicit projection body 24/26. **Inclusive**, overlapping
stacks contained `PreparedEval.applyApplication` 264/285, residual arguments 86/81, and the projection body 30/35;
the corresponding proof-binding `Env.assertCanonicalProof` counts were 28/30. The loop leaf includes dispatch and
inlined work, so it is not a separately saveable time budget. Projection specs were already compiled; their repeated
execution, residual argument construction and proof-binding work remain candidates for separately measured changes.
Native JFR polling samples are not converted into section-time savings forecasts.

Final [scalar JVM](../target/performance/unboxed-eval-scalars/jvm-final-frozen.log),
[scalar native](../target/performance/unboxed-eval-scalars/native-final-scalar.log),
[reverse native](../target/performance/unboxed-eval-scalars/native-reverse-scalar.log),
[matched controls](../target/performance/unboxed-eval-scalars/controls),
[validation](../target/performance/unboxed-eval-scalars/validate-final.log) and
[provenance](../target/performance/unboxed-eval-scalars/provenance.txt) are in ignored `target/performance`.
Provenance records source, test, config, binary and log hashes and the per-seed JFR paths. Instrumented, overlapping,
whole-process-JFR and preliminary representation experiments are superseded for conclusions.

### Unified default Core evaluator (2026-10-02)

`Interpreter.evalTerm`, `evalApply`, `runLam` and thunk forcing enter the single `CoreEvaluator` frame machine. Its loop
handles application order, lets, scope, matching, calls, returns and tail calls for
checked and open Core. Root references and closed nullary sort forms use the same semantic helpers without allocating
a frame. The compatibility `PreparedEval.prepare`/`Prepared.run` wrapper and the TinyGEMM `--prepared-frames` alternate
path have been removed; the benchmark now times `Interpreter.evalApply(run, Vector(prepared))`.

Plans contain only syntax and local addresses. Separate bounded thread-local caches distinguish expression and
function-body plans; a nested call obtains an isolated session, retaining at most eight idle sessions per thread.
An invocation-scoped, 1,024-entry identity memo keeps checked Core closure layout eligibility and its plan, and is
cleared on return or error. Unsupported raw metadata, binder mismatches and overlapping local references use immutable
`Env` bindings *inside this same loop*. A closure, dependent Pi, deferred equation or stuck match receives an immutable
capture, never a reusable slot bank. Native scalar operations retain their validated exact owner/type and overflow
guards. Plan construction still traverses syntax on the host stack: an extremely deep unused child in hand-built Core
can exhaust it before an earlier runtime error. Once planned, explicit arguments run left to right, supplied App
evidence syntax remains ignored, and runtime errors retain their order.

The final `sbt validate` suite passed 996/996, including explicit expected-result/error tests for raw applications,
lexical restoration, malformed binder metadata, duplicate refs, proof binding, same-thread reentry after a failure,
neutral/equation matches and deep non-tail calls. The revised `EvaluationTooDeep` tests use genuine checker/helper
recursion; non-tail Core calls now succeed on a small physical `--stack`.

The preceding prepared-frame and scalar sections are retained as historical measurements, including their old class
names, commands and source fingerprints. Current TinyGEMM timing always uses `Interpreter.evalApply(run, Vector(prepared))`.
The renamed `FrameEvaluationTests` and `ScalarEvaluationTests` assert independent values, errors, forcing counts,
capture identities and neutral shapes against the single evaluator rather than comparing it with a second mode.

The matched TinyGEMM runs used the actual checked source kernel, two warmups and three timed invocations per seed,
serially, with JFR off. Each invocation passed the full 16,384-cell Z/257 oracle and exact counts of 1,048,576
multiplies and 1,048,576 adds, plus the same warp, async, TMA and MMA counters. The timer covers the default
`Interpreter.evalApply(run, Vector(prepared))` call, including its one-element argument vector, but excludes source
loading/checking and output materialization. `source_api_load_check_ns` separately includes the source API setup.
The parent is committed `fd7308d`; its prepared mode is the former opt-in execution tier. JVM runs used Oracle
GraalVM 21.0.12, `-Xmx2g -ea`, and the same TinyGEMM source fixture on each revision. Seconds below are medians of
three samples.

| JVM mode | Seed 17 | Seed 83 | Source load/check |
| --- | ---: | ---: | ---: |
| Parent default | 9.552 | 9.518 | 8.786 |
| Parent prepared | 7.946 | 7.746 | 8.829 |
| Unified default | **8.512** | **8.572** | 9.743 |

The unified default is 10.9% and 9.9% faster than the former default, but 7.1% and 10.7% slower than the former
prepared mode on these two JVM seeds. Its source setup is about 10.9% slower than parent default in these separate
processes; unification did not remove preparation cost from checking. An ordinary `Main` render of
`gpu/encoding/examples/attention_pingpong.rac` with `--json` used five separate JVM processes per revision (two
warmups, three samples): parent median 7.551 s, unified median 7.941 s, a 5.2% regression. Every JSON run printed
exactly `[]`. A separate `--raw` invocation produced **identical** 696,817-byte CUDA output in both revisions,
SHA-256 `c7799ca4d1ac07a8190a78d829b12d205f4fc013cf3547bff4f48b6df7feeb0a`.

Native images used the same GraalVM 21.0.12 builder command, `--parallelism=4 -J-Xmx3g --enable-monitoring=jfr -ea`;
the build reported O2, armv8-a, ML-inferred PGO and Serial GC. JFR was disabled during timing. The parent binary is
SHA-256 `b482f8294502731f57e2df6cce3f0d39642fe51194646e5b60c0f5d293e19eee`; the frozen unified binary is
`d6da1d2c47b45d5391f5a957d614e06a649e7eb4834cc52f573cf122a64f8236`. Native source load/check was
11.707 s for parent default, 12.676 s for parent prepared and 11.313 s for unified default.

| Native mode | Seed 17 | Seed 83 |
| --- | ---: | ---: |
| Parent default | 17.492 | 17.549 |
| Parent prepared | 13.518 | 13.567 |
| Unified default | **13.105** | **12.926** |

The unified native default is 25.1% and 26.3% faster than the parent default. It was slightly faster than parent
prepared in this one serial comparison (3.1% and 4.7%); those small differences should be treated as comparable
performance without a reverse-order control. The earlier unified image measured 12.872/12.847 s before a raw-arity
error-order fix and is retained only as diagnostic evidence. No RSS or allocation reduction is claimed for this
unification.

The original attention rendering command was also measured as a **whole-process native Main** run, not as a TinyGEMM
`evalApply` invocation. Both `Main` images used those same GraalVM build flags and the original
`--prelude gpu/Prelude.rac --root gpu --raw gpu/encoding/examples/attention_pingpong.rac` arguments. Standard output
was captured and checked on every invocation; each of the five runs per revision exited successfully with empty
stderr and the identical 696,817-byte CUDA digest above. Two warmups preceded three timed runs, JFR off:

| Native `Main --raw` | Three whole-process wall samples | Median |
| --- | --- | ---: |
| Parent default | 8.352, 8.411, 8.389 s | 8.389 s |
| Unified default | 7.415, 7.377, 7.348 s | **7.377 s** |

The unified native render is 12.1% faster in this matched run, while the JVM `Main --json` comparison above was 5.2%
slower. The parent native Main image SHA-256 is
`061663517e53bd2932e3820d2c7144a546a9b204333204b62d77cd8929bb00a5`; the unified Main image is
`3bc82555eb9b048698772f75b5d19d661fef679e2cd958c656e7715f911444a5`.

The exact commands, source/test diff fingerprint, per-sample logs, output hashes, image/build hashes and validation
hash are recorded in [unified evaluator provenance](../target/performance/unified-evaluator/provenance.txt). The
[JVM default](../target/performance/unified-evaluator/candidate-jvm-default-final-warm2-sample3.log),
[native default](../target/performance/unified-evaluator/candidate-native-default-final-warm2-sample3.log),
[attention JSON](../target/performance/unified-evaluator/candidate-attention-default-final-warm2-sample3.json) and
[attention CUDA](../target/performance/unified-evaluator/candidate-attention-final-raw.cu) artifacts are preserved
beside their parent controls in ignored `target/performance`. The
[native Main whole-process samples](../target/performance/unified-evaluator/candidate-native-main-attention-raw-warm2-sample3.json)
and its [parent control](../target/performance/unified-evaluator/parent-fd7308d-native-main-attention-raw-warm2-sample3.json)
are kept there too.

### Historical checkpoint: source-level buffer workload (2026-10-02)

This checkpoint measures foundation buffer-operation throughput; it is not a TinyGEMM evaluator. The TinyGEMM
definitions now live in the body-free `gpu/encoding/TinyGemm.rac`; the existing `gpu/encoding/examples/tinygemm.rac`
remains a render wrapper.
`Core.checkedKernel` exposes the immutable kernel AST only with the existing `WellFormed` proof. A Scala setup driver
loads and checks `gpu/evaluator/TinyKernel.rac` once, then separately loads and checks the source workload closure.

`gpu/evaluator/Ring.rac` provides exact arithmetic in Z/257, and `gpu/evaluator/Memory.rac` provides persistent,
power-of-two random-access memory. The bounded workload allocates 16,384 Nat cells and performs two writes and one read
at nonuniform indices per iteration, advancing its iteration index and updating a checksum. This counts buffer
operations, not warp steps.
The host times only `Interpreter.evalApply` inside `Execution.onStack`; loading, checking, Tiny AST construction, and the
independent result check are outside the timed interval. The source fixture is run by normal `sbt validate` through
`GpuEvaluatorSpikeTests`.

The saved render outputs from the archived parent source and the extracted-module wrapper matched byte for byte:
21,728 bytes, SHA-256 `7dc6a52123c1a5b8bc1145fcc7083c61a792a3a13b1a2e441d28a31e2bccefa0`. The Scala test pins this
digest and checks that the accessor returns a five-field `Cuda.Kernel.mk` value at family `Cuda.Kernel`.

A small opt-in native driver can be built and run from the repository root:

```sh
MAIN_CLASS=com.raccoonlang.EvaluatorSpikeBenchmark OUTPUT_DIR=target/performance/evaluator-spike \
  OUTPUT_NAME=raccoon-evaluator-spike \
  scripts/build-graal-native.sh --parallelism=4 -J-Xmx3g
target/performance/evaluator-spike/raccoon-evaluator-spike --iterations 128 --warmups 1 --samples 3
target/performance/evaluator-spike/raccoon-evaluator-spike --iterations 1024 --warmups 1 --samples 3
target/performance/evaluator-spike/raccoon-evaluator-spike --iterations 16384 --warmups 1 --samples 3
```

The custom binary was built with GraalVM 21.0.12 for arm64, O2, Serial GC, `--parallelism=4 -J-Xmx3g`, with default
assertion settings. Its SHA-256 is `6b1611a64a35ce02c9147d219595197c33de0779454a4e193c3c35ec26f6729d`. The measured source
snapshot is parent commit `899c15d4edb4ad5ff69a7c5d44f90d3e891ded70` plus the uncommitted code/test files identified by
fingerprint `e6a9bccd6a97f64d9c7441a0582ee080077ca475fc8c21a6616545b11ac2f74a`. The parent binary used for the exact
Tiny comparison has SHA-256 `b103ede6429e5f8d481c88111dd800d7ab420db72e3eec42601d342d466de39e`.

Each run used one warmup and three timed samples. The timer covers only `Interpreter.evalApply`; the displayed setup
times are outside it. Per invocation, each loop iteration performs exactly three memory API operations: two `set`s and
one `get`. Results are buffer operations per second, not evaluator steps or warp steps.

| Iterations | Buffer ops | Timed samples (ms) | Median (ms) | Buffer ops/s | Checksum |
|---:|---:|---|---:|---:|---:|
| 128 | 384 | 23.400, 23.239, 22.322 | 23.239 | 16,523.68 | 1 |
| 1,024 | 3,072 | 191.225, 189.491, 187.025 | 189.491 | 16,211.86 | 213 |
| 16,384 | 49,152 | 3,018.209, 3,013.243, 3,021.153 | 3,018.209 | 16,285.15 | 241 |

Across fresh driver processes, Tiny AST entry load/check (including the first prelude forcing) took 581.600, 577.517,
and 572.669 ms; the benchmark entry load/check then took 4.389, 4.338, and 4.355 ms. Their respective medians were
577.517 ms and 4.355 ms. All result checks matched an independent, untimed host checksum oracle.

At this historical checkpoint, the workload and driver did not model generated CUDA instructions, warps,
synchronization, asynchronous events, or floating-point operations. It had no 10⁷-warp-step result and no completed
TinyGEMM claim; the full instruction/event evaluator and step-2 decision were still pending at that time. `sbt validate`
passed 955 tests, including the source foundation fixture; the focused spike suite passed all 3 tests, and independent
source/test review was clean. Native build logs,
sample logs, comparison bytes and provenance are preserved under `target/performance/evaluator-spike/` and adjacent
`target/performance/evaluator-spike-*` files (ignored by Git).

## 9. Decisions

1. **Build it, staged as §8**, rather than more hand-written mocks. *Proposed; for the user.*
2. **Typed instructions first.** They pay for themselves without the evaluator. `Stmt.asm` went with `Gpu.rac`.
3. **The evaluator is written in Raccoon** (the user, 2026-10-01). It is the semantics that proofs are stated against.
   Speed is the risk, measured first (§8 step 2). A fast twin is a fallback, never the reference.
4. **Bit-exact only where PTX states the result**, and within documented bounds elsewhere, rather than a claim of
   bit-identity everywhere.
5. **The evaluator replaces the hand-written mocks** for validating harnesses.
6. **FMA contraction**: `-fmad=false` for every kernel, or explicit `fma` and rounding in the printer. *Open.*
7. **The scalar domain is a parameter**: concrete f32 and bf16 for tests, an exact ring for proofs.
8. **Floating point is trusted builtins for now**, checked by the battery. A precise model in Raccoon is on the
   horizon.

## 10. Frame and slot reuse experiment (2026-10-02)

The retained compiler experiment gives each syntax subtree a slot cursor checkpoint and records a separate plan
high-water mark. Parent-owned operand blocks and lexical binders are allocated before their children and remain pinned
while those children compile. Child-owned temporary regions rewind after each node. Match cases compile into the same
region because only one case runs; scrutinee temporaries die before the selected case starts. Escaping closures and Pi
values retain immutable environment snapshots, so later reuse cannot change captured values. This structural lifetime
rule needs no runtime liveness analysis and does not release a parent argument or sort/form operand before its last
child is compiled.

Three expected-value tests exercise a closure and a dependent Pi captured in a match scrutinee and forced after a
branch overwrites the same region, plus nested asymmetric match branches while sibling application arguments remain
live. A cheaper branch-only rewind was neutral in the JVM screen; the subtree cursor subsumes it. A Return-fold screen
was mixed and is dropped: against clean subtree medians, seed 17/83 were 8.4615/8.7895 s versus 8.5480/8.6427 s in
one order, then 8.7439/8.7323 s versus 8.4936/8.7260 s in reverse order. No native Return-fold image was built.

Counters below came from a separate instrumented diagnostic, never from an accepted timing. On one timed JVM
TinyGEMM invocation, the sum of reserved function-plan extents fell from 10,299 to 4,258 slots and maximum plan
extent from 578 to 40. The reference-bank fill count fell from 799.0 million to 458.0 million writes (42.7%),
required bank extent fell from 540,781 to 344,119 slots (36.4%), and maximum bank-array capacity fell from 1,048,576
to 524,288 entries. Bank growths fell from 12 to 11; copied elements fell from 4,193,280 to 2,096,128. Activation,
tail activation, non-tail activation and Return
counts were unchanged. Each timed `onStack` call creates a fresh session, so the recorded bank growth repeats per
invocation. These counts describe reserved bank extent and clearing traffic, not Node/AST metadata size or allocated
objects.

The accepted TinyGEMM runs used the ordinary `Interpreter.evalApply` entry, two warmups and three samples per seed,
with JFR off. They checked all 16,384 result cells and the exact 1,251 warp steps, 88 async completions, 98,304 TMA
bytes, 1,048,576 multiplies and adds, 4 MMA instructions, 64 tmem loads and 16 stores. Times are medians in seconds;
source API load/check and output materialization are outside the timed interval.

| Runtime and process order | b18 seed 17 / 83 | Subtree seed 17 / 83 | Source API load/check, b18 / subtree |
| --- | ---: | ---: | ---: |
| JVM, baseline then candidate | 8.493 / 8.499 | 8.602 / 8.819 | 9.478 / 9.578 |
| JVM, b18 reverse control after branch-only screen | 8.413 / 8.574 | — | 9.533 / — |
| JVM, subtree clean repeat during Return screen 1 | — | 8.548 / 8.643 | — / 9.676 |
| JVM, subtree clean repeat during Return screen 2 | — | 8.494 / 8.726 | — / 9.396 |
| Native, b18 then subtree | 12.678 / 12.771 | 12.623 / 12.444 | 10.821 / 11.392 |
| Native, subtree then b18 | 12.551 / 12.672 | 12.405 / 12.553 | 11.169 / 11.267 |

The JVM b18 reverse control followed branch-only screening. The later subtree-only runs were captured during
Return-fold screening, so those rows are independent checks, not paired reverse-order comparisons. The JVM
evaluator-only samples show no gain and were about 1–4% slower in direct comparisons; the paired native TinyGEMM
comparisons favored the subtree version by about 0.4–2.6%. Source setup/check is reported separately and varied
between runs. The same samples do not establish a broad throughput change.

The original attention command was also measured as whole-process `Main`, separately from TinyGEMM `evalApply`. Each
revision used five independent processes: two warmups and three timed samples. JVM `--json` medians were 7.950 s for
b18 and 8.014 s for subtree. Native `--raw` medians, with revision order alternated between warmups and samples, were
7.223 s and 7.178 s. Every JVM JSON process printed exactly `[]` (newline included), and separate `--raw` checks
produced the expected 696,817-byte CUDA output. Every native invocation produced the same output, SHA-256
`c7799ca4d1ac07a8190a78d829b12d205f4fc013cf3547bff4f48b6df7feeb0a`, with exit 0 and empty stderr. Whole-process
attention speed is effectively unchanged; these measurements do not support a general speedup or total-heap claim.

Baseline JFR `ExecutionSample` stacks contained 585 and 579 evaluator-thread samples. Inclusive per-event counts found
`runLoop` in 583/585 (99.7%) and 575/579 (99.3%) events; `applyApplication` in 278/585 (47.5%) and 279/579 (48.2%); and
`residualArguments` in 72/585 (12.3%) and 78/579 (13.5%). `Arrays.fill(Object[])` was the top frame in 41/585 (7.0%)
and 28/579 (4.8%), though inlining makes clear-call attribution approximate.
Sample-weighted baseline allocation estimates were about 10.6–10.9 GB per invocation, dominated by application,
constructor and residual-argument/vector scaffolding. CPU inclusive stack categories overlap; allocation owner groups
are exclusive within each recording, but their weighted estimates vary by seed. Neither is an exact wall-time
partition or a measurement of candidate allocation savings.

The clean slot candidate passed focused semantic tests and the full `sbt scalafmtAll validate` suite (999 passed,
0 failed). Exact source and class fingerprints, commands, every sample, counter logs, output digests and the excluded
aborted instrumented run are
recorded in [frame/slot experiment provenance](../target/performance/frame-composition-experiments/provenance.txt)
under ignored `target/performance`. The frozen JVM classes and TinyGEMM native image use the measured source; the
native Main image was built after the Match comment clarification. The final formatted source differs from the
measured source only by that comment and scalafmt whitespace; no executable code changed. One early timing attempt
accidentally retained diagnostic hooks, was stopped, and is marked invalid; it is excluded from every result above.
Diagnostics were fully stripped before the accepted frozen-class timings.

## 11. Historical GPU-aware native host-buffer prototype (removed 2026-10-03)

> **Historical prototype checkpoint, removed from the current branch.** This section records the earlier Scala prototype that decoded GPU-specific AST
> into a GPU-aware host interpreter. That boundary was rejected: the language runtime should expose only the independent
> finite `Buffer.Program` API described in [the buffer-program guide](../docs/buffer-program.md), while GPU scheduling,
> descriptors and lowering remain ordinary GPU-library code. At this checkpoint the TinyGEMM migration to that API was
> not complete; subsequent integration, validation and measurement are reported in §12.
> The GPU-aware Scala classes, execution path and native-only tests were removed from `codex/native-buffer-program`.
> The figures and commands below belong only to the old prototype on `codex/gpu-native-backend`; they are not a current
> native backend and are not measurements of the generic buffer executor.

The current TinyGEMM driver is source-only and has no backend selector. Run it from the repository root with
`sbt 'Compile / runMain com.raccoonlang.TinyGemmSpikeBenchmark --warmups 2 --samples 3'`.

The prototype's `NativeGpuBackend` was a Scala host interpreter for the **same checked `Cuda.Kernel` AST** used by the
TinyGEMM source path. It decoded and validated the checked `Cuda.Kernel` and `TinyDevice.Inputs` values, including their
exact 128×128×64 dimensions, launcher parameters, tensor maps, grid, and requirement expressions. It did not substitute a
kernel body or key execution on its name. Unsupported constructors could remain in an AST when unreachable; a reached
unsupported operation returned an explicit failure category.

That opt-in host-buffer prototype was not a GPU driver or a new Raccoon primitive. It supported the one-CTA TinyGEMM
subset through `--backend native` (with `--backend source` as the default at that checkpoint). Its mathematical data
domain was exact `Z/257`: BF16 and F32 determined typed widths, aliases, and addressing, but it did not implement BF16
rounding or IEEE floating-point arithmetic. Scheduling was one
deterministic round-robin order with FIFO async completion; there is no race detector, alternative schedule or
weak-memory model. As in the source evaluator, issuing `tmemLoad` into an already initialized register leaves its old
value readable until a successful `wait::ld` publishes the pending load. This is a bounded shared-model behavior, not
a general GPU memory-hazard or race model.

The decoded plan contains immutable AST and checked launch metadata. Immutable input vectors are separate run
arguments. Each invocation makes private primitive A/B, shared, tensor-memory, coverage and output arrays, and freezes
the returned output into an immutable `Vector[Int]`. A later, failed, changed-input, or concurrent run cannot mutate an
earlier result or the caller's inputs.

Each TinyGEMM run matched all 16,384 source outputs against the independent indexed Z/257 oracle, and matched source
outputs and counters for all 13 source-owned AST mutations. The wrong-K-slice mutation completes with the source
mutant's exact output and counters but differs from the independent canonical result. The load-order mutation issues
two writes to the same destination IDs from adjacent TMEM columns before one wait; source ordering preserves the
original column values, which match the independent oracle. Its extra load adds 16 retired steps, 16 completions and
16 tensor-memory loads (1,267 / 104 / 80 total). Expected unmutated counters remain 1,251 retired warp steps, 88 async
completions, 98,304 TMA bytes, 1,048,576 multiplies, 1,048,576 additions, four MMAs, 64 tensor-memory loads and 16
stores. Focused native-only tests also cover lane masks, exclusive loop bounds/stride, declaration reset, unreachable
unsupported nodes, input/output ownership, address validation, sequential `st.shared` aliases, transactional rollback
and commit, and BF16/U32 half-word aliasing.

The source and host-buffer timers have explicit boundaries. Source `Interpreter.evalApply(run, Vector(prepared))` and
source output API evaluation plus Nat-list decoding are timed in separate worker-thread regions; the matched source
metric is the median of each sample's two-region sum, excluding worker creation/join. `NativeGpuBackend.run(plan,
inputs)` includes private buffer allocation, A/B array copies, and immutable output-vector freezing. Checked-module
load/check, per-seed preparation, input extraction, native AST/input decoding and the host oracle are outside the run
timers and printed separately. Per-run JVM allocations come from `ThreadMXBean` for the executing thread; this is an
allocation counter, not an RSS or total-live-heap measurement. Allocated-byte figures are medians over their own
per-sample counters, independently of the sample that supplies the timing median.

The first JVM screens below predate the deferred-register-batch ordering fix described above; keep them as historical
allocation and timing controls, not as measurements of the final executable. Allocation values are independent sample
medians.

| Earlier JVM snapshot | Seed 17 median / allocated bytes | Seed 83 median / allocated bytes |
| --- | ---: | ---: |
| Source evaluator, 2 warmups / 3 samples; run + output decode | 8.600 s / 11.344 GB run + 0.308 GB output | 8.498 s / 11.344 GB run + 0.306 GB output |
| Host-buffer, before journal, first control; 10 warmups / 5 samples | 27.430 ms / 46,989,152 B | 21.287 ms / 45,915,296 B |
| Host-buffer, undo journal; 10 warmups / 5 samples | 18.921 ms / 15,639,216 B | 12.508 ms / 13,171,856 B |
| Host-buffer, before journal, reverse control; 10 warmups / 5 samples | 19.259 ms / 48,342,800 B | 12.958 ms / 46,477,896 B |

The source/native figures are from warmed JVM runs on this host, not a comparison with GPU execution. Native seed 83 had
large late outliers in the first control; the reverse control is the closer timing comparison. Its medians are only
about 2–4% above the journal candidate and the sample ranges overlap, so the evidence supports near-neutral to modestly
lower run time, not a robust speedup. The allocation reduction is clearer and repeatable: the source epilogue stages
128 `st.shared` instructions, and the pre-journal rollback path cloned the full 256 KiB shared bank for each one,
copying 32 MiB per invocation before array/object overhead. The journal records only touched 32-bit words and restores
them in reverse order on failure. The journal used about 32.7 MB and 33.3 MB fewer allocated bytes than the reverse
control for seeds 17 and 83; this removes the known snapshot traffic, not total backend or evaluator allocation.

Before the deferred-register-batch ordering fix, the journal candidate was compared against a no-journal snapshot with
the same decoder, map guards and runtime. These 10-warmup/5-sample JVM runs are historical executable-snapshot data;
they do not measure the final source fingerprint. The timing was inconclusive: seed 17 was effectively equal and seed
83 favored the journal, while sample-to-sample variance was material.

| Earlier JVM execution snapshot | Seed 17 median / allocated bytes | Seed 83 median / allocated bytes |
| --- | ---: | ---: |
| No-journal control | 17.594 ms / 48,124,064 B | 14.052 ms / 46,758,640 B |
| Undo journal | 17.608 ms / 14,263,432 B | 12.761 ms / 13,029,560 B |

An earlier frozen Graal Native Image, built before the deferred-register-batch ordering fix, was run through both
backends. These results are retained as historical evidence and are superseded by the corrected same-image screen
below.

| Earlier Native Image, backend | Warmups / samples | Seed 17 median / allocated bytes | Seed 83 median / allocated bytes |
| --- | ---: | ---: | ---: |
| Source evaluator + output decode | 2 / 3 | 12.135 s / 14.594 GB run + 0.390 GB output | 12.202 s / 14.594 GB run + 0.390 GB output |
| Host-buffer AST interpreter | 10 / 5 | 12.228 ms / 14,310,280 B | 12.299 ms / 14,309,672 B |

The earlier Native Image candidate has SHA-256
`79e257aff5705ec11ec586e048d7698229ce545dc98ac31a186b2ec51c1ee2bf` and is not the final executable.

After the overlapping-load ordering correction, the final implementation was rebuilt and both backends were measured
in that same Native Image. The source path used two warmups and three samples; the host-buffer path used ten warmups
and five samples. Source timing is the per-sample sum of source invocation and output API/list decoding in separate
worker-local regions. Native timing includes fresh buffers, input copies and immutable output-vector freezing. Both
timers exclude Prelude configuration loading, source API load/check, per-seed preparation, input extraction, plan
decoding and the host oracle; the logs report those separately. The source screen measured API load/check at 10.012 s
and Prelude loading at 18.1 ms. The native-backend screen measured API load/check at 10.101 s and Prelude loading at
13.3 ms.

| Corrected Native Image, backend | Warmups / samples | Seed 17 median / allocated bytes | Seed 83 median / allocated bytes |
| --- | ---: | ---: | ---: |
| Source evaluator + output decode | 2 / 3 | 12.278743 s / 14,593,703,656 B run + 389,837,272 B output | 12.315316 s / 14,593,691,744 B run + 389,836,744 B output |
| Host-buffer AST interpreter | 10 / 5 | 12.032 ms / 14,310,216 B | 11.936 ms / 14,309,608 B |

Within this bounded workload and these different warmup counts, the host-buffer timed region is about 1,021 times
shorter than the source run-plus-output region for seed 17 and 1,032 times shorter for seed 83. This compares two
host execution paths for one exact-ring kernel; it is not GPU throughput, general CUDA support or broad Raccoon
evaluator performance.

The final JVM native-backend screen used 20 warmups and seven samples because an earlier 10/5 run still showed JIT
settling. Its reported medians were 14.212 ms (seed 17) and 9.872 ms (seed 83); per-sample allocation medians were
14,251,728 B and 12,899,512 B. Seed 17's last two samples were lower than its first five, with fewer allocated
bytes, so treat its JVM median as indicative rather than settled. This is a standalone current-candidate result, not
a paired no-journal comparison.

The final overlap-fixed `sbt validate` passed 1,003/1,003 tests. `sbt scalafmtAll` also passed. The final candidate
Native Image was built with Oracle GraalVM 21.0.12, O2, armv8-a, ML-inferred PGO and SerialGC using
`--parallelism=4 -J-Xmx3g --enable-monitoring=jfr -ea`; JFR was off during timing. Its SHA-256 is
`37425435f1812027ae78553aa52df414e75e3089e47c4f56fd43f5a6e3608091`. The optional no-journal Native Image control
was built from the pre-journal device snapshot and predates the ordering correction; it is not used in the final
source/native comparison.

The following commands reproduce the historical prototype only after checking out `codex/gpu-native-backend`:

```sh
sbt 'Compile / runMain com.raccoonlang.TinyGemmSpikeBenchmark --backend source --warmups 2 --samples 3'
sbt 'Compile / runMain com.raccoonlang.TinyGemmSpikeBenchmark --backend native --warmups 20 --samples 7'
```

Build and run the same Native Image for both backends with:

```sh
MAIN_CLASS=com.raccoonlang.TinyGemmSpikeBenchmark OUTPUT_DIR=target/performance/gpu-native-backend OUTPUT_NAME=raccoon-tinygemm-native-overlap-fixed scripts/build-graal-native.sh --parallelism=4 -J-Xmx3g --enable-monitoring=jfr -ea
target/performance/gpu-native-backend/raccoon-tinygemm-native-overlap-fixed --backend source --warmups 2 --samples 3
target/performance/gpu-native-backend/raccoon-tinygemm-native-overlap-fixed --backend native --warmups 10 --samples 5
```

The complete sample logs, baseline and journal source snapshots, exact per-file fingerprints, commands, setup timings,
allocation counters and validation records are preserved under ignored
[`target/performance/gpu-native-backend`](../target/performance/gpu-native-backend). These records describe only that
bounded historical experiment. Current generic `Buffer.Program` measurements are in §12 and apply only to that path.

## 12. Generic `Buffer.Program` pipeline (bounded implementation)

The implementation lives in ordinary GPU-library Raccoon code above the independent finite buffer
language in [`buffer/Program.rac`](../buffer/Program.rac). The host runtime executes only generic encoded programs
through `Buffer.run`; it does not decode CUDA nodes, schedule GPU events, allocate GPU model state, or select a kernel
implementation. The public facade is [`evaluator/BufferGpuPlan.rac`](evaluator/BufferGpuPlan.rac).

**Status.** The focused public API test passed 2/2, including the checked kernel and ten non-fuel rejection mutants;
decoder-focused tests passed 1/1 and the scheduler edge test passed 1/1. The two-seed generic-buffer benchmark
completed with every output checked. `sbt validate` passed 1,029/1,029, so the repository validation gate is green for
this revision. These results do not establish a general CUDA evaluator.

**Supported input.** The first slice accepts only the checked one-CTA TinyGEMM shape M=128, N=128, K=64. The kernel
parameters, host parameters, tensor maps, grid expression and launch requirements must match the existing pure
`TinyDevice` shape predicates, and the launch block size is 256. Dynamic shared memory must be positive, four-byte
aligned and no larger than 262,144 bytes. The kernel name is not part of the predicate: a renamed kernel with an
identical body is compiled from its body. Other shapes, scalar parameter sets, multi-CTA grids and unsupported AST
forms are rejected.

**Compilation.** `Evaluator.BufferGpuPlan.compile(kernel)` takes only a `Cuda.Kernel`; no input arrays are available to
the compiler or retained by its sealed `Plan`. It expands the actual kernel body with the 128×128×64 compile-time
shape, decodes the expanded statements, and asks the event scheduler to validate protocols and produce ordered
`BufferData.Action`s. The scheduler is responsible for its finite warp schedule, event completion, barriers, TMEM
allocation/initialization, output coverage and quiescent exit checks. The facade lowers those actions through
`BufferData.lower` into a generic six-buffer `Buffer.Program` and checks the fixed and discovered extents, slot banks,
program words and instruction count against the generic VM limits before it returns `CompileResult.ready(plan)`.
Unsupported source or a failed check returns `CompileResult.rejected(code)`.

The plan exposes `planProgram(plan)` for inspection and `planStats(plan)` for the scheduler's
`WarpMachine.Stats`. The program contains ordinary input loads, integer operations, repeats and output stores. It does
not contain precomputed TinyGEMM answers or calls back into the GPU model. The measured plan has 385,941 words,
114,024 instructions, six buffers, 43,752 U32 slots and 36,102 U64 slots.

**Execution and errors.** `Evaluator.BufferGpuPlan.run(plan, inputA, inputB)` requires exactly 8,192 values in each
input list and values in 0..256, the current Z/257 input domain. It encodes both inputs as 16-bit little-endian fields,
calls `Buffer.run` once, requires exactly one output, and decodes exactly 16,384 32-bit output fields in 0..256. Each
`Buffer.run` invocation creates fresh private native buffers and returns immutable output lists. A successful result
contains the outputs and plan stats. `RunError.invalidInput(0)` identifies A and `(1)` identifies B;
`RunError.bufferFailure(code)` carries a generic VM failure code; `RunError.invalidOutput` reports the wrong output
count, length or scalar domain. There is no execution fuel parameter: the program's loops are structured and finite,
and generic program/resource validation remains in force. The fixed byte extents are A=16 KiB, B=16 KiB,
output=64 KiB and TMEM=64 KiB. The facade rejects programs over 1,000,000 words, 200,000 instructions, or 65,536
entries in either slot bank; variable buffer extents are limited to 64 MiB each and the total layout to 256 MiB.
Dynamic shared memory must be 4-byte aligned, positive and at most 256 KiB. These explicit limits are for this first
slice, not general device limits.

**Measured host execution.** The generic buffer path was measured with two warmups and three timed samples per seed;
reported values are medians. Compilation likewise used two warmups and three samples. Allocation is measured with the
executing worker's `ThreadMXBean` counter and reports cumulative allocated bytes, not peak or live memory.
`BufferGpuPlan.run` includes 16-bit input conversion, generic program
validation/preparation, fresh private buffers, execution and output-list marshalling. The source boundary is
`TinyGemmApi.run` plus output API evaluation. The prepared-VM boundary runs `NativeBufferProgram.Prepared.run` with
U16LE inputs already built and is a supporting lower-level measurement. Host-side output comparison is outside all
three timed regions; worker creation and join are outside the public/source regions. Every sample checked all 16,384
output values.

| Boundary | Seed 17 median / allocated bytes | Seed 83 median / allocated bytes |
| --- | ---: | ---: |
| `BufferGpuPlan.run` | 477.294 ms / 1,040,535,496 B | 488.172 ms / 1,040,664,344 B |
| Source run + output API | 8.687 s / 12,236,795,208 B | 8.596 s / 12,236,775,200 B |
| Prepared generic VM | 48.813 ms / 1,339,048 B | 48.370 ms / 1,339,048 B |

Plan compilation had a 12.782 s median and 16,212,409,160 allocated bytes; module load/check took 9.961 s.
The plan stats were 1,251 warp steps, 88 async completions, 98,304 TMA bytes, 1,048,576 scalar multiplies,
1,048,576 scalar adds, four MMA instructions, 64 TMEM loads and 16 TMA stores. Compilation is intended to happen
once, with the input-independent plan reused across calls. These figures describe one local bounded experiment, not GPU
throughput or a general performance claim. Measurements in §11 belong to the
removed GPU-aware Scala prototype and do not measure this generic path.

**Reproduction.** The focused checks and benchmark are:

```sh
sbt 'testOnly com.raccoonlang.BufferGpuApiTests'
sbt 'testOnly com.raccoonlang.BufferGpuDecodeTests'
sbt 'testOnly com.raccoonlang.BufferGpuEventScheduleTests'
sbt 'runMain com.raccoonlang.BufferGpuSpikeBenchmark --warmups 2 --samples 3'
sbt scalafmtAll
sbt validate
```

The API test compares both independent input sets with source results, reuses one compiled plan with changed A and B
inputs, checks malformed inputs and repeated/concurrent use, accepts a renamed identical kernel, and exercises
wrong-K descriptor and overlapping-TMEM-load mutations. The decoder test covers its supported instruction subset and
rejections. `sbt validate` passed 1,029/1,029; the full run is recorded in
[`target/performance/gpu-buffer-evaluator/validate.log`](../target/performance/gpu-buffer-evaluator/validate.log).
The benchmark log is [`target/performance/gpu-buffer-evaluator/buffer-gpu-spike-benchmark.log`](../target/performance/gpu-buffer-evaluator/buffer-gpu-spike-benchmark.log).
