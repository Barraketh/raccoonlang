# An evaluator for generated kernels

Status: **proposal** (2026-10-01), not implemented. It follows the first B200 session (`gpu/encoding/NOTES.md`,
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

**Today.** `Cuda.Stmt` covers plain C: declarations, stores, loops, branches and `__syncthreads`. Every PTX
instruction goes through `Stmt.asm(template, outs, ins)`, about 35 distinct instructions at 47 sites in `Core.rac`.
- The certificate checker cannot see them: `Check.rac` notes that I7 and I8 are not checked because "the AST does not
  record which threads run a block or what a barrier is for".
- Descriptors are integers packed by hand, then printed into strings.

**The change.** A constructor `Stmt.instr(i: Instr)`, with `Instr` covering what the encoding core emits:

| Family | Instructions |
|---|---|
| mbarrier | `init`, `inval`, `arrive` (local or remote, count, expect-tx), `try_wait.parity` (scope) |
| barriers | named `bar.sync`, `barrier.cluster.arrive/wait` |
| fences | `tcgen05.fence::before/after_thread_sync`, `fence.proxy.async`, `fence.mbarrier_init` |
| TMA | load (rank, CTA group, barrier), store, `commit_group`, `wait_group` |
| tcgen05 | `alloc`, `dealloc`, `relinquish`, `mma` (decoded instruction and shared-memory descriptors, CTA group), `commit` (mask), `ld`/`st` (shape), `wait` |
| warp | `elect`, `shfl.idx`, `vote.any` |
| registers | `setmaxnreg` |
| math | `ex2.approx`, `lg2.approx`, `rcp.rn`, `cvt.rn.bf16x2` |
| atomics | `ld.relaxed`, `atom.cas` |
| cluster | `%clusterid`, `%nclusterid`, `mapa` |

**What stays the same:**
- **The printed text.** The printer produces the same CUDA. The step's test is that every example still generates
  byte-identical code.
- **`Stmt.asm`.** It stays for `gpu/Gpu.rac`, the old core, which the evaluator does not run.

**Worth it without the evaluator:**
- `Core.rac`'s emitters read as instructions, not strings.
- Descriptors are values with named fields.
- `Check.rac` can state invariants over instructions: which barrier a wait names, and which group runs an aligned
  instruction.

## 4. The evaluator

**Where.** It runs on the host, not in Raccoon: the interpreter takes about 30 s to *generate* an attention kernel.
- It reads a kernel's AST, exported by the library (a JSON printer next to `Core.render`).
- It reads a launch: grid, parameters and buffers, given by a host test.
- Its language is a decision (§9).

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
| 184 registers | no | `ptxas` is not modelled |
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

1. **Typed instructions.** One worker round. Every example generates byte-identical CUDA, and `Check.rac` keeps its
   proofs.
2. **Evaluator v0.**
   - **Content:**
     - the exact numerics subset;
     - sequentially consistent memory with the happens-before race check;
     - asynchronous events;
     - the three schedulers.
   - **Use:** every harness runs against it at small sizes, in place of the hand-written mocks.
   - **Size:** the largest step, a few thousand lines. Most of it is the TMA box and swizzle layouts, the
     shared-memory descriptors, the tensor-memory layouts (M = 128 and M = 256, a pair's halves) and the MMA operand
     forms.
3. **The battery** in `hw.sh`.
4. **Weak memory and the proxies.** `MODELS.md`'s ordering rules O1–O6 become checks: a read counts as ordered only
   through the fence and barrier chain those rules name. This is where the evaluator says most that hardware runs
   cannot, because a missing fence often works on hardware.
5. **A Raccoon statement of the same semantics**, for the proofs.

## 9. Decisions

1. **Build it, staged as §8**, rather than more hand-written mocks. *Proposed; for the user.*
2. **Typed instructions first.** They pay for themselves without the evaluator. `Stmt.asm` remains, for `Gpu.rac`
   only.
3. **The evaluator's language**: Scala in this repository (an sbt subproject next to the checker), or standalone C++
   next to the harnesses. *Open.*
4. **Bit-exact only where PTX states the result**, and within documented bounds elsewhere, rather than a claim of
   bit-identity everywhere.
5. **The evaluator replaces the hand-written mocks** for validating harnesses.
6. **FMA contraction**: `-fmad=false` for every kernel, or explicit `fma` and rounding in the printer. *Open.*
