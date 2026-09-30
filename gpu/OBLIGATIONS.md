# GPU library: proof obligations

Status: specification for review. It states what the GPU library claims, what the claim rests on, and what each
sealed operation must do for the claim to hold, so that the claim can be reviewed against a checklist and, in the
plan of §8, verified in Raccoon. `DESIGN.md` explains the design; this document is its contract.

## 1. The claim

Let `P` be any Raccoon program that type-checks against `gpu/Prelude.rac`, imports `Gpu`, and prints
`Gpu.render(p)` for a `Program p`. Then the printed CUDA C++, compiled for sm_100a and launched by its generated
launcher (or, for a kernel without one, as its builder's launch contract says), satisfies:

- **S1, no data race.** No two accesses to one shared- or global-memory location, at least one a write, from
  different threads or from a thread and an asynchronous unit (TMA, tensor cores), are unordered by the CUDA/PTX
  memory model.
- **S2, collectives.** Every barrier, warp-synchronous and `.sync.aligned` instruction is executed convergently by
  exactly the threads it requires.
- **S3, asynchronous protocols.** Every mbarrier is initialized before use and invalidated after its last use; every
  wait observes the phase its protocol means; nothing reads a buffer an asynchronous unit may still be writing, and
  nothing writes one it may still be reading.
- **S4, resources.** Tensor memory is allocated once per CTA, freed with no tensor-core work in flight, and only its
  allocated columns are used. Shared memory stays within the CTA's allocation.
- **S5, output.** Each element of the output is written at most once per launch, by one thread.
- **S6, well-formed C++.** Every name is declared before use in an enclosing scope, every literal fits its type, and
  every printed identifier is one the library chose or checked.

Not claimed:
- **Liveness.** Roles whose loops run different trip counts deadlock (they cannot race).
- **Functional correctness.** That a GEMM computes a product is tested (`harness/`), not claimed.
- **Performance.**
- **Launches that break the contract.** A launcher called with arrays smaller than its extents, or aliasing arrays.

## 2. What is trusted

- Raccoon's kernel, and `gpu/Prelude.rac` under PAIRS_AND_PRELUDE §1's obligations T1–T5.
- `gpu/Cuda.rac`'s printer: it renders the AST faithfully.
- `gpu/Spec.rac`: its statements of I1–I6 say what the invariants mean, so that the checkers' soundness proofs
  (`gpu/proofs/`, §8) prove what §4 claims.
- The platform assumptions of §3: our reading of the PTX ISA and CUDA semantics.
- nvcc, ptxas, the driver and the hardware.

Everything else is `gpu/Gpu.rac`, whose operations must meet §6, and the typing discipline of §5, which makes
clients use them correctly.

## 3. Platform assumptions

Each assumption is our reading of NVIDIA's documentation and CUTLASS's usage. "Exercised" means the B200 runs of
`DESIGN.md` §7 depend on it and passed; that supports the assumption but does not prove it.

| # | Assumption | Source | Confidence |
|---|---|---|---|
| A1 | `threadIdx.x / 32` broadcast by `__shfl_sync(~0, …, 0)` is the same in every lane of a warp; the lane is `threadIdx.x % 32`. | CUDA guide | high, exercised |
| A2 | `__syncthreads()` must be reached by every thread of the CTA, and orders every shared- and global-memory access of the CTA's threads before it before every one after it. | CUDA guide | high, exercised |
| A3 | `bar.sync id, n` (1 ≤ id ≤ 15, n a multiple of 32) waits for n threads arriving at barrier `id`, all threads of each participating warp, and orders memory among them as A2. | PTX `bar` | high, exercised |
| A4 | `__syncwarp()` reconverges a warp; a `.sync.aligned` instruction must be executed by every thread of the warp, convergently. | PTX | high |
| A5 | `elect.sync` with mask `0xffffffff` in a converged warp makes exactly one lane's predicate true. | PTX `elect` | high, exercised |
| A6 | An mbarrier initialized with count c starts in phase 0; a phase completes when c arrivals have happened and its expected transaction bytes have all completed; `try_wait.parity p` succeeds once the phase of parity p completed, so on a fresh barrier parity 1 succeeds at once. | PTX `mbarrier` | high, exercised |
| A7 | `fence.mbarrier_init.release.cluster` then a CTA barrier makes initialized mbarriers usable by every thread and by TMA and the tensor cores. | PTX, CUTLASS | high, exercised |
| A8 | `mbarrier.inval` ends a barrier; its storage may then be initialized again. Initializing a live barrier again is not relied on. | PTX | medium |
| A9 | `cp.async.bulk.tensor.2d…mbarrier::complete_tx::bytes` writes the box into shared memory asynchronously, zero-filling (and counting) elements outside the tensor, and completes the box's bytes on the barrier. A thread whose wait observes that phase sees the writes. The destination must be 128-byte aligned, and 1024-byte aligned for 128-byte swizzle atoms. | PTX `cp.async.bulk.tensor`, CUDA driver `cuTensorMapEncodeTiled` | high, exercised |
| A10 | `tcgen05.alloc` / `relinquish_alloc_permit` / `dealloc` are warp-collective. Alloc writes the address to shared memory and takes a power of two ≥ 32 columns. A CTA may not allocate after relinquishing. Dealloc requires no tensor-core operation pending on those columns. | PTX `tcgen05` | high, exercised |
| A11 | `tcgen05.mma.cta_group::1.kind::f16`, issued by one thread, is asynchronous: it reads shared memory through the descriptors and writes D in tensor memory, with row i of an M = 128 result in lane i and N consecutive columns. Accumulate-disable overwrites D. The descriptor and instruction-descriptor bit layouts are as in `Gpu.smemDesc`/`instrDesc`. | PTX, CUTLASS `mma_sm100_desc.hpp` | medium-high, exercised (bit-exact results) |
| A12 | `tcgen05.commit…mbarrier::arrive::one` arrives on the barrier once every asynchronous tensor-core operation issued earlier by the executing thread has completed, reads and writes. | PTX | high, exercised |
| A13 | After observing a completion through a thread synchronization (an mbarrier wait or a barrier), `tcgen05.fence::after_thread_sync` orders later tensor-core operations after it. Before signalling one, `tcgen05.fence::before_thread_sync` orders earlier tensor-core operations (loads) before it. | PTX memory model, `tcgen05` | medium-high |
| A14 | `tcgen05.ld.32x32b.x8` is warp-collective: warp w reads lanes 32·(w mod 4) to +31, thread t lane 32·(w mod 4)+t, 8 consecutive 32-bit columns into its registers, valid after `tcgen05.wait::ld`. | PTX | high, exercised |
| A15 | `extern __shared__ __align__(1024)` places the dynamic buffer 1024-byte aligned when the kernel has no static shared memory. | CUDA, CUTLASS practice | medium-high, exercised |
| A16 | A block-scope `__shared__` array is one allocation for the whole kernel execution, whichever block declares it. | CUDA | high |
| A17 | The launcher's `cudaFuncSetAttribute` and `cudaLaunchKernel` run the kernel with the given grid, block and dynamic shared memory, or return an error. | CUDA runtime | high, exercised |
| A18 | `unsigned` arithmetic wraps modulo 2^32; a loop that neither terminates nor has side effects is undefined behavior. | C++ | high |

## 4. Structural invariants of emitted code

These are properties of the printed kernel alone, and all but I7 and I8 are decidable on its AST (§8 layer 1).
`Gpu.render` prints only a kernel that carries no generation error and passes the checkers of `gpu/Check.rac` named
below (`Check.WellFormed`, §9.5), so the parts of I1–I6 those checkers decide hold of every printed kernel, whatever
the builders do.

| # | Invariant | Kept today by |
|---|---|---|
| I1 | Every variable is declared once per kernel, before use, in an enclosing C scope. | Fresh names from `Gen`; lifetimes (M2). Checked on the output by `Check.scoping`: each id declared once, used only in the C scope of its declaration and after it (a loop's variable in its body), and no variable, thread, block or grid index, shared address or array element in the launcher. |
| I2 | Dynamic shared-memory regions are disjoint and aligned as requested. Total ≤ 232448 bytes. Dynamic memory only with a launcher. Never mixed with static arrays. | Bump allocation (`reserve`). Checked on the output by `Check.sharedMemory`: the total, the launcher, no static array with dynamic memory, and every constant offset into the buffer inside it. Disjointness, alignment, and offsets plus run-time indices are not in the AST. |
| I3 | Each join's named barrier has its own id in 1..15, and its count is its group's threads. | `join`, with a check. Checked on the output by `Check.namedBarriers`: each `bar.sync` (the asm template `Gpu.namedBarrier` emits) has literal operands, an id in 1..15 that no other has, and a count that is a positive multiple of 32. That the count is its group's is not in the AST. |
| I4 | Every `u32` literal is below 2^32. | Checked on the output by `Check.literals`: every 32-bit literal of the kernel and its launcher, and the launcher's block size and boxes, below 2^32; every 64-bit literal below 2^64. The other `u` literals the printer writes, shared-window offsets and the launch's shared bytes, are bounded by I2's check in the body; I1's keeps shared addresses out of the launcher. |
| I5 | The kernel's name is a C identifier; every other printed name is the library's. | `uniformParam` needs the Key (M8). Checked on the output by `Check.names`: the kernel's, the parameters' and the tensor maps' names are C identifiers the printer does not declare itself (`v` and digits, `gpu_…`, the launcher's locals), none is the kernel's name, each is declared once in its function, and every parameter an expression names is its function's. C++ keywords, CUDA's names and host library symbols are not excluded: the first two fail to compile, but an `extern "C"` kernel named as a host symbol is not ruled out. |
| I6 | The launcher passes the kernel's parameters in order. It asks for and launches with exactly the kernel's dynamic shared memory. It encodes each tensor map with its `TMap` box, bf16 and 128-byte swizzle. It launches the grid the builder assumes. | The printer passes the parameters in order and the kernel's shared memory. Checked on the output by `Check.launcher`: the launcher declares each non-map parameter as the kernel does, and encodes each tensor map exactly once, from a bf16 input and two u32 scalars of its own. The box, beyond fitting 32 bits, and the grid are the builders'. |
| I7 | Every collective sits where its whole group runs convergently. `__syncthreads` only in `cta` code. `bar.sync` only at a split's join. `elect.sync` only in one-warp code. Warp-collective `tcgen05` in whole-warp code, reconverged by `__syncwarp` after spin loops and guarded stores. | Groups (M3). Not checked on the output: the AST does not record which threads run a block (§9.6). |
| I8 | Every mbarrier is initialized, fenced and CTA-synchronized before any use, and invalidated after every thread's last use. | `withRing`, `withAccRing`, `withAccHandoff`. Not checked on the output: the AST does not record which addresses are barriers (§9.6). |

## 5. The discipline

These rules connect the typing to §1: a well-typed client can only compose sealed operations in ways that keep
the invariants and protocols. Each was found necessary; several were found by review.

- **M1, one emitter.** `Ctx(l, g)` is linear and every operation threads it, so code is emitted in the order authority
  flows, into the block of lifetime `l`.
- **M2, lifetimes are C scopes.** A value or register made in lifetime `l` cannot outlive `l`. Combinators that open a
  C block open a fresh lifetime, and those that do not keep the caller's, so M2 gives I1's "in an enclosing scope".
- **M3, groups.** `g` states which threads run the code. Only `split`, `elect` and `branch` change it, and a per-thread
  branch yields `diverged`, which no collective accepts. `warps(f, 4)` operations need `f mod 4 = 0`. Gives I7.
- **M4, fieldless tokens.** Authority is a linear, sealed, fieldless token whose type states the fact (a tile's state,
  a free stage, an accumulator's typestate). Only sealed operations mint or consume one.
- **M5, `Fixed` state** (review round 1). A branch or loop is generated once, and the code after it from one arm's
  state, so its state must have one value (`Fixed`). Otherwise a sum of typestates could skip a wait in one arm.
- **M6, thread-bound registers** (found in development). A protocol's stage and phase live in registers, which are per
  thread. So an endpoint is taken by one elected thread, or by one exact aligned warpgroup, and stays in that scope.
- **M7, reused storage is released quiescent** (round 2). A loop body's shared array is one array (A16), so a tile is
  released only `empty`, after the barrier that ends its reads.
- **M8, only the typed core prints** (rounds 2 and 3, and this document). Only `Gpu.render` of a sealed `Program`
  prints a kernel, and only the builders make one. A printed string is the library's own or a checked kernel name.
  `uniformParam`, which names parameters, needs the Key.
- **M9, re-fence after a join** (round 1). Threads that receive an accumulator through a thread barrier fence
  (`after_thread_sync`) before loading it, whoever observed the commit.
- **M10, grain.** A value is `uniform` only if it comes from uniform sources: literals, parameters, block and grid
  indices, loop and tile indices, or a shared read at a uniform index of a tile that no thread may write until a
  barrier (M4, M7).
- **M11, deadlock is not a race.** Rings are FIFOs whose producer tails drain every release. Roles that disagree on
  trip counts block forever; none can get a phase ahead.

## 6. Operation obligations

Each sealed operation must emit code that establishes what its result types claim, given what its argument types
claim. Types are abbreviated; "code" is what it emits into its `Ctx`.

### 6.1 Values and registers
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `lit`, `zero`, `add`, `mulC`, `divC`, `remC`, `ceilDivC`, `lt`, `fma` | argument values | nothing (pure expressions) | the value's expression, grain (the join of its inputs'), and `bound` (a true exclusive upper bound, forgotten past 2^32) | A18 |
| `reg`, `get`, `set` | a context | a declaration, read or assignment | a per-thread register of lifetime `l`; `get` is `thread` grain | I1 |

### 6.2 Control
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `loop` | `Fixed(S)`; unrestricted body | `for (i = 0; i < count; ++i) { body }` | the state after ≥ 0 iterations | M5 |
| `loopPeeled` | `Fixed(S1)` | `{ first } for (i = 1; i < count; ++i) { rest }` | the state after 1 + ≥ 0 iterations | M5 |
| `branch` | `Fixed(S)`; unrestricted arms | `if (c) { yes } else { no }`, arms in group `arm(g, grain(c))` | the state after either arm | M3, M5, M10 |
| `split` | `splits(g, k)` (else `#error`) | `if (warp < first+k) { left } else { right }` then the group's join (`__syncthreads` or `bar.sync`) | both sides ran, and every thread passed the join | A1–A3, I3 |
| `elect` | a one-warp context | `elect.sync` flag, `if (flag) { body }`, `__syncwarp` | the body ran on one thread (`Elected(m)`) | A4, A5 |

### 6.3 Shared tiles (SIMT)
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `shared` | a context | `__shared__ t v[n]` | `Tile(empty)`, a handle scoped to the callback | A16 |
| `storeMine` | `cta(n)` context, `Tile(empty)`, n elements | `v[threadIdx.x] = x` | `Tile(written)`: each thread wrote its own element | I7 |
| `sync1`, `sync2` | `cta` context | `__syncthreads()` | written → ready, reading → empty (`afterSync`) | A2 |
| `reads` | `Tile(ready)` | nothing | a read loan scoped to the callback; the tile comes back `reading` | M4 |
| `sread` | a loan; an index with a bound ≤ n (else `#error`) | `const t x = v[i]` | the element, grain of the index | M10 |
| `release` | `Tile(empty)` | nothing | the tile's authority ends | M7 |

### 6.4 Global memory (SIMT)
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `gload` | a matrix, a row and a column | a guarded load, zero outside | the element | — |
| `gstore` | `GOwn`, a `cta(tile²)` context | `if (inside) C[row*N+col] = v`, row and column from the block and thread indices | the CTA's block written once (S5) | A18, I6 |

### 6.5 Stage ring
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `withRing` | `cta` context; boxes pass `boxOk` | 1024-aligned stages, 2S barriers initialized (count 1) by thread 0 with fence and `__syncthreads`, and at close thread 0's `mbarrier.inval`s | `Producer`, `Consumer`; closes only on both `…Done` | A6–A8, A15, I2, I8 |
| `takeProducer`, `takeConsumer` | `Ctx(m, lane)` with `Elected(m)` | the side's stage and phase registers (producer 0/1, consumer 0/0) | `ProducerAt(r, m)` / `ConsumerAt(r, m)`, bound to that thread | M6, A6 |
| `acquire` | `ProducerAt` | wait `empty[stage]` at the producer's phase | `Slot`: the current stage is free (its last reader's commit completed) | A6, A12 |
| `fill` | `Slot`, maps whose boxes are the ring's | `arrive.expect_tx(stage bytes)`, two TMA loads into the stage, advance | the fill is in flight toward `full[stage]` | A9 |
| `finishProducer` | `ProducerAt` | S more waits on `empty`, advancing | every stage was released: no copy in flight, no reader active | A6, A12 |
| `await` | `ConsumerAt` | wait `full[stage]` at the consumer's phase | `Ready`: the stage's copies landed and are visible | A6, A9 |
| `releaseByMma` | `ReadyUsed(r, m)`, `Elected(m)` | `tcgen05.commit` to `empty[stage]`, advance | the stage is released when this thread's MMAs reading it complete | A12 |
| `finishConsumer` | `ConsumerAt` | nothing | `ConsumerDone` | — |

### 6.6 Tensor memory and the accumulator
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `withTmem` | `TmemPermit`, `cta` context, cols ∈ {32..512} | warp 0 alloc and relinquish, fence/`__syncthreads`/fence, read the address; at close fence/`__syncthreads`/fence and warp 0 dealloc | `Acc(empty)`; closes on `Acc(done)`, which has no work in flight | A10, A13, S4 |
| `withAccHandoff` | `cta` context | one barrier (count 1); `inval` at close | `AccSend`, `AccRecv` | A6–A8 |
| `mmaFirst`, `mmaNext` | `Ready(r, m)`, `Elected(m)`, `Acc(empty)` / `AccPending(a, m)`; shape passes `mmaShapeOk` (M = 128, N = cols) | K/16 `tcgen05.mma` from the stage's descriptors into the accumulator, the first overwriting | `ReadyUsed(r, m)`, `AccPending(a, m)` | A11 |
| `sendAcc` | `AccPending(a, m)`, `Elected(m)` | `tcgen05.commit` to the handoff | the handoff completes when every MMA completed | A12 |
| `recvAcc` | `AccRecv` | wait the handoff at parity 0, `after_thread_sync` | `Acc(ready)`: every column written (N = cols) and visible | A6, A13 |
| `storeAcc` | `Acc(ready)`, `COwn`, aligned warpgroup, bn = cols | fence, `__syncwarp`, per 8 columns `tcgen05.ld` + `wait::ld` + guarded stores; rows/columns from block and thread indices | the CTA's block written once | A13, A14, S5 |

### 6.7 Persistent GEMM
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `forTiles`, `forOwnedTiles` | `Fixed(S)`; `SchedOwn` for the owned loop | `for (t = blockIdx.x; t < tiles; t += gridDim.x)` with the tile's origin | per iteration a `TileAt`, and for the owned loop a `TileOwn`; CTAs visit disjoint tiles | M5, S5 |
| `withAccRing` | `Acc(empty)`, bufs·n ≤ cols | full (count 1) and empty (count 128) barriers per buffer; `inval` at close | producer and consumer sides; closes on both `…Done`, handing back `Acc(empty)` | A6–A8 |
| `takeAccProducer` / `takeAccConsumer` | an elected lane / an aligned warpgroup | the side's registers (0/1 and 0/0) | the side, bound to that thread or warpgroup | M6 |
| `acquireAcc` | producer side | wait `empty[buf]`, `after_thread_sync` | `AccFree`: the epilogue's loads of the buffer are done | A6, A13 |
| `mmaFirstInto`, `mmaNextInto` | `Ready`, `AccFree` / `AccFilling`; N = n | MMAs into the buffer's columns | `AccFilling` | A11 |
| `commitAcc` | `AccFilling`, `Elected(m)` | `tcgen05.commit` to `full[buf]`, advance | the buffer completes when its MMAs do | A12 |
| `finishAccProducer` | producer side | `bufs` waits on `empty`, advancing | every buffer was read: no tensor-core work in flight | A6 |
| `awaitAcc` | consumer side | wait `full[buf]`, `after_thread_sync` | `AccFull`: the buffer's results are visible | A6, A13 |
| `storeTile` | `AccFull`, `TileAt` and `TileOwn` of one iteration, bn = n | as `storeAcc`, at the tile's origin | the tile written once | A14, S5 |
| `releaseAcc` | `AccFull` | `before_thread_sync`, 128 arrivals on `empty[buf]`, advance | the buffer is free to the issuer | A13 |

### 6.8 Kernels
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `tiledKernel` | a body over `cta(tile²)` | the kernel; no launcher | a `Program` | I1–I7 |
| `tmaGemmKernel`, `tmaGemmPersistentKernel` | a body; boxes pass `gemmShapeOk` | the kernel and its launcher (extent checks, map encodings, shared-memory attribute, grid) | a `Program` | A17, I6 |
| `finish` | the Key | `#error` lines for every generation error | the `Program` | — |
| `render` | a `Program`; `Check.WellFormed` of its kernel, discharged by evaluating the checkers | the printed kernel | no generation error; I1–I6 as far as the AST shows them | the printer, `gpu/Check.rac` |

## 7. Public surface

Every operation that a client can call without the Key, and that builds a sealed value, must be sound on any
arguments. The audit as of this document:

- **Values.** `lit`, `zero`, `add`, `mulC`, `divC`, `remC`, `ceilDivC`, `lt`, `fma` build expressions from the
  library's own parts, with `u32` width checked on the output by `Check.literals` (I4). `tileRow0` and `tileCol0` read a sealed tile.
- **Evidence.** `fixedUnit`, `fixedPair` and the per-family `fixed…` exist only for one-valued types.
- **Endings.** `release`, `skipTmem`, `finishConsumer` and `finishAccConsumer` consume authority; none mints any.
- **Unsealed data.** `Gen` helpers (`push`, `fresh`, `child`, `after`, `check`, …) and instruction builders (`mbarInit`,
  `mmaIssue`, …) build unsealed `Gen` and `Stmt` values. These reach a kernel only through operations that need the
  Key (`resume`, `emit`, `finish`).
- **Found by this audit.** `uniformParam` built a `Val` from any name, typed `uniform`. It now needs the Key.

A new public operation must be added to this list with its argument.

## 8. Verification plan

The goal is that `Program.mk` takes a proof, `Program.mk (k: Kernel)(safe: Safe(k))`, which only `Gpu` can build
and Raccoon's type checker checks. Sealing then carries the guarantee to every client without reflecting Raccoon's
own typing. We approach it in three layers, each useful alone.

**Layer 1: structural invariants.** I1–I8 as a checker over `Cuda.Kernel`, together with a soundness statement for
each against a small syntactic specification (for example, the declared names at each program point). `render`
requires a proof that the checkers find nothing (§9.5). Where the kernel is concrete, which is always at generation, the
proof is `Eq.refl` evaluated by conversion. Alternatively, I1 becomes intrinsic: an AST indexed by the names in
scope. Needs Raccoon's evaluation-discharged evidence and an evaluator that scales (`docs/PROOF_BY_EVALUATION.md`).

Status: the checkers are built (`gpu/Check.rac`), one for the generation errors and one each for I1–I6 as far as the
AST shows them (§4), with unit tests (`gpu/checks/`). `Gpu.render` requires their certificate, `Check.WellFormed`,
which a client's `Gpu.render(p)` discharges by evaluation, and a failing checker is reported as
`EvidenceNotDischarged`, naming its field and showing its messages, which print as string literals although they are
computed. On the persistent GEMM the checkers, with checking `Check.rac` itself, added about 0.2 s when they were
built. A whole CLI run that generates it (starting the JVM, checking, printing) takes about 3.3 s of wall time, and the
restructuring for the soundness proofs changed it by less than the noise, 0.1 s (`gpu/proofs/NOTES.md`). Each checker
is proved sound in Raccoon (`gpu/proofs/`) against a syntactic statement of what its invariant means (`gpu/Spec.rac`),
and `WellFormed.sound` turns `Check.WellFormed(k)` into `Spec.WellFormed(k)` for every kernel; `gpu/proofs/NOTES.md`
records what made the proofs hard. I7 and I8 are not decidable on today's AST (§9.6).

**Layer 2: protocols.** Abstract models of A6, A9 and A12 (an mbarrier as phase, pending arrivals and expected
bytes; TMA fills and tensor-core commits as asynchronous events), the stage ring, accumulator ring, handoff and
shared-tile typestate as transition systems, and proofs of their safety properties under every interleaving of the
roles:
- no fill of a stage whose reader has not released it;
- no read of a stage whose fill has not completed;
- the tail drains every outstanding operation;
- the parity each side waits on is the phase it means.

We use two routes. One is generic in the stage count S, using arithmetic lemmas. The other is per configuration, by
a model checker written in Raccoon and proved sound once, since S is concrete at generation. Layer 2 is where the
subtle logic lives, and it needs no link to client programs.

**Layer 3: adequacy.** A program logic over an operational semantics of the CUDA subset and of A1–A18: tokens as
resources, each operation of §6 a proven triple, and `Ctx` carrying the proof of the code so far, so that the builders
produce `Safe(k)` compositionally. This closes the link between M1–M11 and S1–S6 that the reviews attacked. It needs
proof automation beyond reflection (metaprogramming or tactics), to be designed once layers 1 and 2 have shown what
is missing.

Even after layer 3, §2 stays trusted, and in particular §3: the models of TMA and tcgen05 are our reading of prose.
The hardware harness stays, as a check of those assumptions.

## 9. Decisions

Settled in review (2026-09-30):
1. **Layer 1 is a checker first.** An intrinsically scoped AST would change most of `Gpu.rac`; the checker, with
   a certificate required of what is printed (§9.5), does not.
2. **The models live in `gpu/model/`**, as Raccoon modules that `Gpu` imports.
3. **Model only what the protocols need.** Of A6–A14, model the ordering facts the protocols need, extending the
   models as proofs demand, each extension citing its source.
4. **The "Establishes" column of §6 becomes Raccoon propositions** as layer 3 is reached, so that its triples are
   stated from this document.

Settled in implementing layer 1 (2026-09-30):

5. **The certificate is on `render`, not on `Program.mk`.** An evidence field on `Program.mk` would need `finish` to
   prove the certificate of a generic kernel, and the library has no idiom for inspecting a computed Bool and
   branching on its proof (a dependent if). `render` is the only path that prints a kernel, so a certificate there
   reaches every client all the same: `render` requires `Gpu.WellFormed(p)`, that is `Check.WellFormed(p.kernel)`,
   which is discharged where a program renders its concrete kernel. A client's own function over programs states
   `Gpu.WellFormed(p)` to forward the proof, since it cannot read a program's kernel (`gpu/checks/generic_render.rac`).
   `finish` no longer checks I2, I4 or I5; the checkers decide them on the output, and a generation error is refused
   by `Check.errors`.
6. **I7 and I8 wait for layer 2.** Deciding them on the output needs the AST to record which threads run each block
   (a group per block) and which shared addresses are mbarriers and in which phase of their life each operation
   uses them. Whether the AST should carry that, or layer 2's models should state them instead, is a question for
   layer 2.
