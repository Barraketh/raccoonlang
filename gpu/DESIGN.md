# GPU library: design of the Blackwell layer

Status: implemented in `Gpu.rac` and exercised by `examples/tinygemm.rac` and `examples/persistent_gemm.rac` (§6);
not yet assembled or run (§7).
`gpu/README.md` describes the spike as a whole.

The target is the structure of a minimal warp-specialized Blackwell GEMM ("TinyGEMM"): a TMA producer warp fills a
ring of shared-memory stages, one elected thread of an MMA warp issues `tcgen05.mma` into a tensor-memory accumulator
and releases each stage by `tcgen05.commit`, and an epilogue warpgroup reads the accumulator with `tcgen05.ld` and
stores the output. Everything below is typed by the three rules of the spike: a linear emitter threaded through all
code, lifetime-scoped values, and fieldless authority tokens.

## 1. Groups

A block of code is run by a static `Group`:

| Group | Threads | May |
|---|---|---|
| `cta(n)` | all `n` threads, converged | CTA barriers, allocate shared/tensor memory and barriers, split into roles |
| `warps(first, count)` | warps `[first, first + count)`, each converged | named barriers over the role, split further; with `count = 4` and `first % 4 = 0` (a proof argument), tensor-memory loads, each warp reading its own lane quadrant |
| `lane` | one elected thread | take ring endpoints, issue TMA, `tcgen05.mma`, `tcgen05.commit` |
| `diverged(n)` | part of a group under a per-thread branch | nothing collective |

Only sealed combinators change the group:

- `split(e, k, A, B, left, right)` runs `left` on the first `k` warps of the current group and `right` on the rest, as
  `if (warp < k) { … } else { … }`, and joins them with a barrier over the whole group (`__syncthreads` for a CTA, a
  fresh named barrier for warps). Each side is a callback invoked exactly once, so it may capture linear tokens, and
  the two sides capture disjoint ones; they return `A` and `B`. Values made before the split are visible on both
  sides; values made on one side are confined to it by its lifetime.
- `elect(e, X, body)` runs `body` on one lane of a one-warp group (`elect.sync`) and reconverges the warp after it
  (`__syncwarp`). The body receives an `Elected(m)` witness for its own scope `m`.
- `branch` on a per-thread condition gives `diverged`, as before.

**Fixed state.** A branch's arms and a loop's body are generated once, and the code after them from the state that
one arm or one iteration returned, while at run time either arm, or any number of iterations, may have run. That is
sound only if the state cannot record which. A state type that did, such as a sum of typestates
(`before(ProducerAt) | after(Slot)`), would let one arm wait, the other not, and the code after the branch assume the
wait. So `branch`, `loop`, `loopPeeled` (for the iterations after the first, which runs exactly once) and the tile
loops take `Fixed(S)`: evidence, which only `Gpu` can build, that every value of `S` is the same one. It exists for
`Unit`, for pairs of fixed types, and for each fieldless token family (`fixedTile`, `fixedProducerAt`, …). Values
that change at run time live in registers (`Reg`), which the unrestricted arms and bodies capture.

Result types of `split`, `elect` and the allocation combinators are explicit arguments: a callback's codomain mentions
its own lifetime binder, which forced implicits cannot see through.

## 2. Asynchronous authority

Everything the hardware does asynchronously is typed by tokens that must be consumed, and by protocol state kept in
registers the protocol owns:

- **Stage ring** (`withRing`, in the whole CTA): allocates `S` shared stages (1024-byte aligned, for the 128-byte
  swizzle) and `2S` mbarriers (`full[s]`, `empty[s]`), initializes them on one thread with `fence.mbarrier_init` and a
  CTA barrier, and hands its callback a `Producer(r)` and a `Consumer(r)` endpoint. The callback must return
  `ProducerDone(r)` and `ConsumerDone(r)`, so both sides finish before the ring's storage can be reused.
  - **Taking an endpoint.** A side's stage index and phase bit are registers, and registers are per thread. So an
    endpoint is used by exactly one thread: an elected thread takes it (`takeProducer`, `takeConsumer`, which need the
    elect's `Elected(m)` and a context of lifetime `m` itself), which declares the side's registers in the elected
    block and yields `ProducerAt(r, m)` / `ConsumerAt(r, m)`. Those are confined to `m`, so they cannot pass to another
    thread (which would start from stage 0 and overwrite a stage still in use), and since only the elect's own
    context has lifetime `m`, the declarations are in scope wherever the endpoint can go.
  - The producer `acquire`s a stage (waits `empty[s]` at its phase), receiving a linear `Slot(r, m)`, and `fill`s it:
    `mbarrier.arrive.expect_tx` for the stage's bytes, then one TMA load per operand, consuming the slot and advancing.
    `finishProducer` waits for every stage to be released (the producer tail), so no TMA can still be writing when
    the ring closes.
  - The consumer `await`s a stage (waits `full[s]` at its phase), receiving a linear `Ready(r, m)` that authorizes
    reading the stage, and releases it when its tensor-core work completes (`tcgen05.commit` to `empty[s]`).
    A synchronous release (`mbarrier.arrive`), for a consumer that reads the stage with ordinary loads, is not built.
  - When the ring closes, every thread is past its last use of the barriers (the roles' join), and one thread
    invalidates them (`mbarrier.inval`), so a ring opened again, in a loop, initializes fresh barriers. The
    accumulator handoff and the accumulator ring close the same way.
  - No type mentions an iteration count, so a loop body over the ring is generated once. Mismatched trip counts
    between the two sides deadlock; they cannot race.
- **Tensor memory** (`withTmem`, in the whole CTA): the kernel hands out one linear `TmemPermit`, which `withTmem`
  uses up: warp 0 allocates `n` columns (`tcgen05.alloc` into a shared word, then `relinquish_alloc_permit`, after
  which a second allocation would be illegal), the CTA synchronizes with the `tcgen05.fence` pair, and the callback
  receives `Acc(a, empty)`. The callback must hand back the accumulator (`Acc` never has tensor-core work in flight),
  in the state `withTmem` is told (`ready` for TinyGEMM, `empty` after an accumulator ring); the CTA synchronizes
  again and warp 0 deallocates. `ready` means holds results: only `recvAcc` makes it, after MMAs that wrote every
  column (the MMA's N is exactly the accumulator's columns, and the epilogue reads exactly that many). A kernel without tensor memory gives the permit up with `skipTmem`.
- **Accumulator**: `Acc(a, empty)` → `mmaFirst` (the first MMA of the stage has `enable_input_d = 0`, since tensor
  memory is not zeroed) → `AccPending(a, m)` → `mmaNext` (accumulating) → `sendAcc` commits it to a one-shot mbarrier
  (`withAccHandoff`). The epilogue's `recvAcc` waits for the barrier, fences `after_thread_sync`, and receives
  `Acc(a, ready)`, which `tcgen05.ld` requires. The handoff consumes the token on the issuing side and mints it on the
  waiting side, which is how authority crosses between roles that are generated separately.
- **Fences where the accumulator is read.** The epilogue's loads start with `tcgen05.fence::after_thread_sync`
  whoever waited for the accumulator, since `Acc(a, ready)` may reach the reading threads through a thread barrier
  from the threads that observed the commit.
- **Commit tracks the issuing thread.** `tcgen05.commit` covers the tensor-core work of the thread that executes it,
  so `AccPending(a, m)` and the used stage `ReadyUsed(r, m)` carry the elect's scope `m`: they are committed by the
  thread that issued them, before its elect ends.
- **The first K step** is peeled: `loopPeeled(e, count, init, first, rest)` emits the first iteration unconditionally,
  then a loop from 1. So the accumulator type changes once, in straight-line code, and every loop body keeps its state
  type. With `count = 0` the first iteration still runs; TMA fills out-of-bounds boxes with zeros, so the accumulator
  is defined (all zeros) and the producer and consumer still agree on the number of stages filled.

## 3. Layout agreement

A tensor map parameter's type carries its box (`TMap(l, spec)`; bf16 elements and 128-byte swizzle are fixed). `fill`
requires the maps' boxes to be the ring's, the stage buffers are laid out from the same boxes, and the `tcgen05.mma`
shared-memory descriptors (start address, stride byte offset 1024, version 1, 128-byte swizzle, K advanced 32 bytes
per step) and the instruction descriptor (f32 accumulator, bf16 operands, both K-major, M, N) are computed from them.
The dynamic buffer is declared 1024-byte aligned, and a kernel may not also declare static shared arrays (a
generation-time error), which would come first in the shared window. So TMA writes, the MMA reads, and the host's
`cuTensorMapEncodeTiled` call cannot disagree about layout: the kernel
comes with a generated host launcher (`<name>_launch`) that encodes both maps from the same boxes, checks the extents
the kernel's 32-bit index arithmetic and TMA's signed coordinates need, sets the dynamic shared memory, and launches
the grid the kernel assumes. What remains to the caller is that A, B and C are distinct device arrays of M×K, N×K
and M×N elements. Shapes the tensor cores or the epilogue do not support are generation-time errors: `withRing` takes
only boxes 64 elements (one 128-byte swizzle row) wide and a multiple of 8 rows (so every stage is 1024-byte aligned),
and an MMA needs M = 128 and N a multiple of 16 up to 256, equal to the accumulator's columns.

## 4. Output

The epilogue warpgroup reads the accumulator eight columns at a time (`__syncwarp`, since a barrier wait's spin loop
or the previous chunk's guarded stores may leave a warp diverged, then `tcgen05.ld.32x32b.x8` and
`tcgen05.wait::ld`): thread `t` of warp `w` holds row `32 (w % 4) + t` of the tile. It stores its own row's columns of
the CTA's block, guarded against the matrix edge, consuming the CTA's `COwn` output token, so no two threads of the
grid write one location. The block and row come from the block and thread indices, never from the caller.

## 5. Mutations to refuse

`rejected/tinygemm_mutants.py` holds TinyGEMM with one mistake each, run by `check.sh` through `mutate.py`:

| Mutant | Refused by |
|---|---|
| filling a stage without `acquire` | `fill` needs a `Slot` |
| leaving the ring without the producer tail | only `finishProducer` makes `ProducerDone` |
| running the producer on the whole warp | only an elected thread can take an endpoint |
| handing a taken endpoint to a later elect | `ProducerAt(r, j)` cannot leave `j` |
| MMA on a stage without `await` | `mmaFirst` needs `Ready` |
| accumulating into the fresh accumulator | `mmaNext` needs `AccPending`, not `Acc(a, empty)` |
| releasing a stage twice | a release consumes the used stage (`ReadyUsed` is linear) |
| the first K step inside the loop | a loop body's state keeps one type |
| never committing the MMAs | `AccPending` and `AccSend` are linear |
| storing before the handoff | `storeAcc` needs `Acc(a, ready)` |
| a second tensor-memory allocation | `TmemPermit` is linear |
| M = 64 boxes | generation-time shape check |

## 6. The persistent kernel

`examples/persistent_gemm.rac` keeps TinyGEMM's roles but launches one CTA per SM (at most one per tile), each looping
over the 128×`bn` tiles of C that `Sched` assigns it (tile `t` visited by CTA `t mod gridDim.x`), and gives tensor
memory two accumulators, so the epilogue of one tile overlaps the MMAs of the next. The stage ring runs on across
tiles. What is new:

- **Tile loops.** `forTiles(e, sched, state, body)` is a loop over the CTA's tiles, generated once; `body` gets the
  iteration's `TileAt(m, bn)` (its first row and column, for TMA coordinates). Every role runs the same loop, so they
  agree on the tiles. `forOwnedTiles` consumes the CTA's `SchedOwn` and also hands each iteration a linear
  `TileOwn(m, bn)`: the one loop that may write the output, once per tile. `storeTile` takes both, so a tile is
  written by the CTA the schedule gives it to, once, at the coordinates the schedule computed.
- **Accumulator ring.** `withAccRing(e, t, acc, bufs, n, X, body)` splits `withTmem`'s accumulator into `bufs`
  buffers of `n` columns, with a full barrier (arrival count one) and an empty barrier (arrival count 128) per
  buffer. The MMA thread takes the producer side (`takeAccProducer`, as for the stage ring) and per tile runs
  `acquireAcc` (wait empty, `tcgen05.fence::after_thread_sync`) → `AccFree` → `mmaFirstInto` → `AccFilling` →
  `mmaNextInto`… → `commitAcc` (`tcgen05.commit` to full). The epilogue takes the consumer side as the whole aligned
  warpgroup (`takeAccConsumer`, with the alignment proof), so its 128 threads run every ring operation together and
  keep identical stage and phase registers: `awaitAcc` (wait full, fence) → `AccFull` → `storeTile` → `releaseAcc`
  (`tcgen05.fence::before_thread_sync`, 128 arrivals on empty). `finishAccProducer` waits until the epilogue has read
  every buffer, so the accumulator goes back to `withTmem`, `empty`, with no tensor-core work in flight. As with the
  stage ring, trip counts that disagree deadlock; they cannot race.
- **Launcher.** The host launcher queries the SM count and launches `min(tiles, SMs)` CTAs.

`rejected/persistent_gemm_mutants.py` refuses storing a tile twice, storing to a tile of the program's choosing,
a second owning loop, reading an accumulator before `awaitAcc`, releasing it before the store, MMAs into a buffer not
yet acquired, and an issuer that does not drain.

## 7. What is not verified here

The PTX templates follow CUTLASS and a published minimal kernel (sources in the scratch notes), but no `nvcc`/`ptxas`
is available on the development machine, so none of the generated sm_100a code has been assembled or run. `check.sh`
compiles the generated C++ against stub headers, with each inline assembly statement replaced by calls over its
operands, which checks everything but the templates. Every template is Experimental until `ptxas -arch=sm_100a`
accepts it and a run on hardware matches a reference GEMM. `harness/gemm_test.cu` is that run: it compares a
generated kernel with a CPU reference exactly, over whole, partial and tiny tiles and more tiles than SMs, checks that
the launcher refuses extents TMA cannot encode, and reports throughput:

```bash
gpu/gen.sh gpu/examples/tinygemm.rac > tinygemm.cu
```

```bash
nvcc -std=c++17 -O2 -arch=sm_100a -o tinygemm_test tinygemm.cu gpu/harness/gemm_test.cu -lcuda && ./tinygemm_test
```

```bash
gpu/gen.sh gpu/examples/persistent_gemm.rac > persistent_gemm.cu
```

```bash
nvcc -std=c++17 -O2 -arch=sm_100a -DGEMM_LAUNCH=persistent_gemm_launch -o persistent_test persistent_gemm.cu gpu/harness/gemm_test.cu -lcuda && ./persistent_test
```
