# GPU library: design of the Blackwell layer

Status: implemented in `Gpu.rac` and exercised by `examples/tinygemm.rac`; not yet assembled or run (§6).
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
  - No type mentions an iteration count, so a loop body over the ring is generated once. Mismatched trip counts
    between the two sides deadlock; they cannot race.
- **Tensor memory** (`withTmem`, in the whole CTA): the kernel hands out one linear `TmemPermit`, which `withTmem`
  uses up: warp 0 allocates `n` columns (`tcgen05.alloc` into a shared word, then `relinquish_alloc_permit`, after
  which a second allocation would be illegal), the CTA synchronizes with the `tcgen05.fence` pair, and the callback
  receives `Acc(a, empty)`. The callback must hand back `Acc(a, ready)`, so no tensor-core work is in flight; the CTA
  synchronizes again and warp 0 deallocates. A kernel without tensor memory gives the permit up with `skipTmem`.
- **Accumulator**: `Acc(a, empty)` → `mmaFirst` (the first MMA of the stage has `enable_input_d = 0`, since tensor
  memory is not zeroed) → `AccPending(a, m)` → `mmaNext` (accumulating) → `sendAcc` commits it to a one-shot mbarrier
  (`withAccHandoff`). The epilogue's `recvAcc` waits for the barrier, fences `after_thread_sync`, and receives
  `Acc(a, ready)`, which `tcgen05.ld` requires. The handoff consumes the token on the issuing side and mints it on the
  waiting side, which is how authority crosses between roles that are generated separately.
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
So TMA writes, the MMA reads, and the host's `cuTensorMapEncodeTiled` call (to be generated from the same spec) cannot
disagree about layout. Shapes the tensor cores or the epilogue do not support (K box other than 64, M other than 128,
N not a multiple of 16 up to 256 or wider than the accumulator) are generation-time errors.

## 4. Output

The epilogue warpgroup reads the accumulator eight columns at a time (`tcgen05.ld.32x32b.x8`, then
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
| releasing a stage twice | the second release leaves an endpoint nothing can finish |
| the first K step inside the loop | a loop body's state keeps one type |
| never committing the MMAs | `AccPending` and `AccSend` are linear |
| storing before the handoff | `storeAcc` needs `Acc(a, ready)` |
| a second tensor-memory allocation | `TmemPermit` is linear |
| M = 64 boxes | generation-time shape check |

## 6. What is not verified here

The PTX templates follow CUTLASS and a published minimal kernel (sources in the scratch notes), but no `nvcc`/`ptxas`
is available on the development machine, so none of the generated sm_100a code has been assembled or run. `check.sh`
compiles the generated C++ against stub headers, with each inline assembly statement replaced by calls over its
operands, which checks everything but the templates. Every template is Experimental until `ptxas -arch=sm_100a`
accepts it and a run on hardware matches a reference GEMM.
