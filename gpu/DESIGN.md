# GPU library: design of the Blackwell layer

Status: working design for the next stage of the spike. `gpu/README.md` describes what exists; this document
describes the sm_100a layer being built on it, and is revised as the code lands.

The target is the structure of a minimal warp-specialized Blackwell GEMM ("TinyGEMM"): a TMA producer warp fills a
ring of shared-memory stages, one elected thread of an MMA warp issues `tcgen05.mma` into a tensor-memory accumulator
and releases each stage by `tcgen05.commit`, and an epilogue warpgroup reads the accumulator with `tcgen05.ld` and
stores the output. Everything below is typed by the three rules of the spike: a linear emitter threaded through all
code, lifetime-scoped values, and fieldless authority tokens.

## 1. Groups

A block of code is run by a static `Group`:

| Group | Threads | May |
|---|---|---|
| `cta(w)` | all `w` warps, converged | CTA barriers, allocate shared/tensor memory and barriers, split into roles |
| `warps(first, count)` | warps `[first, first + count)`, each converged | named barriers over the role, split further |
| `warpgroup(k)` | warps `[4k, 4k + 4)` | warp-collective tensor-memory loads (each warp owns its lane quadrant) |
| `lane` | one elected thread | issue TMA, `tcgen05.mma`, `tcgen05.commit`, mbarrier arrivals |
| `diverged(g)` | part of `g` under a per-thread branch | nothing collective |

Only sealed combinators change the group:

- `split(e, k, left, right)` runs `left` on the first `k` warps of the current group and `right` on the rest, as
  `if (warp < k) { … } else { … }`, and joins them with a barrier over the whole group. Each side is a callback
  invoked exactly once, so it may capture linear tokens, and the two sides capture disjoint ones. Values made before
  the split are visible on both sides; values made on one side are confined to it by its lifetime.
- `elect(e, body)` runs `body` on one lane of a one-warp group (`elect.sync`) and reconverges the warp after it.
- `branch` on a per-thread condition gives `diverged`, as today.

## 2. Asynchronous authority

Everything the hardware does asynchronously is typed by tokens that must be consumed, and by protocol state kept in
registers the protocol owns:

- **Stage ring** (`withRing`, in the whole CTA): allocates `S` shared stages and `2S` mbarriers (`full[s]`, `empty[s]`),
  initializes them on one thread with `fence.mbarrier_init` and a CTA barrier, and hands its callback a `Producer(r)`
  and a `Consumer(r)` endpoint. The callback must return `ProducerDone(r)` and `ConsumerDone(r)`, so both sides finish
  before the ring's storage can be reused.
  - The producer, on one lane, `acquire`s a stage (waits `empty[s]` at its phase), receiving a linear `Slot(r)`, and
    `fill`s it: `mbarrier.arrive.expect_tx` for the stage's bytes, then one TMA load per operand, consuming the slot.
    `finishProducer` waits for every stage to be released (the producer tail), so no TMA can still be writing when
    the ring closes.
  - The consumer `wait`s for a stage (waits `full[s]` at its phase), receiving a linear `Ready(r)` that authorizes
    reading the stage, and releases it either synchronously (`mbarrier.arrive` on `empty[s]`) or when its tensor-core
    work completes (`tcgen05.commit` to `empty[s]`).
  - Stage index and phase bit live in registers declared by each side's `start`; every operation advances them. No
    type mentions an iteration count, so a loop body over the ring is generated once. Mismatched trip counts between
    the two sides deadlock; they cannot race.
- **Tensor memory** (`withTmem`, in the whole CTA): one warp allocates `n` columns (`tcgen05.alloc` into a shared word,
  then `relinquish_alloc_permit`), the CTA synchronizes with the `tcgen05.fence` pair, and the callback receives
  `Acc(a, empty)`. The callback must hand back the accumulator in a state with no tensor-core work in flight; the same
  warp then deallocates.
- **Accumulator**: `Acc(a, empty)` → first `mma` (with `enable_input_d = 0`) → `Acc(a, accumulating)` → further `mma`s
  (accumulating) → handed off by `tcgen05.commit` to a one-shot mbarrier. The epilogue's `await` observes the barrier,
  fences `after_thread_sync`, and receives `Acc(a, ready)`, which `tcgen05.ld` requires. The handoff consumes the
  token on the issuing side and mints it on the waiting side, which is how authority crosses between roles that are
  generated separately.
- **The first K step** is peeled: `loopPeeled(count, first, rest)` emits the first iteration unconditionally, then a
  loop from 1. So the accumulator type changes once, in straight-line code, and every loop body keeps its state type.
  With `count = 0` the first iteration still runs; TMA fills out-of-bounds boxes with zeros, so the accumulator is
  defined (all zeros) and the producer and consumer still agree on the number of stages filled.

## 3. Layout agreement

A tensor map parameter's type carries its element type, box and swizzle (`TMap(l, spec)`). The stage buffers are laid
out from the same spec, and the `tcgen05.mma` shared-memory descriptors (start address, stride byte offset, 128-byte
swizzle) and the instruction descriptor (formats, M, N, majorness) are computed from it. So TMA writes, the MMA reads,
and the host's `cuTensorMapEncodeTiled` call (to be generated from the same spec) cannot disagree about layout.

## 4. Output

The epilogue warpgroup reads the accumulator quadrant by quadrant (`tcgen05.ld.32x32b`, then `tcgen05.wait::ld`):
thread `t` of warp `w` holds row `32w + t` of the tile. It stores its own row's columns, guarded against the matrix
edge, consuming the CTA's `GOwn` output token, so no two threads of the grid write one location.

## 5. Mutations to refuse

Each rule above gets a rejected program: reading a stage without `wait`; filling a stage without `acquire`;
releasing a stage twice; closing the ring without `finishProducer`; the same endpoint captured by both roles; TMA or
MMA issued from a group other than `lane`; `tcgen05.ld` outside a warpgroup or before `await`; accumulating into an
`empty` accumulator; deallocating tensor memory while an MMA may be in flight; a loop body that changes the
accumulator's state.

## 6. What is not verified here

The PTX templates follow CUTLASS and a published minimal kernel (sources in the scratch notes), but no `nvcc`/`ptxas`
is available on the development machine, so none of the generated sm_100a code has been assembled or run. Every
template is Experimental until `ptxas -arch=sm_100a` accepts it and a run on hardware matches a reference GEMM.
