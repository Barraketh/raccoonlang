# GPU library: design of the Blackwell layer

Status: implemented in `Gpu.rac` and exercised by `examples/tinygemm.rac` and `examples/persistent_gemm.rac` (§6); both
ran correctly on a B200 (§7) before the TMA-store epilogue (§2, §4), the fence after `await`'s wait and the arrivals at
initialization that complete phase 0 of the producers' barriers (§2), none of which has yet run on hardware.
`gpu/README.md` describes the spike as a whole.

The target is the structure of a minimal warp-specialized Blackwell GEMM ("TinyGEMM"): a TMA producer warp fills a
ring of shared-memory stages, one elected thread of an MMA warp issues `tcgen05.mma` into a tensor-memory accumulator
and releases each stage by `tcgen05.commit`, and an epilogue warpgroup reads the accumulator with `tcgen05.ld` and
stores the output through shared memory with TMA. Everything below is typed by the three rules of the spike: a linear emitter threaded through all
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
  swizzle) and `2S` mbarriers (`full[s]`, `empty[s]`), initializes them on one thread, which also arrives once on each
  `empty[s]` so that its phase 0 is complete and every stage starts free, then `fence.mbarrier_init` and a CTA barrier,
  and hands its callback a `Producer(r)` and a `Consumer(r)` endpoint. The callback must return
  `ProducerDone(r)` and `ConsumerDone(r)`, so both sides finish before the ring's storage can be reused.
  - **Taking an endpoint.** A side's stage index and phase bit are registers, and registers are per thread. So an
    endpoint is used by exactly one thread: an elected thread takes it (`takeProducer`, `takeConsumer`, which need the
    elect's `Elected(m)` and a context of lifetime `m` itself), which declares the side's registers in the elected
    block and yields `ProducerAt(r, m)` / `ConsumerAt(r, m)`. Those are confined to `m`, so they cannot pass to another
    thread (which would start from stage 0 and overwrite a stage still in use), and since only the elect's own
    context has lifetime `m`, the declarations are in scope wherever the endpoint can go.
  - Both sides start at stage 0 and phase 0. A side waits at the parity of its phase, which flips when it wraps, and
    neither side can get a round ahead of the other; so every wait names the current phase or the one just completed, the only ones `try_wait.parity` is defined for
    (PTX §9.7.15.16.19). The producer's first wait on a stage is on the phase the initializing thread completed: a wait
    of parity 1 on a fresh barrier, as CUTLASS and DeepGEMM start their producers, is not defined by the ISA.
  - The producer `acquire`s a stage (waits `empty[s]` at its phase), receiving a linear `Slot(r, m)`, and `fill`s it:
    `mbarrier.arrive.expect_tx` for the stage's bytes, then one TMA load per operand, consuming the slot and advancing.
    `finishProducer` waits for every stage to be released (the producer tail), so no TMA can still be writing when
    the ring closes.
  - The consumer `await`s a stage (waits `full[s]` at its phase, then `tcgen05.fence::after_thread_sync`, which
    orders the tensor-core work it issues next after the wait), receiving a linear `Ready(r, m)` that authorizes
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
- **Output staging** (`withStaging`, in the whole CTA): allocates `bufs` staging buffers of 32×32 f32 (4096 bytes,
  1024-byte aligned) per warp of an aligned warpgroup, and hands its callback an untaken `StoreSide(s)`; the callback
  must return `StoreDone(s)`, so no TMA store still reads the buffers when their shared memory is released or the
  kernel ends.
  - **Taking the side.** The aligned warpgroup takes it (`takeStore`, with the alignment proof), declaring its current
    buffer index as a register of each of its 128 threads, which run every operation on it together and so keep one
    index; `StoreAt(s, m, f)` is confined to the warpgroup's scope `m`. A TMA store is issued by one thread, and
    `cp.async.bulk.commit_group` and `cp.async.bulk.wait_group` count the bulk async-groups of the thread that
    executes them. So each warp's stores are issued, committed and waited for by one fixed thread, its lane 0: the
    operations guard those instructions with `lane == 0` themselves, and the endpoint cannot reach other threads (the
    per-thread lesson of the rings). Another group (a single warp, another role, the whole CTA) has no context the
    operations accept.
  - **A buffer's typestate**, per chunk: `acquireStage` (lane 0 waits `cp.async.bulk.wait_group.read (bufs − 1)`,
    then `__syncwarp`) → `StageFree`: the current buffer was last read by the store `bufs` stores ago, since each store
    is one group and the buffers are used in turn, and that store has finished reading it; the warp's threads write
    after the wait. `stageAcc` / `stageAccFull` (`tcgen05.ld` into registers, `wait::ld`, `st.shared.v4`) →
    `StageWritten`. `fenceStage` (`fence.proxy.async.shared::cta` in every thread, `__syncwarp`) → `StageFenced`: the
    writes are ordered before the async proxy's reads, and lane 0 is past every thread's fence. `storeStage` (lane 0:
    `cp.async.bulk.tensor.2d.global.shared::cta.bulk_group`, `cp.async.bulk.commit_group`; every thread: next buffer)
    → in flight, back to `StoreAt`. `finishStores` (lane 0: `cp.async.bulk.wait_group 0`, `__syncwarp`) → `StoreDone`.
  - The tokens between acquiring and storing have no `Fixed` evidence, so a chunk's protocol runs in straight-line
    code; `StoreAt` is `Fixed`, and the invariant it stands for (the current buffer's last store is at least `bufs`
    groups back) holds whether an arm or an iteration stored or not.
  - `finishStores` waits for completion, reads and writes, where CUTLASS's sm100 epilogue without C does not wait
    and the CUDA guide's example waits for the reads (`.read`): the PTX ISA states no rule for bulk stores
    outstanding when their thread exits, and this needs none (`OBLIGATIONS.md` A38).
- **The first K step** is peeled: `loopPeeled(e, count, init, first, rest)` emits the first iteration unconditionally,
  then a loop from 1. So the accumulator type changes once, in straight-line code, and every loop body keeps its state
  type. With `count = 0` the first iteration still runs; TMA fills out-of-bounds boxes with zeros, so the accumulator
  is defined (all zeros) and the producer and consumer still agree on the number of stages filled.

## 3. Layout agreement

A tensor map parameter's type carries its box (`TMap(l, spec)`; bf16 elements and 128-byte swizzle are fixed). `fill`
requires the maps' boxes to be the ring's, the stage buffers are laid out from the same boxes, and the `tcgen05.mma`
shared-memory descriptors (start address, stride byte offset 1024, version 1, 128-byte swizzle, K advanced 32 bytes
per step) and the instruction descriptor (f32 accumulator, bf16 operands, both K-major, M, N) are computed from them.
The dynamic buffer is declared 1024-byte aligned, and a kernel may not also declare static shared arrays (`Gpu.render`
refuses it, `Check.sharedMemory`), which would come first in the shared window. So TMA writes, the MMA reads, and the host's
`cuTensorMapEncodeTiled` call cannot disagree about layout: the kernel
comes with a generated host launcher (`<name>_launch`) that encodes the operands' maps from the same boxes, and the
output's (f32, boxes of 32×32 elements, 128-byte swizzle) as `CMap` says, checks the extents TMA's signed coordinates
and the tile counts need and that a row of C is a multiple of 16 bytes, sets the dynamic shared memory, and launches
the grid the kernel assumes. What remains to the caller is that A, B and C are distinct device arrays of M×K, N×K
and M×N elements. Shapes the tensor cores or the epilogue do not support are generation-time errors: `withRing` takes
only boxes 64 elements (one 128-byte swizzle row) wide and a multiple of 8 rows (so every stage is 1024-byte aligned),
and an MMA needs M = 128 and N a multiple of 16 up to 256, equal to the accumulator's columns.

## 4. Output

The epilogue warpgroup stores a 128×`bn` tile of C that it owns (`TileAt` and `TileOwn`: the CTA's block, located by
the block indices, in TinyGEMM; the iteration's tile in the persistent kernel), a chunk of 32 columns at a time:
`forChunks` consumes the tile's `TileOwn` and runs a loop, generated once, whose iteration `c` gets the chunk's
`ChunkAt` (columns `col0 + 32c` to `+ 31`) and a linear `ChunkOwn`, which `storeStage` consumes. Per chunk, every
warp reads its 32 lanes of the chunk's accumulator columns (`__syncwarp`, since a barrier wait's spin loop or lane 0's
branch may leave it diverged, `tcgen05.fence::after_thread_sync`, four `tcgen05.ld.32x32b.x8`, `tcgen05.wait::ld`):
thread `t` of warp `w` holds row `32 (w % 4) + t` of the tile. It writes the row into the warp's staging buffer in
the 128-byte swizzle (16-byte group `g` of row `r` at byte `128 r + 16 (g xor r mod 8)`, which is also free of bank
conflicts), and lane 0 stores the 32×32 box at (column `col0 + 32c`, row `row0 + 32 (w % 4)`) through `C_map` (§2).
TMA clips a box to the matrix, so partial tiles need no guards; the launcher requires rows of C to be whole 16-byte
units, the granularity of that clipping. Each chunk's box of rows is its warp's own, and each chunk is stored once,
so no two stores of the grid write one location, and the coordinates come from the tile and the warp, never from the
caller.

With two buffers per warp, a warp writes one chunk while its lane 0's store of the previous one is still reading.

CUTLASS's sm100 epilogue for this configuration (`REFERENCE_CUTLASS.md` §4) stages 128×32 subtiles for the whole
warpgroup, synchronizes the 128 threads with a named barrier after the fence and again after the wait, and issues
each store from warp 0. Here each warp stages and stores its own 32×32 box: bulk async-groups are per thread, so each
warp's stores have one issuing and waiting thread, the warps synchronize only within themselves (`__syncwarp`), and
no named barrier id is spent; the cost is four TMA stores of 4 KiB per subtile instead of one of 16 KiB. Where
CUTLASS relies on what we could not confirm from PTX, the stricter choice is ours: registers are read only after
`tcgen05.wait::ld`, one thread per warp issues, commits and waits, and the stores are waited for before the staging
memory is released or the kernel ends. Unlike CUTLASS, the accumulator buffer is released after the tile's last
chunk has been staged, not right after its last load.

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
| storing before the handoff | `stageAcc` needs `Acc(a, ready)` |
| writing a staging buffer before `wait_group.read` | `stageAcc` needs `StageFree` |
| ending the epilogue with stores in flight | only `finishStores` makes `StoreDone` |
| a second tensor-memory allocation | `TmemPermit` is linear |
| M = 64 boxes | generation-time shape check |
| an unaligned epilogue warpgroup | `takeStore` asks for the alignment as evidence |

## 6. The persistent kernel

`examples/persistent_gemm.rac` keeps TinyGEMM's roles but launches one CTA per SM (at most one per tile), each looping
over the 128×`bn` tiles of C that `Sched` assigns it (tile index `t` visited by CTA `t mod gridDim.x`), and gives tensor
memory two accumulators, so the epilogue of one tile overlaps the MMAs of the next. The stage ring runs on across
tiles. What is new:

- **Tile order.** Tile indices run through bands of `G` tile rows (the builder's argument; 16 in the example), column
  by column within a band: index `t` lies in band `t / (G·tilesN)`, at tile row `first + i mod rows` and tile column
  `i / rows`, where `first` is the band's first tile row, `rows = min(G, tilesM − first)` and `i` is `t`'s place in
  the band. The last band may have fewer rows, and within each band the map is a bijection onto its rows × columns,
  so the tile indices `[0, tiles)` map one to one onto the tiles, for every M, N and positive G (§6.7 of
  `OBLIGATIONS.md`; a zero G is a generation error). Row-major order made each wave of CTAs read all of B; in bands,
  the CTAs running at once read `G` rows of tiles of A and a few columns of tiles of B, which stay in L2.

- **Tile loops.** `forTiles(e, sched, state, body)` is a loop over the CTA's tiles, generated once; `body` gets the
  iteration's `TileAt(m, bn)` (its first row and column, for TMA coordinates). Every role runs the same loop, so they
  agree on the tiles. `forOwnedTiles` consumes the CTA's `SchedOwn` and also hands each iteration a linear
  `TileOwn(m, bn)`: the one loop that may write the output, once per tile. `forChunks` takes both, so a tile is
  written by the CTA the schedule gives it to, once, at the coordinates the schedule computed.
- **Accumulator ring.** `withAccRing(e, t, acc, bufs, n, X, body)` splits `withTmem`'s accumulator into `bufs`
  buffers of `n` columns, with a full barrier (arrival count one) and an empty barrier (arrival count 128) per
  buffer; the initializing thread completes each empty barrier's phase 0 with one arrive of count 128, so every
  buffer starts free and both sides start at phase 0. The MMA thread takes the producer side (`takeAccProducer`, as for the stage ring) and per tile runs
  `acquireAcc` (wait empty, `tcgen05.fence::after_thread_sync`) → `AccFree` → `mmaFirstInto` → `AccFilling` →
  `mmaNextInto`… → `commitAcc` (`tcgen05.commit` to full). The epilogue takes the consumer side as the whole aligned
  warpgroup (`takeAccConsumer`, with the alignment proof), so its 128 threads run every ring operation together and
  keep identical stage and phase registers: `awaitAcc` (wait full, fence) → `AccFull` → `forChunks` over the tile,
  staging each chunk with `stageAccFull` (§4) → `releaseAcc` (`tcgen05.fence::before_thread_sync`, 128 arrivals on
  empty), once every chunk's loads have completed; the stores themselves may still be in flight, since they read
  shared memory, not tensor memory. `finishAccProducer` waits until the epilogue has read
  every buffer, so the accumulator goes back to `withTmem`, `empty`, with no tensor-core work in flight. As with the
  stage ring, trip counts that disagree deadlock; they cannot race.
- **Output staging.** The epilogue takes the storing side once, before its tile loop, and finishes it after, so
  stores of one tile are still reading their buffers while the next tile's chunks are staged; `acquireStage` waits
  for them only when their buffer comes round again. Shared memory: the stage ring's 192 KiB, the staging's 32 KiB and
  the barriers come to 230496 bytes, under the 232448 an SM has.
- **Launcher.** The host launcher queries the SM count and launches `min(tiles, SMs)` CTAs.

`rejected/persistent_gemm_mutants.py` refuses storing a tile twice, storing to a tile of the program's choosing,
a second owning loop, reading an accumulator before `awaitAcc`, releasing it before the store, MMAs into a buffer not
yet acquired, writing a staging buffer before `wait_group.read`, a TMA store before the proxy fence, waiting for the
stores on one warp of the four whose lanes 0 issued them, ending the epilogue with stores in flight, bands of no tile
rows, and an issuer that does not drain.

## 7. On hardware

`check.sh` compiles the generated C++ against stub headers, with each inline assembly statement replaced by calls
over its operands, which checks everything but the templates. The templates follow CUTLASS; they are checked by
ptxas and by runs on an sm_100a GPU. `harness/gemm_test.cu` compares a generated kernel with a CPU reference exactly
(inputs are small multiples of 1/4, so every sum is exact), over whole, partial and tiny tiles and several tiles per
CTA, three runs each, with sentinel guard bands around C; checks that the launcher refuses extents TMA cannot
encode; and reports throughput.

**Results** (2026-09-29, one NVIDIA B200, driver 580.126, CUDA 12.9, on vast.ai):

These results predate the tile order in bands and the TMA-store epilogue (per-thread scalar stores before them).

| Kernel | Checks | M = N = K = 8192 |
|---|---|---|
| TinyGEMM | all 11 sizes exact, both refusals | 1.431 ms, 768 TFLOP/s |
| Persistent GEMM | all 11 sizes exact, both refusals | 1.121 ms, 980 TFLOP/s |
| cuBLAS (`cublasGemmEx`, same layout) | | 0.512 ms, 2147 TFLOP/s |

ptxas accepted every template (32 registers, no spills). compute-sanitizer's racecheck, synccheck and memcheck report
no hazards or memory errors on the small sizes (memcheck's two API errors are the launcher's intended refusals).
racecheck probably does not model the asynchronous TMA and tensor-core paths, so it supports rather than proves
their absence of races.

The first hardware round found two build problems, both fixed: the launcher's host parameters carried
`__restrict__`, which nvcc's front end (unlike clang's) rejects in `void* args[] = {&C, …}`; and `-arch=sm_100a`
compiles for plain `sm_100` with this nvcc, which has no tcgen05, so kernels are built with `-gencode
arch=compute_100a,code=sm_100a`. The round-1 review's probe that skips the producer's wait on a free stage (refused
since the `Fixed` rule) was also run, generated by the library before that fix: it passes while the ring never wraps
(K ≤ 256) and dies with an unspecified launch failure at K = 1024, once a stage is refilled before its release.

To reproduce:

```bash
gpu/gen.sh gpu/examples/tinygemm.rac > tinygemm.cu
```

```bash
nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a -o tinygemm_test tinygemm.cu gpu/harness/gemm_test.cu -lcuda && ./tinygemm_test
```

```bash
gpu/gen.sh gpu/examples/persistent_gemm.rac > persistent_gemm.cu
```

```bash
nvcc -std=c++17 -O2 -gencode arch=compute_100a,code=sm_100a -DGEMM_LAUNCH=persistent_gemm_launch -o persistent_test persistent_gemm.cu gpu/harness/gemm_test.cu -lcuda && ./persistent_test
```
