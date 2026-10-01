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
clients use them correctly. For `gpu/encoding/` it is `Core.rac` and `Registers.rac`.

**A carve-out from §1 for `gpu/encoding/`.** Its claim is for programs that do not call `Registers.pool`, which only
the kernel builders may call (§7, M24). The language cannot refuse a client's call, since sealing is per file; a
client's pool at a count other than its kernel's makes `setmaxnreg` changes from a count the warps do not hold, which
PTX leaves undefined. `check.sh`'s register check refuses such a kernel when the CUDA toolkit is present
(`encoding/REGISTERS.md` §5).

## 3. Platform assumptions

Each assumption is our reading of NVIDIA's documentation and CUTLASS's usage. "Exercised" means the B200 runs of
`DESIGN.md` §7 depend on it and passed; that supports the assumption but does not prove it.

A19–A33 are the attention core's (`gpu/encoding/Core.rac`, `ATTENTION.md` §4.3, which numbers them so), and A39 its
score buffer's (A3a, `encoding/A3.md`); none is exercised yet, since no attention kernel has run on hardware. A34–A38 are the TMA-store epilogue's, numbered
A19–A23 before the attention core's assumptions took those numbers. A40–A42 are paged decode's
(`encoding/P2.md`), and A43–A56 the CTA pair's (`encoding/TWO_CTA.md`, with the facts and citations in
`encoding/TWO_CTA_FACTS.md`), A57–A59 the correction warpgroup's (A3b, `encoding/A3B.md`), and A60 the persistent
pair GEMM's (`encoding/TWO_CTA.md` §6 step 4), none exercised.

| # | Assumption | Source | Confidence |
|---|---|---|---|
| A1 | `threadIdx.x / 32` broadcast by `__shfl_sync(~0, …, 0)` is the same in every lane of a warp; the lane is `threadIdx.x % 32`. | CUDA guide | high, exercised |
| A2 | `__syncthreads()` must be reached by every thread of the CTA, and orders every shared- and global-memory access of the CTA's threads before it before every one after it. | CUDA guide | high, exercised |
| A3 | `bar.sync id, n` (1 ≤ id ≤ 15, n a multiple of 32) waits for n threads arriving at barrier `id`, all threads of each participating warp, and orders memory among them as A2. | PTX `bar` | high, exercised |
| A4 | `__syncwarp()` reconverges a warp; a `.sync.aligned` instruction must be executed by every thread of the warp, convergently. | PTX | high |
| A5 | `elect.sync` with mask `0xffffffff` in a converged warp makes exactly one lane's predicate true. | PTX `elect` | high, exercised |
| A6 | An mbarrier initialized with count c starts in phase 0 with c pending arrivals. An arrive of count k (1 by default) takes k of them; that k must not exceed the pending arrivals is our reading (PTX is silent; MODELS.md P5); a phase completes when its pending arrivals and its transaction count are both zero, and the next phase starts with c pending. `try_wait.parity p` is defined only for the current phase, for which it returns False, and the immediately preceding one, for which it returns True. In each phase, some wait must return True before any arrival of the next phase (PTX §9.7.15.16.5.1, which governs here; the CUDA guide's similar sentence is about `cuda::barrier`). Nothing is assumed of a parity-1 wait on a barrier that has never completed a phase: the rings complete phase 0 of every barrier a producer waits on first, at initialization. | PTX ISA 9.4 §9.7.15.16.3, §9.7.15.16.5.1, §9.7.15.16.8, §9.7.15.16.9, §9.7.15.16.12, §9.7.15.16.16, §9.7.15.16.19; CUDA Programming Guide §4.10.2 (for `cuda::barrier`: arrivals only on a non-zero counter) | high, exercised (the arrivals at initialization not yet) |
| A7 | `fence.mbarrier_init.release.cluster` then a CTA barrier makes initialized mbarriers usable by every thread and by TMA and the tensor cores, which access the barrier through the generic proxy. For a pair protocol the CTA barrier is a cluster barrier (A45). | PTX ISA 9.4 §9.7.15.4 (the fence applies to the thread's prior `mbarrier.init`s), §9.7.10.28.5.3 and §9.7.18.12.1 (generic-proxy barrier access); CUTLASS | high, exercised |
| A8 | `mbarrier.inval` ends a barrier: any operation but `init` on its storage is then undefined, so no arrival or complete-tx may land after it. Its storage may be initialized again: a ring reopened in a loop is initialized again by thread 0 right after its own `inval`, in program order, the CTA barrier being the join before the `inval` (so every other thread's last use precedes both). Initializing a live barrier is undefined and not relied on. | PTX ISA 9.4 §9.7.15.16.12, §9.7.15.16.13 (Example 2 initializes again after `inval` and `bar.cta.sync`) | high |
| A9 | `cp.async.bulk.tensor.2d…mbarrier::complete_tx::bytes` writes the box into shared memory asynchronously, zero-filling (and counting) elements outside the tensor, and on completion performs one complete-tx of the box's bytes on the barrier, with release semantics at cluster scope. A thread whose wait observes that phase sees the writes. The destination must be 128-byte aligned, and 1024-byte aligned for 128-byte swizzle atoms. | PTX ISA 9.4 §9.7.10.28.5.3, §9.7.10.28.1.2, §9.7.15.16.6; CUDA driver `cuTensorMapEncodeTiled` | high, exercised |
| A10 | `tcgen05.alloc` / `relinquish_alloc_permit` / `dealloc` are warp-collective. Alloc writes the address to shared memory and takes a power of two ≥ 32 columns. A CTA may not allocate after relinquishing. Dealloc requires no tensor-core operation pending on those columns. | PTX `tcgen05` | high, exercised |
| A11 | `tcgen05.mma.cta_group::1.kind::f16`, issued by one thread, is asynchronous: it reads shared memory through the descriptors and writes D in tensor memory, with row i of an M = 128 result in lane i and N consecutive columns. Accumulate-disable overwrites D. The descriptor and instruction-descriptor bit layouts are as in `Gpu.smemDesc`/`instrDesc`. | PTX, CUTLASS `mma_sm100_desc.hpp` | medium-high, exercised (bit-exact results) |
| A12 | `tcgen05.commit…mbarrier::arrive::one` arrives on the barrier once every `tcgen05.mma`, `tcgen05.cp` and `tcgen05.shift` issued earlier by the executing thread has completed, reads and writes (not its `tcgen05.ld`/`.st`, which `tcgen05.wait` tracks), and implicitly performs `tcgen05.fence::before_thread_sync`. | PTX ISA 9.4 §9.7.18.12.1 (overall completion, unlike `.sync_restrict::shared::read::mma::a`), §9.7.18.6.2.1.1 (what it tracks), §9.7.18.6.4.2 (Example 2) | high, exercised |
| A13 | After observing a completion through a thread synchronization (an mbarrier wait or a barrier), `tcgen05.fence::after_thread_sync` orders later tensor-core operations, MMAs and loads, after it; the ISA states the fence is needed there, and we assume no other ordering of an asynchronous `tcgen05` operation after a wait. Before signalling one, `tcgen05.fence::before_thread_sync` orders earlier tensor-core operations (loads) before it. | PTX ISA 9.4 §9.7.18.6.3 (which also says the standard mechanisms apply), §9.7.18.6.4 (§9.7.18.6.4.2, Example 2: the fence "is needed") | high |
| A14 | `tcgen05.ld.32x32b.x8` is warp-collective: warp w reads lanes 32·(w mod 4) to +31, thread t lane 32·(w mod 4)+t, 8 consecutive 32-bit columns into its registers, valid after `tcgen05.wait::ld`. | PTX | high, exercised |
| A15 | `extern __shared__ __align__(1024)` places the dynamic buffer 1024-byte aligned when the kernel has no static shared memory. | CUDA, CUTLASS practice | medium-high, exercised |
| A16 | A block-scope `__shared__` array is one allocation for the whole kernel execution, whichever block declares it. | CUDA | high |
| A17 | The launcher's `cudaFuncSetAttribute` and `cudaLaunchKernel` run the kernel with the given grid, block and dynamic shared memory, or return an error. | CUDA runtime | high, exercised |
| A18 | `unsigned` arithmetic wraps modulo 2^32; a loop that neither terminates nor has side effects is undefined behavior. | C++ | high |
| A19 | `tcgen05.st.sync.aligned.32x32b.xN.b32 [taddr], {…}` is warp-collective, every thread giving the same `taddr`; warp w of a warpgroup may access only lanes 32·(w mod 4) to +31 (text), and thread t writes lane 32·(w mod 4)+t, N consecutive columns (Figure 186 only; exercised for `ld` by the GEMMs). It is asynchronous; `tcgen05.wait::st` waits for every earlier `tcgen05.st` of the thread. | PTX §9.7.18.8.1, §9.7.18.8.4, §9.7.18.8.5, §9.7.18.6.2.1.2 | high (text); not exercised |
| A20 | A tensor-memory write by one thread (`st`, `wait::st`, `fence::before_thread_sync`, `mbarrier.arrive`) is visible to a `tcgen05.mma` issued by another thread after it observes that phase and fences `after_thread_sync`. | PTX §9.7.18.6.3, §9.7.18.6.4.4 (whose examples are `ld` → `mma` and `mma` → `ld`), §9.7.18.8.5 Example 2 (`st`, `wait::st`, `mma` in one thread) | medium-high |
| A21 | The barrier arrival of `tcgen05.commit` happens after the tracked MMAs have finished reading their tensor-memory A operand, so a thread that observes it and fences `after_thread_sync` may overwrite A. | PTX §9.7.18.12.1 ("track the completion of all the prior asynchronous tcgen05 operations"), §9.7.18.6.2.1.1 | medium-high |
| A22 | Within one warp, `tcgen05.ld` then `tcgen05.st` to the same address is ordered (the rescale's read-modify-write), as is `st` then `ld`. | PTX §9.7.18.6.2 (pipelined pairs `ld → st`, `st → ld`) | high |
| A23 | With `tcgen05.mma.cta_group::1.kind::f16 [d], [a], b-desc, idesc, p`, M = 128, A bf16 and not transposed: row i of A is lane i, K elements are packed two per 32-bit column with the lower K index in the low 16 bits, and each K = 16 step reads 8 columns from the given address. | PTX §9.7.18.10.10.1 (the form); the layout only in Figure 217 (§9.7.18.10.5.4) and CUTLASS's `SM100_MMA_F16BF16_TS` | **holds on a B200** (probe H1 and A1–A3b's harnesses, 2026-10-01) |
| A24 | B MN-major with 128-byte swizzle: instruction-descriptor bit 16 set; shared-memory descriptor LBO = 16384 (between 64-element halves of N), SBO = 1024 (between groups of 8 K rows), start advanced 2048 bytes per K step, base offset 0. | PTX §9.7.18.3.1–3, §9.7.18.4.1–2, §9.7.18.10.3 | **holds on a B200** (probe H2, 2026-10-01) |
| A25 | `cvt.rn.bf16x2.f32 d, a, b` rounds to nearest even and puts `a` in the upper half of `d`. | PTX §9.7.10.24 `cvt` | high |
| A26 | `ex2.approx.ftz.f32` is within 2 ulp and maps −∞ to +0; `lg2.approx.ftz.f32` is within 2⁻²² absolute on (0.5, 2) and 2⁻²² relative for other positive inputs; `rcp.rn.f32` is IEEE. Functional only. | PTX §9.7.3.21, §9.7.3.20, §9.7.3.13 | high |
| A27 | MMA D and A addresses and `tcgen05.ld/st` addresses may start at any column that is a multiple of 64 within the allocation. | PTX §9.7.18.1.1 (addressing); no alignment rule found in the text | **holds on a B200** (probe H3, 23/23 cases, 2026-10-01) |
| A28 | `cp.async.bulk.tensor.3d` with a rank-3 map zero-fills (and counts) elements outside the tensor in every dimension, and a 64 × 128 × 1 box lands as the rank-2 box does. Not relied on in A1, whose maps are rank 2 (`encoding/README.md`); A2's tails will. | PTX §9.7.10.28.5.3; CUDA driver `cuTensorMapEncodeTiled` | high |
| A29 | All `tcgen05` instructions of a kernel must use one `.cta_group`. | PTX §9.7.18.7.1, §9.7.18.10.10.1 | high (text) |
| A30 | (A3) `setmaxnreg.{inc,dec}.sync.aligned.u32` must be executed by every warp of a warpgroup, identically, with a synchronization between two of them; `.dec` needs a count at most the warp's, `.inc` one at least it, and `.inc` waits until the CTA's pool has the registers. Load-bearing in A3b: `splitWarpgroups` runs one per warpgroup, as its branch's first instruction (A59). | PTX §9.7.21.5 | high (text) |
| A31 | (A3) `vote.sync.any.pred` / `vote.sync.ballot.b32` with a full mask in a converged warp gives every lane the same result. Load-bearing in A3b: `voteAny`'s value is of grain `warp`, and a branch on it runs `warpwise` (M21). | PTX §9.7.15.10 | high |
| A32 | *Withdrawn* (`ATTENTION.md` §8): `tcgen05.ld.red` is not available on sm_100a. | PTX §9.7.18.8.3 | — |
| A33 | (A3) An MMA's reads of its tensor-memory A operand are ordered before a later MMA's writes of D to the same columns when one thread issues both (P overlaid on S, then the next S). Load-bearing in A3a: `issueScores` writes S over the P that the product the same thread issued before it reads, with no barrier between. | PTX §9.7.18.6.2 (pipelined pair "A and metadata reads → D writes"); FA4 relies on it (`ATTENTION.md` §2.7) | high (text); to be probed (`encoding/A3.md` §4) |
| A34 | `cp.async.bulk.tensor.2d.global.shared::cta.bulk_group`, issued by one thread, asynchronously reads the box from shared memory (1024-byte aligned for the 128-byte swizzle, whose rows of the box are 128 bytes) and writes it to the tensor at the given coordinates. Elements outside the tensor are not written, but clipping is at 16-byte granularity of the global address: with the base 16-byte aligned (the launch contract) and rows a multiple of 16 bytes (the launcher's check, and the encoding's stride rule), that is the row's end, so nothing outside the tensor is written, also when the box lies wholly outside. The operation belongs to the bulk async-group that the issuing thread's next `cp.async.bulk.commit_group` closes. | PTX ISA 9.4 §9.7.10.28.5.3 (`cp.async.bulk.tensor`), §5.5.3 (tiled mode, §5.5.3.3 out-of-boundary access), §5.5.7 (swizzling); CUDA Programming Guide §4.12 (TMA: "parts of the tile may be out of bounds" on writes, strides and addresses 16-byte multiples, shared memory 128-byte aligned, box rows at most the swizzle width); the 16-byte granularity observed on H100 in triton-lang/triton#11583, extrapolated to sm_100 | medium-high (a wholly outside box: medium); to be exercised (`{1, 8, 8}` stores wholly outside boxes) |
| A35 | `cp.async.bulk.commit_group` closes the executing thread's bulk async operations issued since its last commit into one bulk async-group. `cp.async.bulk.wait_group.read N` returns once at most the N most recent bulk async-groups of the executing thread have not finished reading their sources; `cp.async.bulk.wait_group N` once, beyond that, all earlier ones have completed, writes included and visible to the executing thread. Groups are per thread: a thread's wait says nothing of another thread's groups. | PTX ISA 9.4 §9.7.10.28.1.1 (async-group mechanism), §9.7.10.28.6.1, §9.7.10.28.6.2 | high |
| A36 | `fence.proxy.async.shared::cta`, executed by a thread after its `st.shared` writes, orders them before later operations of the async proxy on shared memory that are ordered after the fence (here by `__syncwarp`, A37), such as a TMA store's reads. Once a thread's `wait_group.read` returned, generic writes ordered after it (A37) may overwrite the store's source without a proxy fence. | PTX ISA 9.4 §9.7.15.4 (`membar`/`fence`, proxy fences), §9.7.10.28.2 (async proxy); CUTLASS `tma_store_fence` before the epilogue's barrier and TMA store, `tma_store_wait` before rewriting; CUDA Programming Guide §4.12 example | medium-high; to be exercised |
| A37 | `__syncwarp()` orders the memory accesses of the warp's threads before it before their accesses after it (as A2 for a CTA). | CUDA Programming Guide (`__syncwarp`) | high |
| A40 | (P2) A TMA load of a box of g ≤ 128 rows of 64 bf16 elements, 128-byte swizzled, into a 1024-byte-aligned destination writes those rows where a 128-row box at that destination writes its first g rows: the swizzle permutes each row's 16-byte chunks by the row's shared-memory address bits 7–9, not by the row's index in the box. The box's bytes, g · 128, are what its complete-tx counts. | PTX ISA 9.4 §5.5.7 (swizzling modes, a function of the shared-memory address), §9.7.10.28.5.3 (`cp.async.bulk.tensor`); CUDA driver `cuTensorMapEncodeTiled` (box rows 1 to 256) | medium-high; to be exercised (`paged_decode_g1`, a one-row box) |
| A41 | (P2) `ld.relaxed.gpu.global.b64` and `atom.relaxed.gpu.global.cas.b64` on one naturally aligned 64-bit word, by threads of one GPU, are morally strong with respect to each other, so each is performed with single-copy atomicity: a read sees the whole of one write, never halves of two. `atom.cas` stores its new value iff the word equals its compare value, as one indivisible read-modify-write, and returns the value it read. `cvta.to.global.u64` turns a kernel parameter array's generic address into its global one. | PTX ISA 9.4 §8 (memory consistency model: morally strong operations; the Atomicity axiom), `ld` (`.relaxed.scope`), `atom` (`.cas`), `cvta` | high |
| A42 | (P2) `shfl.sync.idx.b32 d, a, 0, 31, 0xffffffff`, executed by every lane of a warp, gives each lane lane 0's `a`. It waits for every lane of the mask, so lanes that left a lane-0 branch meet there; the kernel reconverges with `__syncwarp` first. | PTX ISA 9.4 `shfl.sync` | high |
| A38 | Nothing is assumed of bulk stores outstanding when their thread exits: every thread that commits one waits for all its groups to complete (`wait_group 0`) before its shared memory is released and before it exits. CUTLASS 4.8's sm100 epilogue without C does not wait at all (`store_tail`), its sm90 one waits for all groups' reads (`tma_store_wait<0>`, the `.read` form), as does the CUDA guide's example; the PTX ISA, as read here, states no rule for exit, so the stronger wait. | CUTLASS `sm100_epilogue_tma_warpspecialized.hpp` `store_tail` (`REFERENCE_CUTLASS.md` §4); PTX ISA 9.4 §9.7.10.28.6.2; CUDA Programming Guide §4.12 | — (a design choice, relying on A35 only) |
| A39 | (A3a) Nothing is assumed of an MMA whose tensor-memory A operand overlaps its own D: none is issued. The score buffer keeps a product's A (P, columns 64–127) and D (Ô, 128–255) disjoint; only the next S's D (columns 0–127) overlaps P, the A of an earlier MMA (A33). | PTX §9.7.18.10.10.1 (states no rule for overlapping A and D) | — (a design choice) |
| A43 | (pair) A kernel declared with `__cluster_dims__(2, 1, 1)` and launched by `cudaLaunchKernel` with an even grid x runs as clusters of two co-scheduled CTAs along x. `%cluster_ctarank` is 0 and 1 in a cluster, and its two CTAs form one CTA pair; `%clusterid.x` is the cluster's index along x, the same in both. | PTX §11.7.1 (`.reqnctapercluster`: the runtime uses the declared shape), §9.7.18.5.1 (pairs), §10.12, §10.16; CUDA guide's cluster example | medium: launch through the attribute is inferred |
| A44 | (pair) `barrier.cluster.arrive.release.aligned` then `barrier.cluster.wait.acquire.aligned`, run by every thread of both CTAs, orders every memory access of either CTA's threads before the arrive before every access after the wait. | PTX §9.7.15.3 | high |
| A45 | (pair) `mbarrier.init`, then `fence.mbarrier_init.release.cluster` by the initializing thread, then a cluster barrier (A44), makes the barriers usable by the peer's remote arrivals, the leader's multicast commits and the peer's TMA completions. The cluster barrier's release also covers the initializing thread's setup arrivals. No async-proxy fence is needed after the wait for the peer's TMA: a TMA accesses its barrier through the generic proxy. | PTX §9.7.15.4 (Examples: init, the fence, a cluster barrier), §9.7.15.3, §9.7.10.28.5.3 (the TMA's barrier access is generic-proxy) | high |
| A46 | (pair) `mapa.shared::cluster.u32 d, a, 0` gives the address in the leader's shared memory of the object at `a` in the executing CTA's. `mbarrier.arrive.release.cluster.shared::cluster.b64 _, [d]` performs one arrive-on on that barrier, releasing at cluster scope, and a `try_wait.parity.acquire.cluster` in the leader that observes the phase synchronizes with it. No thread waits on another CTA's barrier. | PTX §9.7.10.26, §9.7.15.16.11, §9.7.15.16.16, §9.7.15.16.19; CUDA guide §4.12.3 (cluster scope) | high |
| A47 | (pair) `cp.async.bulk.tensor.2d.cta_group::2.shared::cluster.global.mbarrier::complete_tx::bytes [dst], [map, …], [b]`, with `dst` in the issuing CTA and `b` the leader's barrier (by `mapa`), writes the box at `dst` as A9 and performs one complete-tx of its bytes on `b`, releasing at cluster scope. A complete-tx may precede the expect-tx within a phase: the transaction count goes negative, and the phase cannot complete while an arrival is pending. | PTX §9.7.10.28.5.3, §9.7.15.16.6; CUTLASS `SM100_TMA_2SM_LOAD` (the qualifier order) | high |
| A48 | (pair) `tcgen05.mma.cta_group::2.kind::f16` with M = 256, issued by one thread of the leader, reads A's rows 0–127 and B's rows 0 to N/2 − 1 from the leader's shared memory and A's rows 128–255 and B's other rows from the peer's, at the same descriptor addresses, and writes D's rows 0–127 and 128–255 to the leader's and the peer's tensor memory, lane = row mod 128, at one column address. The instruction descriptor's M field is 256 >> 4. | PTX §9.7.18.10, §9.7.18.10.10.1, §9.7.18.2.1 (Table 48), §9.7.18.4.2; the split only in CUTLASS `mma_traits_sm100.hpp` | medium |
| A49 | (pair) `tcgen05.commit.cta_group::2.mbarrier::arrive::one.shared::cluster.multicast::cluster [b], 0b11` arrives once, at cluster scope, on the barrier at `b`'s offset in each CTA of the pair, after every earlier `cta_group::2` MMA of the issuing thread has completed, its accesses to the peer's shared memory and tensor memory included, and performs `tcgen05.fence::before_thread_sync`. The two arrivals are not assumed simultaneous. | PTX §9.7.18.12.1, §9.7.18.6.2.1.1, §9.7.18.6.4.2 | high (the inclusion of the peer's accesses inferred) |
| A50 | (pair) `tcgen05.alloc`, `relinquish_alloc_permit` and `dealloc` `.cta_group::2` are run by warp 0 of each CTA, collectively, and each may block until both have. A 512-column allocation starts at column 0 in both CTAs. Dealloc requires that no tensor-core work or `tcgen05.ld`/`st` reaches either CTA's columns concurrently. | PTX §9.7.18.5 (Tables 55–57), §9.7.18.7.1 | high |
| A51 | (pair) A33 holds for `cta_group::2`, in both CTAs' tensor memory. | PTX §9.7.18.6.2 ("same N") | medium |
| A52 | (pair) `tcgen05.fence::before_thread_sync` and `::after_thread_sync` compose with cluster-scope arrivals and waits across the pair as within a CTA: A13, A20 and M13 hold when the writer and the waiter are in different CTAs. | PTX §9.7.18.6.3, §9.7.18.11.1 (no restriction to a CTA stated) | medium |
| A53 | (pair) An async-proxy write of a CTA's shared memory (a TMA load, by either CTA) and an async-proxy read of it by an MMA the other CTA issued are ordered by the barrier chain of O1 and O2 alone, with no proxy fence, as if by one thread block. | not in PTX (§8.9.5 covers "the same thread block"); CUTLASS and FA4 rely on it | **low–medium: a hardware probe and a question to NVIDIA** |
| A54 | (pair) `tcgen05.ld`/`st` reach only the executing CTA's tensor memory, with the lanes of A14 and A19. | PTX §9.7.18.8, §9.7.18.5 (Table 55) | high |
| A55 | (pair) Nothing is assumed of an access to a CTA that has exited, invalidated the barrier or freed the columns: every remote arrival, complete-tx, multicast commit and MMA access aimed at a CTA precedes, through a wait of its protocol, the cluster barrier before the close, and each CTA closes and exits only after it. | PTX §2.2.2 (the peer must not have exited), §9.7.18.5 (Table 55), §9.7.15.16.13 | — (a design choice) |
| A56 | (pair) A CTA whose dynamic shared memory exceeds half of an SM's 228 KB (`pairShared`, 116 KB + 1, which every pair kernel requests at least) is the only CTA on its SM, so no two clusters' collective 512-column allocations meet on one SM. PTX does not say whether the first warp of a `cta_group::2` allocation holds its columns while it waits for the peer's; two clusters sharing two SMs could otherwise each hold one SM's columns and wait for the other's. | CUDA guide (228 KB of shared memory per SM on sm_100, up to 227 KB per CTA); PTX §9.7.18.7.1 (silent on a waiting allocation's columns) | high (the occupancy rule); the hazard it avoids is unknown |
| A57 | (A3b) Chained completion. A `tcgen05` operation whose completion thread A observes through an mbarrier wait and `tcgen05.fence::after_thread_sync`, followed by A's arrive (release) on a second mbarrier, then B's wait (acquire) on that phase and B's `tcgen05.fence::after_thread_sync`, is complete before B's later `tcgen05` operations. The correction warpgroup (B) rescales Ô after the softmax warpgroup (A) observed the product before (S full) and sent α. | PTX ISA 9.4 §9.7.18.6.3 (the fences compose with mbarrier operations "to establish an ordering between the tcgen05 operations across threads"), §9.7.18.11.1; FA4 relies on it without the fence (`flash_fwd_sm100.py` 2700: "by the time softmax has signaled the correction warps, S_i must have been done, so O_i-1 must have been done as well") | medium-high; to be probed |
| A58 | (A3b) `max.f32`, `add.rm.f32`, `sub.rn.f32`, `fma.rn.f32`, `shl.b32` and `add.s32` compute as PTX specifies, IEEE and without flushing subnormals (no `.ftz`), so `ex2emu`'s error is the one measured on the host by emulating them (`encoding/NOTES.md` §"A3b"): 2⁻¹³·⁴⁷ relative for x ∈ [−126, 8], 2⁻¹²⁷ absolute for x ∈ [−127, −126). | PTX ISA 9.4 §9.7.3.3 (`add`), §9.7.3.4 (`sub`), §9.7.3.6 (`fma`), §9.7.3.12 (`max`), §9.7.9.8 (`shl`), §9.7.1.1 (`add.s32`) | high |
| A59 | (A3b) In a kernel compiled with `__launch_bounds__(n, r)` whose warpgroups run `setmaxnreg`, every warp enters with the budget `Registers.budget(n, r)` per thread, so the CTA's pool, which `setmaxnreg` draws on, holds n times the budget (the bounds cap a thread at the budget; that the count is then exactly the budget is the claim; A3b: 512 threads, 1 CTA, 128), and `ptxas` allocates the code a `setmaxnreg` dominates within its count (each role's, since it is the first instruction of the role's branch), spilling rather than exceeding it. | PTX §9.7.21.5 ("the kernel has been launched with a valid value of maximum number of per-thread registers"); CUTLASS's and FA4's warp-specialized kernels | medium-high: the entry count and the roles' spills are checked on every build by `check.sh`'s register check, which fails a kernel that changes counts and does not enter at its budget (`toolkit/registers.py`, `encoding/REGISTERS.md` §5); the SASS's `USETMAXREG` draws on the CTA's pool (`.CTAPOOL`); A3b passes its harness on a B200 (2026-10-01) |
| A60 | (pair, persistent) `%nclusterid.x` is the number of clusters along x of the launch, the same in every thread of the grid, and the clusters' `%clusterid.x` are 0 to `%nclusterid.x − 1`, one cluster each. With the launcher's grid of 2P × 1 CTAs and `__cluster_dims__(2, 1, 1)` (A43), there are P clusters, so the pairs' tile sequences (from `%clusterid.x` in steps of `%nclusterid.x`) partition the tile indices. | PTX §10.12 (`%clusterid`), §10.13 (`%nclusterid`) | high |

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
| I6 | The launcher passes the kernel's parameters in order. It asks for and launches with exactly the kernel's dynamic shared memory. It encodes each operand's tensor map with its `TMap` box, bf16 and 128-byte swizzle, and the output's as `CMap` says (f32, 32×32, 128-byte swizzle). It launches the grid the builder assumes. | The printer passes the parameters in order and the kernel's shared memory, and takes a map's element type from its source. Checked on the output by `Check.launcher`: the launcher declares each non-map parameter as the kernel does, and encodes each tensor map exactly once, for the use (load or store) the kernel's parameter declares, over one of the launcher's own arrays of the kind and element type that use needs (a bf16 input to load, an f32 output to store; two maps may share an array), with two u32 scalars of its own. That the body loads only through load maps and stores only through store maps, the box beyond fitting 32 bits, and the grid are the builders'. |
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
  branch yields `diverged`, which no collective accepts; a warp-uniform branch yields `warpwise` (M21). `warps(f, 4)`
  operations need `f mod 4 = 0`. Gives I7.
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
  indices, loop and tile indices, a shared read at a uniform index of a tile that no thread may write until a
  barrier (M4, M7), a read at a uniform index of a kernel input (the decode prologue's length, `encoding/P2.md`
  §3), or a full-warp `shfl.sync` broadcast from one lane (A42) in a CTA of one warp (the append's claim,
  `encoding/P2.md` §2), or a cluster index (`%clusterid.x` and `%nclusterid.x`, read by the pair builders: the same
  in every thread of a CTA, and of both CTAs of a pair, A43 and A60). An input is read-only for the whole launch: no
  thread of it writes one, and the launch contract of every builder that reads one says that nothing else does either,
  since a concurrent writer of an input is a race on it.
  A value is `warp` (the same in every lane of a warp) only if it comes from a warp vote (`voteAny`) or from `warp`
  and `uniform` values.
- **M11, deadlock is not a race.** Rings are FIFOs whose producer tails drain every release. Roles that disagree on
  trip counts block forever; none can get a phase ahead.

M12–M15 hold for `gpu/encoding/Core.rac`, the attention core, which has the operations they govern; `Gpu.rac` has
none of them (`ATTENTION.md` §4.1), and closes its protocols on `…Done` tokens instead of M15.

- **M12, row affinity.** Every per-row access (tensor-memory loads and stores of the 32x32b shape, `storeO`'s global
  row) computes its row from the executing thread, never from an argument: a tensor-memory lane from `warp mod 4` and
  the lane (`quadrantLanes`), a global row from the builder's row expression (`AttnOut`'s, `Mask`'s), which reads the
  warp and lane, and the `AttnOut`'s first row of the CTA, which reads the block indices. A global row is the CTA's only for the warpgroups the builder meant, so the store needs the `OOwn` of
  that warpgroup (`OOwn(l, t, f)`): one tile's CTA hands that of warps 4–7, the pair kernel those of warps 0–3 and 4–7
  (`storeO`, `storeFinal`). Per-row data (the statistics registers) never crosses threads except through a core protocol that
  indexes both sides the same way, so each thread's running maximum and sum describe the row its loads read. The
  statistics registers are data, not protocol state: they choose no barrier, phase or buffer, so they need no
  endpoint token and M6 does not apply to them; a wrong value is a wrong result, not a race. They are thread-bound
  anyway, by M2: they are declared in the warpgroup's side of a split, so no other role can name them.
- **M13, thread-written tensor memory.** A thread-written tensor-memory operand (P, and Ô after a rescale) is
  published only by the sealed sequence `__syncwarp`, `wait::st`, `fence::before_thread_sync`, arrive (`publishP`),
  and consumed only after wait, `fence::after_thread_sync` (`awaitP`) (PTX §9.7.18.6.4.4). This extends M9 to the
  opposite direction.
- **M14, coverage indices.** Where a buffer must be written whole before it is published (P), its token counts the
  chunks written (`PFree(…, next)`), and the publishing operation requires the full count (`publishP` needs 16).
- **M15, sides end in their finishers** (the readability review). A protocol's sides (`withRing`'s, `withAccRing`'s,
  `withExchange`'s and `withStaging`'s endpoints and every typestate token derived from them, `OFinal` included) are
  linear and belong to the opener's scope, which the callback's result cannot name (`docs/SCOPE_CONTAINMENT.md`), so
  the callback uses every side up before the opener closes. Every operation that takes a side gives one back, except
  its finisher: the waiting finishers `finishProducer`, `finishAccProducer` and `finishStores` (drains and waits), and
  `finishExWriter` (a wait, giving `OFinal`, which only `closeExWriter` ends); and the code-free `finishConsumer`,
  `finishAccConsumer`, `finishExReader` and `closeExWriter`, whose sides' issued work is released to the waiting side.
  So a close follows the drain, as a `…Done` token's return made it do (M7, M11). A new operation that took a side
  and gave none back would have to drain as the waiting finishers do. A3a's score buffer adds the waiting `awaitFinal`
  (giving `Final`, which only `closeRows` ends) and the code-free `finishMma` and `closeRows`; A3b's correction side
  the code-free `finishCorrection`, whose every publish waited for its stores.
- **M16, overlays** (A3a). Where one region's columns are read and then overwritten, the write takes the token that
  only the completed reads give. Threads writing over what they read (P over S) write from `Loaded`, which only
  `loadRow` makes, after its `wait::ld`; the tensor cores writing over what an earlier MMA of the same thread reads
  (the next S over P) write from `Holding`, which after a publish only `issuePV`, the reading MMA's issue, makes (A33);
  `takeMma` makes it before any publish, when no P exists, and `issueScores` hands it on.
  Between the two sides the reads are ordered by the buffer's barriers, as M9 and M13 order the exchange's.
- **M17, claims** (P2's append, `encoding/P2.md` §2). A write whose target the run-time data chooses needs a fact
  about that data, and the fact is a claim. Three things carry it:
  - **Exclusivity**, from the atomic. Every write of an owner word in a launch stores that launch's epoch (step 3's
    CAS stores `epoch·2^32 + b`, and nothing else writes the owners), so once a word holds the launch's epoch no claim
    changes it, and two claims of one word that hold are for one sequence and one head, so one warp. A failed CAS
    found the launch's epoch, so none needs a retry. The step 1 read must be single-copy atomic (A41): a torn read
    could pair this launch's epoch with another word's sequence. This holds for any start values of the owners and
    any epochs; a reused epoch can refuse a claim, or re-admit a sequence's own earlier claim, never two sequences. `harness/claim_model.py` checks it on every interleaving.
  - **Confinement**, from the arm. `withClaim` runs its arm only where the claim holds, and the row the warp writes is
    the one lane 0 claimed, by data flow (the broadcast), not a lane's own reading of the table. `Claimed`, which only
    the arm receives, belongs to its scope, and the arm returns the emitter alone.
  - **Exactly once**, from linearity. The arm receives a linear `AppendOwn`, which only `appendRow` uses up.
  The argument is about one launch: launches that share the owners must not overlap, as two launches on two streams
  with epochs 5 and 6 would each see the other's epoch as old, and both CAS steps would succeed. The launch contract
  says so, as any kernel that writes memory another kernel reads needs it.
- **M18, lockstep** (pair). Each CTA's producer and the leader's consumer walk one stage sequence of a pair ring, and
  the leader's issuer and each CTA's warpgroup one buffer sequence of a pair accumulator ring. Their counts agree
  because every role runs the trip count the kernel computed once from its parameters, as within a CTA (M11), and no
  client code reads a value that differs between the CTAs: the rank is the core's (`CtaPair`), which uses it only to
  choose the leader's arm and each CTA's half, and the client's other values are the launch's parameters, literals and
  loop indices, the same in both CTAs, or thread-grain values, which no loop count or uniform branch takes. A
  disagreement, as from a mistaken count, deadlocks: the extra fills wait in their producer's tail for releases that never come, and that CTA
  never reaches the close's cluster barrier. A persistent pair kernel's roles loop over its tiles (`forPairTiles`), each
  from `%clusterid.x` in steps of `%nclusterid.x` up to the tile count, all three the same in both CTAs (A60, M10): so
  both CTAs visit one tile sequence, and every role the same number of tiles. No role's loop runs in one CTA only:
  - a loop uses up its role's side, which an `onLeader` arm cannot capture (M20, M23), and the leader-only sides'
    loop, the issuer's, has no counterpart in the peer;
  - no value of the leader's alone reaches code both CTAs run, so none can choose a trip count or a branch there. An
    arm hands back only its context, and the only unrestricted mutable state it could write is a register declared
    outside it, which `set` refuses at generation. Everything else that a write reaches (shared tiles, staging
    buffers, global memory, tensor memory, claims) needs a linear token, which the arm cannot capture. No side can get a phase ahead, since each CTA's `empty[s]` receives only
  the leader's commits for that stage, and the leader's `full[s]` both CTAs' bytes for the same round.
- **M19, pair resources** (pair). A pair opener (`withPairTmem`, `withPairRing`, `withPairAccRing`) takes the
  kernel's own context, `Ctx(l, …)` with the kernel's `CtaPair(l)`, so it runs in the kernel's top-level spine and
  never under a branch, loop, role or other scope, each of which has a lifetime of its own. Every thread of both CTAs
  runs every opener and close, in one order, from one generated text, so both CTAs' layouts are equal. An opener
  publishes its barriers (A45) before its callback runs; its close waits at a cluster barrier (A44) after the
  callback, whose sides have all been finished (M15), then invalidates or frees. The single-CTA openers (`withRing`,
  `withTmem`, `withAccHandoff`, `withAccRing`, `withExchange`, `withScoreBuffer`, `withCorrectedBuffer`) read the kernel's CTA group from the
  generation state and refuse in a pair kernel, and every `tcgen05` instruction prints that group, so a kernel uses one
  (A29). Every barrier wait and commit prints the group's form too (`.acquire.cluster`, the commit multicast to both
  CTAs). A pair kernel asks for at least `pairShared` bytes of shared memory, so its CTAs have SMs of their own (A56).
- **M20, the leader** (pair). Tensor-core work and commits are issued only in the leader. The endpoints that issue
  them, a pair ring's consumer and a pair accumulator ring's issuing side, are taken only with a `Leader(n)`, which
  only `onLeader`'s arm holds and which belongs to the arm's scope; every MMA and commit consumes a token derived from
  those endpoints, so it runs in the arm. The arm hands back only its context.
  The arm captures no linear value: what it uses up runs in one CTA only. It is handed the sides it may use up, which
  must be leader-only (`LeaderOnly`): a pair ring's `Consumer` and a pair accumulator ring's `AccProducer`, whose every
  operation is the leader's and whose finishers the peer may skip (`Core.LeaderOnly` gives why). Every other side, a
  producer's, a warpgroup's or the storing side, has work in each CTA, and its finisher runs in code both CTAs run: so
  each CTA drains its own producer and waits for its own stores before the closes (M15, M19). Without this, an arm
  could finish the peer's producer or storing side in the leader alone (review of step 4). The arm writes no register
  declared outside it (`Gen.writable`, checked by `set`), so no value leaves it but through its context (M18).
- **M21, `warpwise`** (A3b). A branch on a condition of grain `warp` runs its arms in `warpwise(f, c)`
  (`Group.arm`): each warp converged, the group as a whole not, since whole warps run either arm. Warp collectives on
  a warp's own lanes take that group (`rescaleQuadrant`: `tcgen05.ld`, `.st` and `wait::ld` of the warp's quadrant,
  `__syncwarp`). No protocol operation does: each takes `warps(f, 4)`, since every thread of the warpgroup runs it,
  keeping one copy of the side's registers and arriving once per phase (M6). `recvAcc`, generic in its group, would
  take a `warpwise` context, but its side reaches no arm: a branch's arms capture no linear value, and its state must be
  `Fixed`, which `AccRecv` is not. A per-thread condition still yields `diverged` (M3), so a skip decided per thread
  cannot reach `rescaleQuadrant`.
- **M22, the α ring** (A3b). A per-row value passes between two aligned warpgroups only through the α ring of a buffer
  with a correction warpgroup, one slot of 128 f32, and both index it alike: thread r writes and reads element
  `threadIdx.x mod 128`,
  which in an aligned warpgroup is `32·(warp mod 4) + lane`, the row of its lane (M12). The send (`publishAlpha`)
  waits for the slot's empty phase, writes and arrives on its full barrier in one operation; the receive
  (`awaitAlpha`) waits on the full barrier, fences `after_thread_sync`, reads and arrives on the empty one in one
  operation; each end's phase register is its warpgroup's (M6). The sender sends once per block after the
  first, from `Probs` (after it observed the block's scores, A57); the receiver receives once per block after the
  first; and the correction warpgroup arrives on P full once per block, after its zeroing or rescale. So a slot is
  never written before it is read, nor read before it is written, and each phase of P full holds one block's 256
  arrivals.

- **M23, callbacks run where their group says.** A callback that may capture linear values runs exactly on the
  threads its context's group names, in every CTA, once. A combinator whose emitted code runs a callback only under a
  run-time condition, or several times, either narrows the context's group to the threads that run it, or takes an
  unrestricted callback, which captures no linear value. The bug this states (review of step 4): `onLeader`'s arm ran
  in one CTA of the pair, kept its group, and captured linear sides, so a side could be finished in the leader alone.
  - **Narrowing:** `split`, `elect`, and the role builders on them (`Layout.roles4`, `rolesPair`, `rolesCorrected`,
    `splitWarpgroups`, `withShare`).
  - **Unrestricted:** `branch`, `when`, the loops (`loop`, `loopFrom`, `loopPeeled`, `forChunks`, `forTiles`,
    `forOwnedTiles`, `forPairTiles`, `forOwnedPairTiles`, `forHalfChunks`), `withClaim` and `onLeader`; and the
    generation-time repetitions, which emit a callback once per chunk (`eachChunk`, `writeP`, `mapChunks`, `mapRow`).
  - **Unconditional:** the openers (`shared`, `reads`, `withRing`, `withTmem`, `splitTmem`, `withAccHandoff`,
    `withAccRing`, `withStaging`, `withExchange`, the score buffers and the pair openers), whose callbacks run once on
    their context's threads.
  Every conditional combinator has a standing mutant that uses up an outer linear token in its callback, refused by
  the closure's kind: `append_in_loop` (`loop`), `claim_inside_arm` (`withClaim`), `store_side_captured_by_chunk_loop`
  (`forChunks`), and in `gemm_pair_mutants.py` `stores_wait_in_branch`, `stores_wait_in_when`,
  `stores_wait_in_loop_from`, `stores_wait_in_peeled_rest`, `stores_wait_in_tile_loop`,
  `store_side_captured_by_owned_tile_loop`, `reader_finished_in_chunk_loop` and the four `onLeader` mutants.
  `forTiles` and `forOwnedTiles` have no client in `encoding/`; their bodies' type is `forPairTiles`'s.
- **M24, register shares** (`encoding/REGISTERS.md`). A warpgroup's register count changes only through its share,
  which only `encoding/Registers.rac` makes and ends:
  - **The pool.** A kernel that changes counts has the CTA's register pool, `RegPool(l, threads, b)`, created by its
    builder (`Registers.pool`) at the budget b of the threads and residency it compiles for, so every warp enters at
    b (A59). It is unrestricted: evidence of b, which the context does not carry.
  - **The split** (`Registers.split`) gives each warpgroup of a 512-thread CTA its `RegShare(l, f, b, count)`, linear, if
    the counts fit the pool: each one `setmaxnreg` takes, and 128 · Σ counts ≤ 512 · b (evidence). So every first
    increase finds the registers the first decreases free.
  - **The emitters** (`Core.withShare`, `Core.regsBack`) need the Key and a share, and print the change its type
    states: from the share's b to its count as the first instruction of warpgroup f's branch, and back to b after the
    split's join, followed by a CTA barrier. A branch holds its share and hands it to the join, so no share reaches
    code before the split or after the way back.
  - **The join** (`Registers.join`) uses the four shares up together. No operation changes a share, so there is no
    change in the middle of a role.
  - **The invariant: outside a split, every warp holds b.** The barrier after the way back makes it so: without it, a
    warpgroup back at b could start a second split and take, by its first increase, registers that another
    warpgroup's increase back still waits for. So a kernel may split any number of times, in sequence, in a loop or
    under a uniform branch. A split needs a `cta(512)` context, so splits never nest in a role.
  Trusted, and reviewed rather than checked (`encoding/REGISTERS.md` §2 and §9):
  - that only a builder creates a pool, with the threads and residency it prints (§7, and §2's carve-out). The
    language seals per file, so `Registers.pool` is a definition any module can call; a pool at another per-thread
    count prints changes from a count the warps do not hold, which the register check refuses;
  - that Core prints no `setmaxnreg` but through `withShare` and `regsBack`. Its raw `asm` statements could.

M18–M20 hold for the CTA pair (`encoding/TWO_CTA.md`, `Core.rac`'s pair sections), M21 and M22 for A3b's correction
warpgroup (`encoding/A3B.md`), M23 for every combinator of `encoding/Core.rac`, and M24 for the register pool of
`encoding/Registers.rac`.

## 6. Operation obligations

Each sealed operation must emit code that establishes what its result types claim, given what its argument types
claim. Types are abbreviated; "code" is what it emits into its `Ctx`.

### 6.1 Values and registers
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `lit`, `zero`, `add`, `mulC`, `divC`, `remC`, `ceilDivC`, `lt`, `fma` | argument values | nothing (pure expressions) | the value's expression, grain (the join of its inputs'), and `bound` (a true exclusive upper bound, forgotten past 2^32) | A18 |
| `reg`, `get`, `set` | a context; for `set` in `encoding/Core.rac`, a register declared inside the innermost `onLeader` arm, if any (else a generation error) | a declaration, read or assignment | a per-thread register of lifetime `l`; `get` is `thread` grain | I1, M18 |

### 6.2 Control
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `loop`, `loopFrom` (encoding) | `Fixed(S)`; unrestricted body | `for (i = start; i < count; ++i) { body }`, `start` 0 for `loop` | the state after ≥ 0 iterations | M5 |
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
| `withRing` | `cta` context; boxes pass `boxOk` | 1024-aligned stages, 2S barriers initialized (count 1) by thread 0, which then arrives once on each `empty[s]`, completing its phase 0, with fence and `__syncthreads`, and at close thread 0's `mbarrier.inval`s | `Producer`, `Consumer`, every stage free; closes only on both `…Done` | A6–A8, A15, I2, I8 |
| `takeProducer`, `takeConsumer` | `Ctx(m, lane)` with `Elected(m)` | the side's stage and phase registers (producer 0/0, consumer 0/0) | `ProducerAt(r, m)` / `ConsumerAt(r, m)`, bound to that thread | M6, A6 |
| `acquire` | `ProducerAt` | wait `empty[stage]` at the producer's phase | `Slot`: the current stage is free (its last reader's commit completed) | A6, A12 |
| `fill` | `Slot`, maps whose boxes are the ring's | `arrive.expect_tx(stage bytes)`, two TMA loads into the stage, advance | the fill is in flight toward `full[stage]` | A9 |
| `finishProducer` | `ProducerAt` | S more waits on `empty`, advancing | every stage was released: no copy in flight, no reader active | A6, A12 |
| `await` | `ConsumerAt` | wait `full[stage]` at the consumer's phase, `after_thread_sync` | `Ready`: the stage's copies landed and are visible, to this thread and to the tensor-core work it issues next | A6, A9, A13 |
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
| `stageAcc` | `Acc(ready)`, `StageFree`, a `ChunkAt(p, cols)` of the accumulator's width, aligned warpgroup | as `stageAccFull` (§6.7), from the accumulator's columns | `StageWritten`, the accumulator still `ready` | A13, A14 |

### 6.7 The output
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `forChunks` | `TileAt` and `TileOwn` of one tile, bn a positive multiple of 32 (else `#error`); `Fixed(S)` | `for (c = 0; c < bn/32; ++c)` | per iteration the chunk's `ChunkAt` (columns `col0 + 32c` on) and a linear `ChunkOwn`: each chunk of the tile once | M5, S5 |
| `withStaging` | `cta` context, bufs > 0 | 4·bufs buffers of 4096 bytes, 1024-byte aligned | `Staging`, `StoreSide`; closes only on `StoreDone`, when no store reads the buffers | I2, A34 |
| `takeStore` | aligned warpgroup `warps(f, 4)` in scope `m` (evidence) | the buffer-index register, 0 | `StoreAt(s, m, f)`: every warp's current buffer free, no store of its lane 0 in flight | M6, A35 |
| `acquireStage` | `StoreAt` | lane 0: `cp.async.bulk.wait_group.read (bufs − 1)`; `__syncwarp` | `StageFree`: the store that last read the current buffer, `bufs` groups back, finished reading, before any thread's next write | A35, A36, A37 |
| `stageAccFull` | `AccFull`, `StageFree`, a `ChunkAt(p, n)` of the buffer's width | `__syncwarp`, `after_thread_sync`, 4 `tcgen05.ld.32x32b.x8`, `wait::ld`, 8 `st.shared.v4.f32` of the thread's row in the 128-byte swizzle | `StageWritten`: the warp's 32 rows of the chunk in the buffer; the loads complete, so the accumulator may be released | A13, A14 |
| `fenceStage` | `StageWritten` | every thread `fence.proxy.async.shared::cta`, `__syncwarp` | `StageFenced`: the writes ordered before any async-proxy read issued after | A36, A37 |
| `storeStage` | `StageFenced`, `ChunkAt` and `ChunkOwn` of one chunk, `CMap` | every lane: the buffer's address and the row `row0 + 32·(warp mod 4)` (the warp index is a full-warp `__shfl_sync`, A1, so never under the lane-0 branch); lane 0: TMA store of the buffer to (`col0`, row), `commit_group`; next buffer | `StoreAt`: one more group, reading the buffer just left; the warp's rows of the chunk written once, clipped to C | A34, A35, S5 |
| `finishStores` | `StoreAt` | lane 0: `cp.async.bulk.wait_group 0`; `__syncwarp` | `StoreDone`: every store of the warpgroup complete, reads and writes | A35, A37, A38 |

In `encoding/Core.rac`, `stageAcc` and `stageAccFull` are each split in two, so that a chunk is loaded before its
staging buffer is waited for and the load does not queue behind the store that last read the buffer:

| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `loadAccChunk`, `loadBufferChunk` | `Acc(ready)` of a region / `AccFull` of a ring's buffer, a `ChunkAt(p, n)` of its width, aligned warpgroup | 32 declarations, `__syncwarp`, `after_thread_sync`, 4 `tcgen05.ld.32x32b.x8` of the warp's lane quadrant from column 32·index, `wait::ld` | `ChunkRegs(k)`: the thread's 32 values, in registers of the block's lifetime; the loads complete, so the accumulator may be released; the `Acc`/`AccFull` handed back | A13, A14 |
| `writeStage` | `StageFree`, `ChunkRegs(k)` of the same block | the row's address in the warp's current buffer, 8 `st.shared.v4.f32` in the 128-byte swizzle | `StageWritten`: the warp's 32 rows of the chunk in the buffer | A37 |

### 6.8 Persistent GEMM
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `tmaGemmPersistentKernel` | a band height G > 0 (else `#error`) | `tilesM`, `tilesN`, `tiles = tilesM·tilesN`, `bandRows = min(tilesM, G)`, `bandTiles = bandRows·tilesN`, all below 2^32 by the launcher's extent checks | `Sched`, `SchedOwn` | A18 |
| `forTiles`, `forOwnedTiles` | `Fixed(S)`; `SchedOwn` for the owned loop | `for (t = blockIdx.x; t < tiles; t += gridDim.x)` (the schedule's start and step), and in the body the tile's origin by the band order (`DESIGN.md` §6) | per iteration a `TileAt`, and for the owned loop a `TileOwn`. **Obligation:** the band order is a bijection from `[0, tiles)` onto the tiles for every M, N and G > 0 (the last band may have fewer rows), so CTAs visit disjoint tiles, and the one owning loop visits each tile once. Argued in `Gpu.tileLoop`; checked exhaustively on the host for grids up to 48×48 tiles and G ≤ 20, and on the GPU by coverage (`harness/gemm_test.cu`) | M5, S5, A18 |
| `withAccRing` | `Acc(empty)`, bufs·n ≤ cols | full (count 1) and empty (count 128) barriers per buffer, thread 0 then arriving with count 128 on each empty barrier, completing its phase 0; `inval` at close | producer and consumer sides; closes on both `…Done`, handing back `Acc(empty)` | A6–A8 |
| `takeAccProducer` / `takeAccConsumer` | an elected lane / an aligned warpgroup | the side's registers (0/0 and 0/0) | the side, bound to that thread or warpgroup | M6 |
| `acquireAcc` | producer side | wait `empty[buf]`, `after_thread_sync` | `AccFree`: the epilogue's loads of the buffer are done | A6, A13 |
| `mmaFirstInto`, `mmaNextInto` | `Ready`, `AccFree` / `AccFilling`; N = n | MMAs into the buffer's columns | `AccFilling` | A11 |
| `commitAcc` | `AccFilling`, `Elected(m)` | `tcgen05.commit` to `full[buf]`, advance | the buffer completes when its MMAs do | A12 |
| `finishAccProducer` | producer side | `bufs` waits on `empty`, advancing | every buffer was read: no tensor-core work in flight | A6 |
| `awaitAcc` | consumer side | wait `full[buf]`, `after_thread_sync` | `AccFull`: the buffer's results are visible | A6, A13 |
| `releaseAcc` | `AccFull` | `before_thread_sync`, 128 arrivals on `empty[buf]`, advance | the buffer is free to the issuer: every chunk's loads completed (`wait::ld` in `stageAccFull`) | A13 |

### 6.9 Kernels
| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `tiledKernel` | a body over `cta(tile²)` | `__launch_bounds__(tile², 1)`; the kernel; no launcher | a `Program` | I1–I7 |
| `tmaGemmKernel`, `tmaGemmPersistentKernel` | a body; boxes pass `gemmShapeOk` | `__launch_bounds__(256, 1)`; the kernel (parameters `A_map`, `B_map`, `C_map`, `M`, `N`, `K`) and its launcher (extent checks, `N mod 4 = 0`, the three map encodings, shared-memory attribute, grid); for `tmaGemmKernel` the CTA's `TileAt` from the block indices and its `TileOwn` | a `Program` | A17, A34, I6 |
| `finish` | the Key; the CTA's threads n and its residency r, as its builder states them | `#error` lines for every generation error | the `Program`, with its bounds (n, r) | — |
| `render` | a `Program`; `Check.WellFormed` of its kernel, discharged by evaluating the checkers | `__launch_bounds__(n, r)` of the `Program`; the printed kernel | no generation error; I1–I6 as far as the AST shows them; a thread's registers within `Registers.budget(n, r)`, so the kernel never fails to launch for lack of them | the printer, `gpu/Check.rac` |

### 6.10 The attention core

The operations `gpu/encoding/Core.rac` adds to `Gpu.rac`'s (`ATTENTION.md` §3, §4.2), as built for A1, A2 and paged
attention (`encoding/PAGED.md`). Its other operations are `Gpu.rac`'s, with the obligations of §6.1–§6.9, except for
two things.
- Every use of a tensor-memory region's address goes through `tmemBase` (the allocation's address plus the region's
  offset): `mmaFirst`, `mmaNext`, `loadAccChunk`, `withAccRing` (and through its buffers `mmaFirstInto`, `mmaNextInto`,
  `loadBufferChunk`, `eachChunk` and `writeP`) and `withExchange` address the region they are given, not column 0; only
  `withTmem`'s deallocation names the allocation's address.
- No protocol closes on a `…Done` token (M15). `withRing`, `withAccRing`, `withExchange` and `withStaging` take a callback
  that returns the emitter and its result only. Their sides are linear and belong to the opener's scope, which the
  result's type cannot name, so the callback uses every side up before the close (`docs/SCOPE_CONTAINMENT.md`), and
  the one operation per side that uses it up without handing it on is its finisher. `finishProducer`,
  `finishAccProducer` and `finishStores` emit §6.5, §6.8 and §6.7's waits and return the emitter; `finishExWriter`
  waits and gives `OFinal`, which `closeExWriter` ends; `finishConsumer`, `finishAccConsumer`, `finishExReader` and
  `closeExWriter` emit nothing, since everything their side issued is released to the waiting side. So each close
  still follows the drain that §6.5–§6.8 tie to their `…Done` tokens, by the obligation that every other operation
  taking a side gives a side back (§7).

| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `fadd`, `fsub`, `fmul`, `fmax`, `select` | argument values | nothing (pure expressions; `fmax` prints CUDA's `max(float, float)`) | the value, grain the join of its inputs' | — |
| `fconst`, `ex2`, `lg2`, `rcp` | a context, any group; `fconst`: bits < 2³² (else a generation error) | a declaration and one instruction (`mov.b32`, `ex2.approx.ftz.f32`, `lg2.approx.ftz.f32`, `rcp.rn.f32`) | the value, grain of the input (`fconst` uniform) | A26 |
| `splitTmem` | `Acc(a, empty)` of a `Tmem(a, cols)`, `cta` context; 0 < k < cols and 64 ∣ k (else a generation error) | nothing | regions `Tmem(b, k)` at the region's offset and `Tmem(c, cols − k)` at offset + k, in fresh scopes, with an `Acc(empty)` each; closes on both `Acc`s, handing back `Acc(a, empty)` | A27, S4 |
| `holdStage` | `Ready(r, m)` | nothing | `ReadyUsed(r, m)`: the stage stays unreleased until `releaseByMma` | A12 |
| `mmaScores` | `ReadyUsed(ra, m)`, `Ready(rb, m)`, `AccFree(q, m)` of an `AccRing(q, 128)`, `Elected(m)`; both rings' stages two 64 × 128 boxes (else a generation error) | 8 `tcgen05.mma` (two box pairs, four K = 16 steps each) from K-major descriptors into the producer's current buffer, the first overwriting | `ReadyUsed` of both, `AccFilling` | A11 |
| `eachChunk` | `AccFull(q, m, f)` (an aligned warpgroup's), `warps(f, 4)` context, a step | per chunk c < n / 8, in order: 8 declarations, `__syncwarp`, `tcgen05.ld.32x32b.x8` at column 8c of the consumer's current buffer in the warp's lane quadrant, `wait::ld`; then the step's code; no fence, since `awaitAcc` fenced in every thread of the warpgroup | each step is handed the thread's row, columns 8c–8c+7, as thread-grain values of the context's lifetime; `AccFull` kept | A13, A14, M12 |
| `withExchange` | `Acc(a, empty)` of a `Tmem(a, 256)`, `cta` context | P full (count 128) and P empty (count 1), thread 0 completing P empty's phase 0 with one arrival at initialization; `inval` at close | the `Exchange` (Ô at the region's column 0, P at 128), `ExWriter`, `ExReader`, linear and of the exchange's scope, so finished before the close; hands back `Acc(a, empty)` | A6–A8 |
| `takeExWriter` | `warps(f, 4)` context, f mod 4 = 0 (evidence) | the writer's phase register, 0 | `ExWriterAt(x, m, f, fresh)`, bound to that warpgroup | M6 |
| `takeExReader` | `Ctx(m, lane)` with `Elected(m)` | the reader's phase register, 0 | `ExReaderAt(x, m, fresh)`, bound to that thread | M6 |
| `acquireP` | `ExWriterAt(x, m, f, o)` | wait P empty at the writer's phase, `after_thread_sync` | `PFree(x, m, f, o, 0)`: the last product completed, P and Ô quiescent and visible | A6, A13, A21 |
| `writeP` | `AccFull(q, m, f)` of an `AccRing(q, 128)`, `PFree(…, 0)`, `warps(f, 4)` context, a step returning eight f32 values | per chunk c < 16, in order: S's chunk c loaded as by `eachChunk`; the step's code; 4 u32 declarations, 4 `cvt.rn.bf16x2.f32` of the step's values (pairs 2i+1, 2i, so element 2i is in the low half), `__syncwarp`, `tcgen05.st.32x32b.x4` at P's column 4c in the warp's lane quadrant | `PFree(…, 16)`: every chunk of the thread's row of P written once, in order (pending `wait::st`); `AccFull` kept | A13, A14, A19, A23, A25, M12, M14 |
| `rescaleO` | `PFree(…, o, c)`, an f32 value | `held`: the value's declaration; 16 × (8 declarations, `__syncwarp`, `tcgen05.ld.32x32b.x8`, `wait::ld`, `tcgen05.st.32x32b.x8` of the 8 products) over Ô in the warp's lane quadrant. `fresh`: nothing, since Ô holds nothing until the first product overwrites it | the thread's row of Ô scaled (pending `wait::st`); `PFree` unchanged | A14, A19, A22, M12 |
| `publishP` | `PFree(…, 16)` | `__syncwarp`, `wait::st`, `before_thread_sync`, one arrival per thread (128) on P full, flip the writer's phase | `ExWriterAt(…, held)`: P and Ô handed to the reader | A19, A20, M13, M14 |
| `awaitP` | `ExReaderAt(x, m, o)` | wait P full at the reader's phase, `after_thread_sync` | `PReady(x, m, o)`: P and Ô written and visible to the tensor cores | A6, A20, M13 |
| `mmaPV` | `PReady(x, m, o)`, `Ready(r, m)` of a ring whose stages are two 64 × 128 boxes (else a generation error), `Elected(m)` | 8 `tcgen05.mma` with D at Ô, A in tensor memory at P + 8s, B the stage MN-major (transpose-B, LBO the box's 16384 bytes, SBO 1024, 2048 bytes a step); the first overwriting when `o` is `fresh`, accumulating when `held` | `PUsed(x, m)`, `ReadyUsed(r, m)` | A23, A24 |
| `commitPV` | `PUsed(x, m)`, `Elected(m)` | `tcgen05.commit` to P empty, flip the reader's phase | `ExReaderAt(x, m, held)`; the buffer returns to the writer when the products complete | A12, A21 |
| `finishExWriter` | `ExWriterAt(…, held)` | wait P empty at the writer's phase, `after_thread_sync` | `OFinal`: every product completed, none in flight, Ô visible | A6, A13, A21 |
| `closeExWriter`, `finishExReader` | `OFinal` / `ExReaderAt(…, held)` | nothing | the side used up | — |
| `maskedScores` | `warps(f, 4)` context (converged: its causal form runs warp collectives), a `Mask(L)` (sealed: only the builders make one), a block index (any value), c < 16 (else a generation error), eight f32 values | `kv0 = 128 · block + 8c`; the limit: `seq`, or (causal) `__syncwarp`, the row `q + 1` with `q` the mask's row (`128 · blockIdx.x + 32 · (warp mod 4) + lane` for one tile, `256 · blockIdx.x + 32 · warp + lane` for two) declared before `min(seq, q + 1)`; 8 declarations `(kv0 + j < limit) ? v_j : −∞` (the builder's −∞) | the masked scores, thread grain, of the context's lifetime; no protocol state, and no branch, so the group stays converged | M3, M12 |
| `storeO` | `OFinal(x, m, f)`, `OOwn(L, t, f)` and `AttnOut(L, t)` (t f32 or bf16, which only the builders choose), `warps(f, 4)` context, two f32 values | `__syncwarp`, `after_thread_sync`; declarations of the thread's row `r`, the `AttnOut`'s (as `maskedScores`', or a decode CTA's `32 · (warp mod 4) + lane`), its row of O, `first + r` with `first` the `AttnOut`'s (`blockIdx.y · seq`, or a decode CTA's `blockIdx.x · B · H · G + blockIdx.y · G`), the guard `r < seq` (G for a decode CTA), and copies of the two values; 16 × (8 declarations, `__syncwarp`, `ld.x8`, `wait::ld`, 8 guarded stores of Ô · inv, a decode CTA's as 0 where its split is empty, each through `static_cast<__nv_bfloat16>` for bf16, round to nearest even); the guarded LSE store; `before_thread_sync` | the CTA's rows of O and LSE written once (`OOwn` consumed): rows of a last query tile past `seq`, and a decode CTA's rows past G, are never stored; distinct CTAs' rows are distinct; `OFinal` kept | A13, A14, M12, S5 |
| `fillBlock` | as `fill`; one `HeadMap` of the ring's first box; a ring whose stages are two 64 × 128 boxes (else a generation error); a row | `arrive.expect_tx`, two TMA loads through the map at columns 0 and 64 of row `blockIdx.y · seq` plus the caller's (rank-2 maps over `[BH·seq, 128]`, `encoding/README.md`) | as `fill`; both halves of the stage from one map and one row | A9 |
| `attentionKernel` | a body; causal or not; O's type t, f32 or bf16 (else a generation error) | `__launch_bounds__(256, 1)`; `blocks = ceil(seq / 128)`, or `min(ceil(seq / 128), blockIdx.x + 1)` causal, once; −∞, once; the kernel (parameters `Q_map`, `K_map`, `V_map`, `O` of t, `LSE`, `BH`, `seq`, `scale_log2`) and its launcher (refusing seq = 0, BH = 0, BH ≥ 65536, BH · seq · 128 ≥ 2³¹, rows ≠ BH · seq, dim ≠ 128; three rank-2 encodings over `rows` × `dim` with 64 × 128 boxes; grid (ceil(seq / 128), BH) of 256 threads) | `AttnLaunch` (the maps, `AttnOut`, the `Mask`, seq, blocks, the query block's first row, `scale_log2`), `OOwn`, `TmemPermit`; a `Program` | A17, I6 |
| `fillPage` | as `fill`; a ring whose stages are two 64 × 128 boxes (else a generation error); `PageTable`, `PageMap` of the ring's first box; a block index `j` | a guarded read of `block_table[b][j]` (`b = blockIdx.y / H`; 0 outside the table), `arrive.expect_tx`, two TMA loads at row `p · 128`, columns `(blockIdx.y mod H) · 128` and 64 more (the cache `[pages · 128, H · 128]`) | as `fill`; whatever the table holds, the loads read only the cache or zeros (`PAGED.md` §3) | A9 |
| `pagedAttentionKernel` | as `attentionKernel`, and 1 ≤ H ≤ 65535 | `__launch_bounds__(256, 1)`; as `attentionKernel`, with parameters `Q_map`, `K_map`, `V_map`, `O`, `LSE`, `block_table`, `B`, `seq`, `max_pages`, `scale_log2`, and a launcher refusing seq = 0, B = 0, B · H ≥ 65536, B · H · seq · 128 ≥ 2³¹, rows_q ≠ B · H · seq, dim ≠ 128, max_pages < ceil(seq / 128), B · max_pages ≥ 2³¹, pages · 128 ≥ 2³¹, rows_kv ≠ pages · 128, cols_kv ≠ H · 128; grid (ceil(seq / 128), B · H) | `PagedLaunch` (as `AttnLaunch`, with `PageMap`s for K and V and the `PageTable`), `OOwn`, `TmemPermit`; a `Program` | A17, I6 |
| `withScoreBuffer` | `Acc(a, empty)` of a `Tmem(a, 256)`, `cta` context | S full (count 1) and P full (count 128), no phase completed at initialization; `inval` at close | the `ScoreBuffer` (S at the region's column 0, P at 64, Ô at 128), `RowSide`, `MmaSide`, linear and of the buffer's scope, so finished before the close; hands back `Acc(a, empty)` | A6–A8 |
| `takeRows` | `warps(f, 4)` context, f mod 4 = 0 (evidence) | the warpgroup's phase register, 0; of a buffer with a correction warpgroup, also the α ring's sending phase register, 0 | `RowsAt(x, m, f, fresh)`, bound to that warpgroup | M6 |
| `takeMma` | `Ctx(m, lane)` with `Elected(m)` | the MMA thread's phase register, 0 | `Holding(x, m)`, bound to that thread: the buffer is the MMA thread's, nothing issued | M6 |
| `awaitScores` | `RowsAt(x, m, f, o)` | wait S full at the warpgroup's phase, `after_thread_sync`, flip the phase | `Scored(x, m, f, o)`: the block's S complete and visible; the product before it complete, so Ô quiescent | A6, A12, A13 |
| `loadRow` | `Scored(x, m, f, o)`, `warps(f, 4)` context | 128 declarations, `__syncwarp`, 16 × `tcgen05.ld.32x32b.x8` at S's columns 8c in the warp's lane quadrant, one `wait::ld` | `Read(x, m, f, o)`: every load of S complete; the row as a `Row` of 16 chunks, thread-grain values of the context's lifetime | A13, A14, M12, M16 |
| `mapRow` | a `Row(k)`, a context of lifetime `k`, a step | the step's code per chunk, in order | the `Row` of the step's results, 16 chunks | — |
| `writeProbs` | `Loaded(x, m, f, o)`, a `Row(k)`, `warps(f, 4)` context, a step returning eight f32 values | per chunk c < 16, in order: the step's code; 4 u32 declarations, 4 `cvt.rn.bf16x2.f32`, `__syncwarp`, `tcgen05.st.32x32b.x4` at P's column 4c (S's 64 + 4c) in the warp's lane quadrant | `Probs(x, m, f, o)`: every chunk of the thread's row of P written once, in order (pending `wait::st`) | A19, A23, A25, M12, M14, M16 |
| `rescaleRow` | `Probs(x, m, f, o)` of a buffer whose rescaler is the softmax warpgroup, an f32 value | `held`: as `rescaleO`, over Ô at column 128. `fresh`: `__syncwarp`, 16 × `tcgen05.st.32x32b.x8` of 0 over Ô | `Probs(x, m, f, held)`: the thread's row of Ô scaled, or set to 0 (pending `wait::st`) | A14, A19, A22, M12 |
| `publishProbs` | `Probs(x, m, f, held)` of a buffer whose rescaler is the softmax warpgroup | `__syncwarp`, `wait::st`, `before_thread_sync`, one arrival per thread (128) on P full | `RowsAt(x, m, f, held)`: P and Ô handed to the MMA thread, and the row's loads ordered before its next writes | A19, A20, M13 |
| `awaitFinal` | `RowsAt(x, m, f, held)` | wait S full at the warpgroup's phase, `after_thread_sync` | `Final(x, m, f)`: the last product complete, none in flight, Ô visible | A6, A12, A13 |
| `storeFinal` | `Final(x, m, f)`, `OOwn(L, t, f)`, `AttnOut(L, t)`, `warps(f, 4)` context, two f32 values | as `storeO`, from Ô at the buffer's column 128 | as `storeO`; `Final` kept | A13, A14, M12, S5 |
| `closeRows`, `finishMma` | `Final` / `MmaAt(x, m)` | nothing | the side used up | — |
| `issueScores` | `Holding(x, m)`, `ReadyUsed(ra, m)`, `ReadyUsed(rb, m)`, `Elected(m)`; both rings' stages two 64 × 128 boxes (else a generation error) | 8 `tcgen05.mma` from K-major descriptors into S (the buffer's columns 0–127), the first overwriting | `Holding(x, m)`, `ReadyUsed` of both | A11, A33, M16 |
| `awaitProbs` | `MmaAt(x, m)` | wait P full at the MMA thread's phase, `after_thread_sync`, flip the phase | `Published(x, m)`: P and Ô written and visible to the tensor cores | A6, A20, M13 |
| `issuePV` | `Published(x, m)`, `ReadyUsed(r, m)` of a ring whose stages are two 64 × 128 boxes (else a generation error), `Elected(m)` | 8 `tcgen05.mma` with D at Ô (column 128), A in tensor memory at P (column 64) + 8s, B the stage MN-major, every one accumulating | `Holding(x, m)`, `ReadyUsed(r, m)` | A23, A24, A39 |
| `commitBuffer` | `Holding(x, m)`, `Elected(m)` | `tcgen05.commit` to S full | `MmaAt(x, m)`; the buffer passes to the warpgroup when the thread's work completes | A12, A21 |
| `pairAttentionKernel` | as `attentionKernel` | `__launch_bounds__(384, 1)`; as `attentionKernel`, with `blocks = ceil(seq / 128)`, or `min(ceil(seq / 128), 2 · blockIdx.x + 2)` causal, and a launcher with grid (ceil(seq / 256), BH) of 384 threads, refusing as `attentionKernel`'s | `PairLaunch` (as `AttnLaunch`, with `q0 = 256 · blockIdx.x` and `q1 = q0 + 128`) and the mask's and output's row `256 · blockIdx.x + 32 · warp + lane`, `OOwn(l, t, 0)` and `OOwn(l, t, 4)`, `TmemPermit`; a `Program` | A17, I6 |

The rows of `maskedScores` and `storeO` (and so `storeFinal`) are the `Mask`'s and the `AttnOut`'s, which only the
builders make: `rowInHead` for a CTA of one tile, `rowInPairCta` for A3a's and A3b's two. `attentionKernel` and
`pagedAttentionKernel` hand `OOwn(l, t, 4)`.

Rank-3 encodings in `fillBlock` and `attentionKernel` (`ATTENTION.md` §3.7, A28) are not built: A2 keeps rank-2 maps,
masking the part of a last key block past `seq` and never storing the rows of a last query tile past it
(`encoding/README.md`).

### 6.11 Paged decode

The operations of `encoding/P2.md`'s three kernels (`Core.rac`'s paged-decode section). The decode CTA runs A2's roles
and operations, with the rows `storeO` takes from its `AttnOut`. The append and combine kernels are one warp per CTA
(`warpCta`), so a value the same in every lane of the warp is uniform.

| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `fillGroup` | as `fill`; a ring whose stages are two 64 × 128 boxes (else a generation error); a `GroupMap` of `group` rows | `arrive.expect_tx(2 · group · 128)`, two TMA loads of `group` rows at row `blockIdx.y · group`, columns 0 and 64, into the stage's two halves | as `fill`; the stage's first `group` rows of each half hold the CTA's queries, the others are never loaded | A9, A40 |
| `decodeKernel` | a body; 1 ≤ H ≤ 65535, 1 ≤ G ≤ 128 (else a generation error) | `__launch_bounds__(256, 1)`; the prologue, once, before the roles: `b = blockIdx.y / H`, `len = lens[b]`, `n = len / 128 + 1`, `c = ceil(n / gridDim.x)`, `first = blockIdx.x · c`, `end = min(n, first + c)`, `nonEmpty = first < end`, `count = nonEmpty ? end − first : 1`, the split's keys `nonEmpty ? (len − 128 · first) + 1 : 0`; −∞; the kernel (parameters `Q_map`, `K_map`, `V_map`, `Opart`, `LSEpart`, `block_table`, `lens`, `B`, `max_pages`, `scale_log2`) and its launcher (refusing B = 0, B · H ≥ 65536, splits = 0, splits · B · H · G · 128 ≥ 2³¹, rows_q ≠ B · H · G, dim ≠ 128, B · max_pages ≥ 2³¹, and the cache's pages · 128 ≥ 2³¹, rows_kv ≠ pages · 128, cols_kv ≠ H · 128; Q's map with 64 × G boxes; grid (splits, B · H) of 256 threads) | `DecodeLaunch`: the `GroupMap`, the `PageMap`s, the `PageTable`, the `AttnOut` of the CTA's G rows of the partials (from `blockIdx.x · B · H · G + blockIdx.y · G`, O kept where `nonEmpty`), A2's non-causal `Mask` with the split's keys as its limit, `count` and `first` (uniform, M10), `scale_log2`; `OOwn`, `TmemPermit`; a `Program`. Every role runs `count ≥ 1` blocks | A17, I6, M10, M11 |
| `withClaim` | `ClaimOwn(L)` (linear: one claim per warp), `Lengths`, `PageTable`, `Claims`, a `warpCta` context, an unrestricted arm that returns the emitter alone | every lane: `b = blockIdx.x / H`, the flag and the row registers, 0. Lane 0: `pos = lens[b]`, `p` = table entry `[b][pos / 128]` if `pos / 128 < max_pages`, else `pages`; if `p < pages`: the row `128p + pos mod 128`, `mine = epoch · 2³² + b`, `cur` by `ld.relaxed.gpu.global.b64` of word `p · H + blockIdx.x mod H`; if `cur`'s epoch is `epoch`, the flag `cur = mine`, else the flag `atom.relaxed.gpu.global.cas.b64(word, cur, mine) = cur`. Every lane: `__syncwarp`; the flag and the row broadcast from lane 0 by `shfl.sync.idx`; `if (0 < flag) { arm }`; lane 0 stores the flag at `appended[blockIdx.x]` | the arm runs, on the whole warp, only where this warp's claim of `(p, h)` holds, with `Claimed(m)` of lane 0's row and a linear `AppendOwn(m)`, both of the arm's scope; at most one warp's claim of a word holds in a launch | A41, A42, M17 |
| `appendRow` | `Claimed(m)`, `AppendOwn(m)` (linear, used up), `PagedCache`, `NewKV`, a `warpCta` context | each lane: 8 copies of `k_new[blockIdx.x · 128 + 8 · lane + j]` to K at the claim's row, column `(blockIdx.x mod H) · 128 + 8 · lane + j` (64-bit index), and of V likewise | the warp writes, once, only the row its claim holds, each lane its own 8 columns of it; the row lies inside the cache (`p < pages`) | M17 |
| `appendKernel` | a body; 1 ≤ H ≤ 65535 (else a generation error) | `__launch_bounds__(32, 32)` (`warpResidency`); the kernel (parameters `K`, `V`, `k_new`, `v_new`, `lens`, `block_table`, `owners`, `appended`, `max_pages`, `pages`, `epoch`) and its launcher (refusing B = 0, epoch = 0, B · H · 128 ≥ 2³¹, pages · 128 ≥ 2³¹, pages · H ≥ 2³¹, B · max_pages ≥ 2³¹; grid (B · H) of 32 threads) | `AppendLaunch`, one `ClaimOwn` per warp; a `Program` | A17, I6 |
| `splitLse`, `splitRow` | `Partials`, a split index `s` (any value) | `s < splits ? LSEpart[s · rows + blockIdx.x] : 0`; the lane's 4 columns `s < splits ? Opart[(s · rows + blockIdx.x) · 128 + 4 · lane + j] : 0` | the values, `s`'s grain for the LSE (one address, of an input), thread grain for the row; every read inside the partials | M10 |
| `storeCombined` | `CombinedOwn(L)` (linear), `Combined`, a `warpCta` context, four f32 values and one | each lane: 4 stores of `O[blockIdx.x · 128 + 4 · lane + j]` as bf16; lane 0: `LSE[blockIdx.x]` | the warp's row of O and LSE written once, each element by one lane | S5 |
| `combineKernel` | a body | `__launch_bounds__(32, 32)` (`warpResidency`); the kernel (parameters `Opart`, `LSEpart`, `O`, `LSE`, `rows`, `splits`) and its launcher (refusing rows = 0, splits = 0, splits · rows · 128 ≥ 2³¹; grid (rows) of 32 threads) | `CombineLaunch` (the partials, the output, `splits`), one `CombinedOwn` per warp; a `Program` | A17, I6 |

### 6.12 CTA pairs

The pair kernel's operations (`encoding/TWO_CTA.md`). A pair ring's sides are the ring's (`Producer`, `Consumer`,
`ProducerAt`, `Slot`, `ConsumerAt`, `Ready`, `ReadyUsed`), and a pair accumulator ring's the accumulator ring's; their
operations take the `PairRing` or `PairAccRing`, which only the pair openers make, and which no single-CTA operation
takes. Where a pair operation differs from a single-CTA one only in what the CTA group prints, it runs the single-CTA
one: in a pair kernel every wait is `try_wait.parity.acquire.cluster` and every commit multicast to both CTAs.

The persistent pair GEMM's epilogue runs the TMA-store operations of §6.7 (`withStaging`, `takeStore`, `acquireStage`,
`writeStage`, `fenceStage`, `storeStage`, `finishStores`) unchanged. A CTA's staging buffers, stores and bulk
async-groups are its own (`.shared::cta`), so `withStaging` emits no barrier and does not refuse in a pair kernel. Each
CTA finishes its own storing side: `finishStores` runs in code both CTAs run, since an `onLeader` arm cannot capture the
side (M20). The warpgroup releases a tile's accumulator after its chunk loop (`releasePairAcc`): every chunk's loads
have completed (`wait::ld` in `loadPairChunk`), and the stores still in flight read the staging buffers only.

| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `pairGemmKernel` | a body; boxes pass `pairGemmShapeOk` (else a generation error) | `__launch_bounds__(256, 1)`; `__cluster_dims__(2, 1, 1)`; the CTA group `two`; `%cluster_ctarank` and `%clusterid.x` read once; the kernel (parameters `A_map`, `B_map`, `C`, `M`, `N`, `K`) and its launcher (M·N < 2³², M, N, K < 2³¹, the two map encodings, grid `pairs(ceil(N / 2bh), ceil(M / 256))` of 256 threads, at least `pairShared` bytes of shared memory) | `PairGemm` (the maps, the `PairTile`: rows `256·blockIdx.y + 128·rank`, B's rows `col0 + bh·rank`, `col0 = 2bh·clusterid.x`, of width 2bh in its type; `PairOut`, K), `HalfOwn`, `CtaPair`, `TmemPermit`; a `Program` | A17, A43, A56, I6 |
| `onLeader` | a `CtaPair`; sides `S` with `LeaderOnly(S)`; an unrestricted arm, which writes no outer register | `if (rank == 0) { body }` | the body ran in the leader only, with a `Leader(m)` of the arm's scope, and used up the sides there; no linear value used up in one CTA only but the leader-only sides | M20 |
| `withPairTmem` | the kernel's `Ctx(l, cta)` and `CtaPair(l)`, `TmemPermit` | as `withTmem` with 512 columns and `cta_group::2`; at close `before_thread_sync`, a cluster barrier, `after_thread_sync`, warp 0's dealloc | `Tmem(a, 512)`, `Acc(a, empty)`; closes on `Acc(done)` | A44, A50, M19 |
| `withPairRing` | the kernel's `Ctx(l, cta)` and `CtaPair(l)`; boxes pass `boxOk` | `withRing`'s layout, inits and setup arrivals, the fence, a cluster barrier; at close a cluster barrier, then thread 0's `inval`s | `PairRing`, `Producer`, `Consumer`, every stage free in both CTAs | A44, A45, M19 |
| `takePairProducer`, `acquirePair` | as `takeProducer`, `acquire` | as theirs, the wait at cluster scope | `ProducerAt`, `Slot`: this CTA's half of the stage free (the leader's commit completed) | A49 |
| `fillPair` | `Slot`, the `PairTile`, maps of the ring's boxes, a K coordinate | `mapa` of `full[s]` to the leader's; in the leader `arrive.expect_tx` of both halves' bytes; two `::2` TMA loads into this CTA's half at the tile's rows for this rank, completing on the leader's `full[s]`; advance | this CTA's half in flight toward the leader's `full[s]` | A46, A47 |
| `finishPairProducer` | `ProducerAt` | S waits on this CTA's `empty`, advancing | every stage of this CTA's half released: no copy in flight, no MMA reading it | A49 |
| `takePairConsumer` | as `takeConsumer`, and a `Leader` | as `takeConsumer` | `ConsumerAt`, in the leader | M20 |
| `awaitPair` | `ConsumerAt` | wait the leader's `full[s]`, `after_thread_sync` | `Ready`: both halves landed and visible to the tensor-core work issued next | A47, A53 |
| `mmaPairFirst`, `mmaPairNext` | `Ready`, `AccFree`/`AccFilling` of a `PairAccRing(q, n)`; shape passes `pairMmaShapeOk` (else a generation error) | four `tcgen05.mma.cta_group::2` of M = 256, N = n from the stage's descriptors into the buffer, the first overwriting | `ReadyUsed`, `AccFilling` | A48, A51 |
| `releasePair` | `ReadyUsed` | a commit to `empty[s]` multicast to both CTAs; advance | the stage is released in both CTAs when the thread's MMAs reading it complete | A49, A53 |
| `withPairAccRing` | the kernel's `Ctx(l, cta)` and `CtaPair(l)`, `Acc(a, empty)` of a `Tmem(a, cols)`, bufs·n ≤ cols | `withAccRing`'s layout with `empty[b]` of count 256, completed at setup; the fence, a cluster barrier; at close a cluster barrier, then `inval`s | `PairAccRing`, `AccProducer`, `AccConsumer`; hands back `Acc(a, empty)` | A44, A45, M19 |
| `takePairAccProducer`, `acquirePairAcc` | an elected lane and a `Leader` / the issuing side | the side's registers / wait the leader's `empty[b]`, `after_thread_sync` | `AccProducerAt`, in the leader / `AccFree`: both warpgroups' loads of the buffer done | A46, A52, M20 |
| `commitPairAcc` | `AccFilling` | a commit to `full[b]` multicast to both CTAs; advance | the buffer passes to both warpgroups when its MMAs complete | A49 |
| `finishPairAccProducer` | the issuing side | `bufs` waits on the leader's `empty`, advancing | every buffer read by both warpgroups: no tensor-core work in flight | A46 |
| `takePairAccConsumer`, `awaitPairAcc` | an aligned warpgroup / the reading side | the side's registers / wait this CTA's `full[b]`, `after_thread_sync` | `AccConsumerAt` / `AccFull`: this CTA's rows of the buffer visible | A49, A52 |
| `storeHalf` | `AccFull` of a buffer of n columns, a `PairTile` of width n, `PairOut`, `HalfOwn`; n a multiple of 8 (else a generation error) | `__syncwarp`; the row `rows + 32·(warp mod 4) + lane` and `row < M`; a loop over n/8 chunks: 8 declarations, `__syncwarp`, `tcgen05.ld.32x32b.x8`, `wait::ld`, 8 stores guarded by `row < M` and `col < N` | this CTA's half of the tile written once (`HalfOwn` consumed); `AccFull` kept | A14, A54, M12, S5 |
| `releasePairAcc` | `AccFull` | `before_thread_sync`; `mapa` of `empty[b]` to the leader's; one remote arrive per thread; advance | the buffer is free to the issuer once both warpgroups (256) arrived | A46, A52 |
| `pairGemmPersistentKernel` | a body; a band height G > 0, boxes passing `pairGemmShapeOk` (else a generation error) | `__launch_bounds__(256, 1)`; `__cluster_dims__(2, 1, 1)`; the CTA group `two`; `%cluster_ctarank`, `%clusterid.x` and `%nclusterid.x` read once; the schedule's counts for tiles of 256 × 2bh (`tilesN`, `tilesM`, `tiles`, `bandRows`, `bandTiles`, as `tmaGemmPersistentKernel`'s); the kernel (parameters `A_map`, `B_map`, `C_map`, `M`, `N`, `K`) and its launcher (`tmaGemmLauncher`'s requirements and three maps, so N mod 4 = 0; grid `2·min(SMs/2, tiles)` × 1 of 256 threads; at least `pairShared` bytes of shared memory) | `TmaGemm`, `PairSched` (the schedule from `%clusterid.x` in steps of `%nclusterid.x`, and the kernel's pair), `PairSchedOwn`, `CtaPair`, `TmemPermit`; a `Program` | A17, A43, A56, A60, I6 |
| `forPairTiles`, `forOwnedPairTiles` | a `PairSched`, `Fixed(S)`; a `PairSchedOwn` for the owned loop | `for (t = clusterid.x; t < tiles; t += nclusterid.x)`, and in the body the tile's origin by the band order | per iteration this CTA's `PairTile` of the tile (rows `row0 + 128·rank`, B's rows `col0 + bh·rank`, width 2bh), and for the owned loop a `HalfOwn`. The band order is §6.8's bijection, and the pairs' sequences partition the tile indices (A60), so the one owning loop visits each tile once per CTA, and the two CTAs of a pair the same tiles | M5, M18, S5, A60 |
| `forHalfChunks` | a `PairTile` of width w and its `HalfOwn`; `Fixed(S)` | `for (c = 0; c < w/32; ++c)` | per iteration the chunk's `ChunkAt(p, w)` (rows from the tile's `rows`, this CTA's; columns `col0 + 32c` on) and a linear `ChunkOwn`: each chunk of this CTA's half of the tile once | M5, M12, S5 |
| `loadPairChunk` | as `loadBufferChunk`, of a `PairAccRing` | as `loadBufferChunk`, from this CTA's lanes of the current buffer | as `loadBufferChunk` | A13, A14, A54 |

### 6.13 The correction warpgroup

The operations of A3b's correction warpgroup (`encoding/A3B.md`, `Core.rac`'s correction-warpgroup section): a score
buffer whose Ô a correction warpgroup rescales, the α ring inside it, `warpwise` (M21), and the register split. The
score buffer's other operations are §6.10's, with `rescaleRow` and `publishProbs` refused on such a buffer.

| Operation | Requires | Emits | Establishes | Relies on |
|---|---|---|---|---|
| `withCorrectedBuffer` (`openScoreBuffer`, which `withScoreBuffer` also runs) | `Acc(a, empty)` of a `Tmem(a, 256)`, `cta` context | as `withScoreBuffer`, with P full of count 256; the α ring: a full and an empty barrier of count 128, thread 0 completing the empty one's phase 0 with 128 arrivals at initialization, then one slot of 128 f32; `inval` of the four barriers at close | the `ScoreBuffer(x, correction)`, `RowSide`, `MmaSide`, `CorrectionSide`, linear and of the buffer's scope; hands back `Acc(a, empty)` | A6–A8 |
| `publishAlpha` | `Probs(x, m, f, o)` of a buffer whose rescaler is the correction warpgroup, `warps(f, 4)` context, an f32 value | `held`: wait the α ring's empty barrier at the sending phase, store the value at element `threadIdx.x mod 128` of the slot, arrive on the full barrier, flip the phase; `fresh`: none of these. Then `__syncwarp`, `wait::st`, `before_thread_sync`, one arrival on P full | `RowsAt(x, m, f, held)`: P handed to the MMA thread; the block's α handed to the correction warpgroup after the warpgroup observed the block's scores | A6, A19, A20, A57, M13, M22 |
| `takeCorrection` | `warps(f, 4)` context, f mod 4 = 0 (evidence), `CorrectionSide(x)` | the α ring's receiving phase register, 0 | `CorrectAt(x, m, f, fresh)`, bound to that warpgroup | M6 |
| `zeroQuadrants` | `CorrectAt(x, m, f, fresh)`; a context of group `warps(f, 4)` or `warpwise(f, 4)` (`ownQuadrants`, evidence) | `__syncwarp`, 16 × `tcgen05.st.32x32b.x8` of 0 over Ô in the warp's lane quadrant | `Rescaling(x, m, f)`: Ô set to 0 (pending `wait::st`); no product has touched it | A19, M12, M21 |
| `awaitAlpha` | `CorrectAt(x, m, f, held)`, `warps(f, 4)` context | wait the α ring's full barrier at the receiving phase, `after_thread_sync`, a declaration of element `threadIdx.x mod 128` of the slot, arrive on the empty barrier, flip the phase | `Rescaling(x, m, f)`: the product before the block's scores complete, ordered before the warpgroup's next `tcgen05` operations; the row's α, thread grain | A6, A13, A57, M22 |
| `rescaleQuadrant` | `Rescaling(x, m, f)`; a context of group `warps(f, 4)` or `warpwise(f, 4)` (`ownQuadrants`, evidence); an f32 value | as `rescaleO`'s `held` case, over Ô (the buffer's column 128) in the warp's lane quadrant | `Rescaling(x, m, f)`: the running warps' rows of Ô scaled (pending `wait::st`) | A14, A19, A22, M12, M21 |
| `publishRescaled` | `Rescaling(x, m, f)`, `warps(f, 4)` context | `__syncwarp`, `wait::st`, `before_thread_sync`, one arrival on P full | `CorrectAt(x, m, f, held)`: Ô handed to the MMA thread | A19, A20, M13 |
| `finishCorrection` | `CorrectAt(x, m, f, held)` | nothing | the side used up | — |
| `voteAny` | `warps(f, c)` context, a bool value | a u32 declaration and `vote.sync.any.pred` with a full mask of the value | a bool of grain `warp`: whether the value holds in any lane of the warp | A4, A31, M10 |
| `ex2emu` | a context, any group; an f32 value x < 128 (its domain; not checked) | a declaration and one `asm` of `max.f32`, `add.rm.f32`, `sub.rn.f32` ×2, `fma.rn.f32` ×3, `shl.b32` and `add.s32` (FA4's `ex2_emulation`) | 2^x within 2⁻¹³·⁴⁷ relative for x ∈ [−126, 8] and 2⁻¹²⁷ absolute for x ∈ [−127, −126); +0 for x < −127 and −∞; wrong for x ≥ 128 and NaN (NaN gives +0); grain of the input | A58 |
| `splitWarpgroups` (`withShare`, `regsBack`) | `cta(512)` context, a `RegPool(L, 512, b)`, four counts that fit it (`Registers.fits`: each a multiple of 8 from 24 to 256, and 128 · Σ ≤ 512 · b; evidence); four bodies on warps 0–3, 4–7, 8–11 and 12–15 | `split` at warp 8, then at 4 and at 12; each warpgroup's branch runs `setmaxnreg` from b to its share's count (`.inc` up, `.dec` down, none if equal) and its body; after the join, each warpgroup `setmaxnreg` back to b, in warpgroup order (`regsBack`), so every first increase precedes every increase back; then `__syncthreads()` | the four bodies ran, each at its count; every warp holds b after the split; the shares used up (M24) | A3, A30, A59, I3, M24 |
| `when` | as `branch`, one arm | as `branch`, with an empty else arm | the state after the arm, or unchanged | M5 |
| `correctedAttentionKernel` | as `pairAttentionKernel` | as `pairAttentionKernel`, with a CTA of 512 threads (the launcher's block 512) and `__launch_bounds__(512, 1)` | as `pairAttentionKernel`, and the CTA's register pool, `Registers.pool(l, 512, 1)`: `RegPool(l, 512, 128)` | A17, A59, I6, M24 |

## 7. Public surface

Every operation that a client can call without the Key, and that builds a sealed value, must be sound on any
arguments. The audit as of this document:

- **Values.** `lit`, `zero`, `add`, `mulC`, `divC`, `remC`, `ceilDivC`, `lt`, `fma` build expressions from the
  library's own parts, with `u32` width checked on the output by `Check.literals` (I4). `tileRow0` and `tileCol0` read a sealed tile.
- **Evidence.** `fixedUnit`, `fixedPair` and the per-family `fixed…` (among them `fixedAccFull` and `fixedStoreAt`) exist
  only for one-valued types. None exists for `StageFree`, `StageWritten` or `StageFenced`, so a chunk's protocol runs
  in straight-line code.
- **Endings.** `release`, `skipTmem`, `finishConsumer` and `finishAccConsumer` consume authority; none mints any.
- **Unsealed data.** `Gen` helpers (`push`, `fresh`, `child`, `after`, `check`, …) and instruction builders (`mbarInit`,
  `mbarArriveCount`, `barrierCompletions`, `mmaIssue`, …) build unsealed `Gen` and `Stmt` values. These reach a kernel only through operations that need the
  Key (`resume`, `emit`, `finish`).
- **Output tiles and staging** (the TMA-store epilogue). `forChunks` consumes a tile's `TileOwn` and mints one
  `ChunkOwn` per chunk; `withStaging` mints the one `StoreSide`, `takeStore` turns it into the warpgroup-bound
  `StoreAt` (alignment evidence), and `acquireStage`, `stageAcc`, `stageAccFull`, `fenceStage`, `storeStage` and
  `finishStores` each consume the token of one typestate and mint the next (§6.6, §6.7; in `encoding/Core.rac`,
  `writeStage` in place of the two staging operations, writing the sealed `ChunkRegs` that only `loadAccChunk`,
  `loadBufferChunk` and `loadPairChunk` make, of their block's scope, so of one chunk); the coordinates, buffers
  and the issuing lane are the library's, never an argument. `tileRow0` and `tileCol0` read a sealed tile, as
  before. The instruction builders `bulkWaitRead`, `bulkWait`, `bulkCommit`, `fenceProxyAsync`, `tmaStore2d`,
  `storeShared4`, and the helpers `onLaneZero`, `stageBuffer`, `stageChunk`, build unsealed `Stmt`s or `Gen`s,
  which reach a kernel only through the Key.
- **Found by this audit.** `uniformParam` built a `Val` from any name, typed `uniform`. It now needs the Key.

- **The attention core** (`gpu/encoding/Core.rac`, §6.10). The f32 operations (`fadd`, `fsub`, `fmul`, `fmax`,
  `select`, `fconst`, `ex2`, `lg2`, `rcp`) and the unsealed `F32x8.mk` build values from the library's own `Val`s,
  and a `Val` carries no authority; `fconst`'s bits are checked at generation, and `asmValue`, which prints an
  instruction template, needs the Key. `holdStage` mints no authority, only renames a stage already held.
  `fixedReadyUsed`, `fixedExWriterAt` and `fixedExReaderAt` are evidence for fieldless one-valued families only.
  `splitTmem` mints two `Acc` tokens from one, over disjoint columns (the core's arithmetic), and takes back both
  before it returns the one; that is sound only while every use of a region's address goes through `tmemBase`.
  `fillBlock` is `fill` with the head coordinate and both columns the core's, from one map and one row, and
  `fillPage` `fill` with the row the core's, from the table. `eachChunk` and `writeP` run a client's step, an
  unrestricted function of values to code and values, on chunks they load under the buffer's `AccFull`; the loads,
  the chunk count and P's stores are theirs, so the step can neither load outside that window nor skip or repeat a
  chunk of P. `rescaleO` and `mmaPV` read `OState` themselves: an undefined Ô is overwritten, never rescaled or
  accumulated. `finishProducer`, `finishAccProducer`, `finishStores`, `finishConsumer`, `finishAccConsumer`,
  `closeExWriter` and `finishExReader` consume a side and mint nothing, and they are the only operations that take a
  side without giving one back (`finishExWriter`, the writer's wait, gives `OFinal`, a side that only `closeExWriter`
  ends): that is what lets the protocols close without `…Done` tokens (§6.10, M15), so a new operation that took a
  side and gave none back would have to drain as the waiting finishers do. `maskedScores` builds values from values and the
  sealed `Mask`; it emits no barrier, ring or tensor-memory operation, and a wrong block or chunk is a wrong result. In a causal kernel it
  emits warp collectives (`__syncwarp`, and the row's full-mask `__shfl_sync`), which are sound because it takes a
  `warps(f, 4)` context: a per-thread branch arm's group is `diverged`, so no part of a warp can reach it alone
  (`rejected/attention_mutants.py`, `mask_in_thread_branch`). The unsealed
  `AttnLaunch.mk` and `PagedLaunch.mk` build a launch from sealed maps, table, output and mask and from `Val`s:
  `blocks` and `q0` choose trip counts and coordinates only, so a wrong one deadlocks (M11) or loads the wrong rows
  (`ATTENTION.md` §5), and `seq` and `scale` are data, a wrong one a wrong result; none can race, since `storeO` takes
  its rows and guard from `AttnOut`, which is sealed. `outTypeOk`, `outValue`, `rowInHead` and `minusInfinityBits`
  build `Bool`s, `Expr`s and a `Nat`; `attnStart` needs the Key. The instruction builders `cvtBf16x2`, `tmemStore4`,
  `tmemStore8`, `tmemWaitStore` and `mmaIssueTmemA`, and the helpers `quadrantLanes`, `loadRow8`, `rescaleChunks`,
  `pvSteps`, `storeChunks`, `fillCode`, `mmaBoxes`, `pBase`, `pFullBar`, `pEmptyBar`, `flip`, `eight`, `offsetBy`,
  `boxAt`, `tmemBase`, `isHeadBox`, `headStage`, `attnParams`, `attnLauncher`, `pagedParams` and `pagedLauncher`, build
  unsealed `Expr`s, `Stmt`s, `Gen`s, `Bool`s and launchers, which reach a kernel only through the Key, as does `storeP`,
  now the `Gen` of one chunk of P; `row8`, `fbin`, `pvStage`, `mmaRingStage`, `loadChunk`, `chunksFrom` and
  `pChunksFrom` need it. `overwritesO` builds a `Bool`.
- **The score buffer** (A3a, §6.10). `loopFrom` is `loop` from another first index (`loop` is `loopFrom` from 0).
  `PairLaunch.mk`, unsealed, is as `AttnLaunch.mk`: `q0` and `q1` choose coordinates only. `mapRow` runs a client's step on a `Row`'s values and returns a `Row` of as many chunks; a `Row` is
  sealed, so its 16 chunks come only from `loadRow`, and `writeProbs` writes exactly one chunk of P per chunk.
  `fixedRowsAt` and `fixedMmaAt` are evidence for fieldless one-valued families. `takeRows`, `awaitScores`,
  `loadRow`, `writeProbs`, `rescaleRow`, `publishProbs`, `awaitFinal`, `storeFinal`, `takeMma`, `issueScores`,
  `awaitProbs`, `issuePV` and `commitBuffer` each consume a side's token and mint the next, and `closeRows` and
  `finishMma` consume one and mint none: they are its finishers (M15). `storeRow`, `counting`, `scoresFull`,
  `probsFull`, `probsAt`, `outAt`, `mapChunks`, `probChunks`, `scaleRow`, `rowInPairCta` and `upToTile` build unsealed `Gen`s,
  `Expr`s and lists, which reach a kernel only through the Key; `attnStart` needs it.
- **Paged decode** (`encoding/P2.md`, §6.11). `fillGroup` is `fill` with the row the core's and the bytes of a box of
  `group` rows. `withClaim` consumes the linear `ClaimOwn` and mints `Claimed` only inside the arm it emits under the
  broadcast flag; `Claimed` is sealed and of the arm's scope, and the arm is unrestricted, so it captures no linear
  value, and mints the linear `AppendOwn` there too, which only `appendRow` uses up. `appendRow` takes the row from
  `Claimed` and the columns from the warp and lane. `storeCombined` consumes `CombinedOwn`. `F32x4.splat`, `map`,
  `zip` and `columns`, `Reg4.mk`, `reg4`, `get4` and `set4` build values and registers from values and registers, as
  `F32x8.mk`, `reg`, `get` and `set` do; `asmOut`, which prints a template, needs the Key. `splitLse` and `splitRow` read the sealed `Partials` with their guard. The unsealed `DecodeLaunch`,
  `AppendLaunch` and `CombineLaunch` build launches from sealed parts and `Val`s: `blocks` and `first` (decode) and
  `splits` (combine) choose trip counts and table entries only, so a wrong one deadlocks (M11), reads a wrong page or
  split (guarded), or computes a wrong result. `F32x4.mk` builds values from values. `warpCta`, `wideParam`,
  `belowI32`, `cacheRequires`, `cacheMaps`, `fillBoxes`, `rowInTile`, `keptOrZero`, `storeRow`,
  `splitRowOf`, `laneColumns`, `columnStores`, `globalAt`, `loadRelaxed64`, `casRelaxed64`, `broadcastLane0`,
  `decodeArrays`, `decodeParams`, `decodeLauncher`,
  `appendParams`, `appendLauncher`, `combineParams` and `combineLauncher` build unsealed `Group`s, `Expr`s, `Stmt`s,
  `Gen`s, `String`s and launchers, which reach a kernel only through the Key; `headOut`, which builds an `AttnOut`,
  needs it.
- **The CTA pair** (§6.12). `CtaPair`, `Leader`, `PairTile`, `PairOut`, `HalfOwn`, `PairRing` and `PairAccRing` are
  sealed, and only `pairGemmKernel`, `onLeader` and the pair openers make them. No operation hands a client the rank
  (M18). `onLeader` mints a `Leader` that belongs to its arm and hands back only the arm's context. `takePairProducer`,
  `acquirePair`, `fillPair`, `finishPairProducer`, `takePairConsumer`, `awaitPair`, `mmaPairFirst`, `mmaPairNext`,
  `releasePair`, `takePairAccProducer`, `acquirePairAcc`, `commitPairAcc`, `finishPairAccProducer`,
  `takePairAccConsumer`, `awaitPairAcc`, `storeHalf` and `releasePairAcc` each consume a side's token and mint the next,
  or, as the single-CTA finishers, none; `fillPair` and `storeHalf` take their rows from the sealed `PairTile`, never
  from the caller. The unsealed `PairGemm.mk` builds a launch from sealed parts and a `Val`, K, which chooses trip
  counts only (M18). `oneCta`, `ringLayout`, `accRingLayout`, `setupBarriers`, `publishBarriers`, `clusterSync`,
  `waitSem`, `mbarArriveRemote`, `tmaLoad2dPair`, `isLeader`, `pairShared`, `pairMmaShapeOk`, `pairGemmShapeOk`,
  `pairGemmParams`, `gemmHostParams`, `gemmRequires`, `operandMaps` and `pairGemmLauncher` build unsealed `Gen`s,
  `Stmt`s, `Expr`s, `String`s, `Nat`s, `Bool`s and launchers, which reach a kernel only through the Key; `emitIn`,
  `readSpecial`, `toLeader`, `ringAt`, `accRingAt`, `pairStart`, `pairFinish`, `tmemScope`, `closePair` and
  `mmaPairStage` need it.
  The persistent pair GEMM adds the sealed `PairSched` and the linear `PairSchedOwn`, which only
  `pairGemmPersistentKernel` makes. `forPairTiles` mints a `PairTile` per tile from the sealed schedule and its pair,
  `forOwnedPairTiles` consumes the `PairSchedOwn` and mints a `HalfOwn` per tile, and `forHalfChunks` consumes a
  `HalfOwn` and mints a `ChunkOwn` per chunk, with the rows the `PairTile`'s; `loadPairChunk` is `loadBufferChunk` on a
  pair accumulator ring. `onLeader` takes `LeaderOnly` evidence, which only `leaderOnlyUnit`, `leaderOnlyConsumer`,
  `leaderOnlyAccProducer` and `leaderOnlyPair` make, for `Unit`, a pair ring's `Consumer` (from its `PairRing`), a pair
  accumulator ring's `AccProducer` (from its `PairAccRing`) and pairs of them (M20). `schedule`, `pairTile` and `chunkLoop` need the Key; `Cuda.smCount` and the grid
  `Grid.persistentPairs` are the printer's.
- **The correction warpgroup** (A3b, §6.13). `withCorrectedBuffer` mints one `ScoreBuffer(x, correction)` and its
  three sides; `Rescaler` is unsealed data, but a `ScoreBuffer` is sealed, so a buffer's rescaler is its opener's.
  `publishAlpha`, `takeCorrection`, `zeroQuadrants`, `awaitAlpha`, `rescaleQuadrant` and `publishRescaled` each consume
  a side's token and mint the next, and `finishCorrection` consumes one and mints none: it is the correction side's
  finisher (M15). `fixedCorrectAt` and `fixedRescaling` are evidence for fieldless one-valued families. `voteAny`
  builds a value from a value, of grain `warp` because the vote makes it so; a `warp`-grain value from anything else
  would let a branch run `warpwise` arms on a condition that differs within a warp. `Grain.warp` is a constructor
  any client can name, but only on `Val`s, which are sealed: a client cannot make a `Val` of a grain the core did not
  give it. `ex2emu` builds a value; its template is the core's. `splitWarpgroups` divides a register pool and emits
  every `setmaxnreg`, through `withShare` and `regsBack`, which need the Key and a share (M24). `when` is `branch`
  with an empty else arm. `AlphaRing.mk`, `alphaRing` and `alphaOf` build offsets and register names, which grant
  nothing; `ownQuadrants`, `zeroRow`, `publishCode`, `alphaRow`, `setMaxRegs` and `twoTileStart` build unsealed
  `Bool`s, `Gen`s, `Expr`s and `Stmt`s, which reach a kernel only through the Key (`openScoreBuffer` and
  `twoTileStart` need it).
- **The register pool** (`gpu/encoding/Registers.rac`, M24). It declares `RegPool`, sealed and unrestricted, and
  `RegShare`, sealed and linear, and emits nothing. `split` mints a pool's four shares, under the evidence `fits`;
  `join` uses four shares up and mints nothing; `budget`, `countOk` and `fits` build numbers and `Bool`s. `pool` mints
  a pool from nothing, and is the one trusted operation: only a kernel builder may call it, with the threads and
  residency the builder passes to `finish` (`correctedAttentionKernel`: 512 and 1). Nothing checks that, since sealing
  is per file and `Registers.rac` cannot need the Key without importing `Core`, which imports it (`encoding/REGISTERS.md`
  §9). A client's pool at the kernel's own count is the builder's pool again; one at another count makes
  `splitWarpgroups` print changes from a count the warps do not hold, which the register check refuses
  (`pool_at_other_count`).
- **The examples' shared modules** (`gpu/encoding/Layout.rac`, `gpu/encoding/Attention.rac`) are clients: they declare
  no sealed family and need no Key. `Layout.roles4` is `split` three times, `Layout.rolesPair` four times,
  `Layout.rolesCorrected` `splitWarpgroups` and `split` three times. `Attention.pairLoader` and `pairIssuer` are A3a's
  loader and issuer, which A3b shares.

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
- the parity each side waits on is the phase it means;
- every phase is observed by a wait before the next is arrived on.

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
