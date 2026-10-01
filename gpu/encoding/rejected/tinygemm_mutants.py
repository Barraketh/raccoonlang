# The encoding core's TinyGEMM with one mistake each: each rule of the Blackwell layer (gpu/DESIGN.md) that TinyGEMM
# exercises refuses the program that breaks it. A protocol's side, with no `…Done` token to hand back, is linear and belongs to its opener's
# scope, so a role that ends without its finisher is refused as leaving it unused; and one finished inside the chunk
# loop, whose body captures no linear value, is refused too (M23). Run by check.sh through gpu/mutate.py.

SOURCE = "encoding/examples/tinygemm.rac"

MUTANTS = [
    dict(
        name="ring_closed_while_filling", expect="LinearUnused", mentions="p has a linear type",
        why="Ends the producer without its tail: its last copies could still be landing when the ring's storage goes "
            "away. The producer is linear and belongs to the ring's scope, and only `finishProducer`'s drain uses it "
            "up.",
        old="""      (finishProducer(e, ring, p), Unit.unit)""",
        new="""      (e, Unit.unit)""",
    ),
    dict(
        name="stores_in_flight_at_close", expect="LinearUnused", mentions="sa has a linear type",
        why="Ends the epilogue without waiting for its TMA stores: the staging buffers' shared memory would be released "
            "while a store still reads it. The storing side is linear and belongs to the staging scope, and only "
            "`finishStores`' wait uses it up.",
        old="""    (finishStores(e, stg, sa), acc)""",
        new="""    (e, acc)""",
    ),
    dict(
        name="store_side_captured_by_chunk_loop", expect="TypeMismatch", mentions="closures differ in kind",
        why="Hands the storing side to the chunk loop's body by capture, not through its state, and finishes it per "
            "chunk. A loop's body runs any number of times, so it captures no linear value.",
        old="""    let (e, (acc, sa)) := forChunks(e, k.tile, own, fixedPair(fixedAcc(a, AccState.ready), fixedStoreAt(s, m, groupWarp)), (acc, sa), chunk)
    (finishStores(e, stg, sa), acc)""",
        new="""    let (e, acc) := forChunks(e, k.tile, own, fixedAcc(a, AccState.ready), acc,
      fun (p: Lifetime)(ch: ChunkAt(p, 128))(co: ChunkOwn(p, 128))(e: Ctx(p, Wg))(acc: Acc(a, AccState.ready)): Pair(Ctx(p, Wg), Acc(a, AccState.ready)) => {
        let (e, (acc, sa)) := chunk(p, ch, co, e, (acc, sa))
        (finishStores(e, stg, sa), acc)
      })
    (e, acc)""",
    ),
    dict(
        name="fill_without_acquire", expect="ImplicitReconstructionFailed", mentions="Slot",
        why="Fills the producer's current stage without waiting for it to be free: `fill` needs the `Slot` that "
            "`acquire` hands out.",
        old="""        let (e, s) := acquire(e, ring, p)
        fill(e, ring, s, k.a, mulC(i, 64), tileRow0(k.tile), k.b, mulC(i, 64), tileCol0(k.tile))""",
        new="""        fill(e, ring, p, k.a, mulC(i, 64), tileRow0(k.tile), k.b, mulC(i, 64), tileCol0(k.tile))""",
    ),
    dict(
        name="producer_not_elected", expect="ImplicitReconstructionFailed", mentions="ProducerAt",
        why="Runs the producer on the whole warp, without electing a thread: every lane would wait, arm the barrier "
            "and issue the copies. Only an elected thread can take the endpoint that `acquire` and `fill` need.",
        old="""    elect(e, Unit, fun (j: Lifetime)(w: Elected(j))(e: Ctx(j, One)): Pair(Ctx(j, One), Unit) => {
      let step := fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, One))(p: ProducerAt(r, j)): Pair(Ctx(n, One), ProducerAt(r, j)) => {
        let (e, s) := acquire(e, ring, p)
        fill(e, ring, s, k.a, mulC(i, 64), tileRow0(k.tile), k.b, mulC(i, 64), tileCol0(k.tile))
      }
      let (e, p) := takeProducer(e, w, ring, p)
      let (e, p) := loopPeeled(e, steps, fixedProducerAt(r, j), p, step, step)
      (finishProducer(e, ring, p), Unit.unit)
    })""",
        new="""  {
    let step := fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, Load))(p: Producer(r)): Pair(Ctx(n, Load), Producer(r)) => {
      let (e, s) := acquire(e, ring, p)
      fill(e, ring, s, k.a, mulC(i, 64), tileRow0(k.tile), k.b, mulC(i, 64), tileCol0(k.tile))
    }
    let (e, p) := loopPeeled(e, steps, fixedProducerAt(r, m), p, step, step)
    (finishProducer(e, ring, p), Unit.unit)
  }""",
    ),
    dict(
        name="producer_changes_thread", expect="TypeMismatch", mentions="ProducerAt",
        why="Takes the producer in one elected thread, fills a stage, and hands the endpoint on for a later elect to "
            "continue. The stage and phase registers belong to the first thread; another would start from stage 0 "
            "and overwrite a stage still being read. An endpoint taken in scope `j` cannot leave it.",
        old="""      (finishProducer(e, ring, p), Unit.unit)
    })
""",
        new="""      (finishProducer(e, ring, p), Unit.unit)
    })

  def producer2 {l: Lifetime}{r: Lifetime}(k: Launch(l))(ring: Ring(r, ringCfg))(p: Producer(r))(m: Lifetime)
      (e: Ctx(m, Load)): Pair(Ctx(m, Load), ProducerAt(r, m)) :=
    elect(e, ProducerAt(r, m), fun (j: Lifetime)(w: Elected(j))(e: Ctx(j, One)): Pair(Ctx(j, One), ProducerAt(r, m)) => {
      let (e, p) := takeProducer(e, w, ring, p)
      let (e, s) := acquire(e, ring, p)
      fill(e, ring, s, k.a, lit(0), tileRow0(k.tile), k.b, lit(0), tileCol0(k.tile))
    })
""",
    ),
    dict(
        name="mma_without_await", expect="TypeMismatch",
        why="Issues the first MMA on the consumer's current stage without waiting for its copies to land: "
            "`mmaFirst` reads a stage through the `Ready` that `await` hands out.",
        old="""        let (e, rd) := await(e, ring, c)
        let (e, (used, acc)) := mmaFirst(e, w, ring, rd, t, acc)""",
        new="""        let (e, rd) := (e, c)
        let (e, (used, acc)) := mmaFirst(e, w, ring, rd, t, acc)""",
    ),
    dict(
        name="accumulate_into_empty", expect="TypeMismatch",
        why="Accumulates into the fresh accumulator: tensor memory is not zeroed, so the first MMA must overwrite it.",
        old="""        let (e, (used, acc)) := mmaFirst(e, w, ring, rd, t, acc)""",
        new="""        let (e, (used, acc)) := mmaNext(e, w, ring, rd, t, acc)""",
    ),
    dict(
        name="release_twice", expect="LinearReused", mentions="used",
        why="Releases a stage twice: the second commit would free the next stage before its MMAs are issued. A "
            "release consumes the used stage, so the second has none to release.",
        old="""        let (e, (used, acc)) := mmaNext(e, w, ring, rd, t, acc)
        let (e, c) := releaseByMma(e, w, ring, used)""",
        new="""        let (e, (used, acc)) := mmaNext(e, w, ring, rd, t, acc)
        let (e, c) := releaseByMma(e, w, ring, used)
        let (e, c2) := releaseByMma(e, w, ring, used)""",
    ),
    dict(
        name="loop_changes_accumulator", expect="TypeMismatch",
        why="Runs every K step, the first included, as one loop body that starts from the empty accumulator: the "
            "body is generated once, so its state must keep one type; the first step has to be peeled.",
        old="""loopPeeled(e, steps, fixedPair(fixedConsumerAt(r, j), fixedAccPending(a, j)), (c, acc), first, rest)""",
        new="""loop(e, steps, fixedPair(fixedConsumerAt(r, j), fixedAccPending(a, j)), (c, acc), first)""",
    ),
    dict(
        name="mma_never_committed", expect="LinearUnused", mentions="acc has a linear type",
        why="Finishes the issuer without committing its MMAs to the handoff: the epilogue could never observe them "
            "complete, and tensor memory could be freed with MMAs in flight.",
        old="""      let e := sendAcc(e, w, hd, send, acc)
""",
        new="",
    ),
    dict(
        name="store_before_handoff", expect="TypeMismatch", mentions="Lifetime.union(Lifetime.union(Lifetime.union(a, h), s), m)",
        why="Reads the accumulator without waiting for the issuer's commit: `forChunks`'s state is `Acc(a, ready)`, "
            "which only `recvAcc` makes; `recv` is an `AccRecv` of the handoff's scope.",
        old="""    let (e, acc) := recvAcc(e, hd, recv)
    let (e, sa) := takeStore(e, stg, side)
    let (e, (acc, sa)) := forChunks(e, k.tile, own, fixedPair(fixedAcc(a, AccState.ready), fixedStoreAt(s, m, groupWarp)), (acc, sa), chunk)""",
        new="""    let (e, sa) := takeStore(e, stg, side)
    let (e, (acc, sa)) := forChunks(e, k.tile, own, fixedPair(fixedAcc(a, AccState.ready), fixedStoreAt(s, m, groupWarp)), (recv, sa), chunk)""",
    ),
    dict(
        name="stage_before_wait", expect="ImplicitReconstructionFailed", mentions="StageFree",
        why="Writes the staging buffer without waiting for the store that last read it: lane 0's "
            "`cp.async.bulk.wait_group.read` is what frees it, and `writeStage` needs the `StageFree` that "
            "`acquireStage` hands out.",
        old="""      let (e, free) := acquireStage(e, stg, sa)
      let (e, written) := writeStage(e, stg, free, regs)""",
        new="""      let (e, written) := writeStage(e, stg, sa, regs)""",
    ),
    dict(
        name="second_tmem_allocation", expect="LinearReused", mentions="permit",
        why="Allocates tensor memory after giving up the permit: `tcgen05.alloc` after `relinquish_alloc_permit` is "
            "illegal.",
        old="""      let (e, u) := withTmem(e, permit, 128, AccState.ready, Unit, body)""",
        new="""      let gone := skipTmem(permit)
      let (e, u) := withTmem(e, permit, 128, AccState.ready, Unit, body)""",
    ),
    dict(
        name="static_and_dynamic_shared", expect="EvidenceNotDischarged", mentions="Check.Clean.sharedOk",
        why="Declares a static shared array in a kernel whose TMA stages live in the dynamic buffer: the static array "
            "comes first in the shared window, and the dynamic buffer could lose the 1024-byte alignment the 128-byte "
            "swizzle needs.",
        old="""      let (e, u) := withTmem(e, permit, 128, AccState.ready, Unit, body)
      e""",
        new="""      shared(e, DType.f32, 256, fun (a2: Lifetime)(sa: Smem(a2, DType.f32, 256))(ta: Tile(a2, DType.f32, 256, TileState.empty))
          (e: Ctx(l, Cta)): Ctx(l, Cta) => {
        let gone := release(ta)
        let (e, u) := withTmem(e, permit, 128, AccState.ready, Unit, body)
        e
      })""",
    ),
    dict(
        name="kernel_name_not_identifier", expect="EvidenceNotDischarged", mentions="Check.Clean.namesOk",
        why="Names the kernel with text that is not a C identifier: the name is printed as written, so it could "
            "inject code of its own.",
        old="""tmaGemmKernel("tinygemm",""",
        new="""tmaGemmKernel("tinygemm(float* C) { C[0] = 0.0f; } __global__ void evil",""",
    ),
    dict(
        name="kernel_named_like_parameter", expect="EvidenceNotDischarged", mentions="Check.Clean.namesOk",
        why="Names the kernel `A`, a C identifier that generates, but also the name of the launcher's parameter: in "
            "the launcher, `reinterpret_cast<const void*>(A)` would take the pointer to A's elements for the kernel, "
            "and launch it. No chosen name may be one the printer or the launcher declares.",
        old="""tmaGemmKernel("tinygemm",""",
        new="""tmaGemmKernel("A",""",
    ),
    dict(
        name="literal_wider_than_u32", expect="EvidenceNotDischarged", mentions="Check.Clean.literalsOk",
        why="Scales the K coordinate by a constant that does not fit the 32-bit value it is typed as.",
        old="""        fill(e, ring, s, k.a, mulC(i, 64), tileRow0(k.tile), k.b, mulC(i, 64), tileCol0(k.tile))""",
        new="""        fill(e, ring, s, k.a, mulC(i, 4294967296), tileRow0(k.tile), k.b, mulC(i, 64), tileCol0(k.tile))""",
    ),
    dict(
        name="box_narrower_than_swizzle", expect="EvidenceNotDischarged", mentions="ring: a box must be 64 elements wide",
        why="Loads 32-element (64-byte) boxes of A with the 128-byte swizzle, which needs 128-byte rows and "
            "1024-byte-aligned stages.",
        old="""  def boxA : TmaSpec := TmaSpec.mk(64, 128)""",
        new="""  def boxA : TmaSpec := TmaSpec.mk(32, 128)""",
    ),
    dict(
        name="mma_m64", expect="EvidenceNotDischarged", mentions="mma: unsupported shape",
        why="Loads 64-row boxes of A: an M=64 accumulator is not laid out one row per tensor-memory lane, as the "
            "epilogue reads it.",
        old="""  def boxA : TmaSpec := TmaSpec.mk(64, 128)""",
        new="""  def boxA : TmaSpec := TmaSpec.mk(64, 64)""",
    ),
    dict(
        name="k_steps_by_zero", expect="EvidenceNotDischarged", mentions="positive",
        why="Counts the K slices by dividing by zero: `ceilDivC` asks for a positive divisor as evidence.",
        old="""ceilDivC(k.k, 64)""",
        new="""ceilDivC(k.k, 0)""",
    ),
    dict(
        name="store_before_fence", expect="ImplicitReconstructionFailed", mentions="StageFenced",
        why="Issues the TMA store without the proxy fence: the threads' `st.shared` writes are not ordered before the "
            "async proxy's reads of the buffer. `storeStage` needs the `StageFenced` that `fenceStage` hands out.",
        old="""      let (e, fenced) := fenceStage(e, written)
      let (e, sa) := storeStage(e, stg, fenced, k.c, ch, co)""",
        new="""      let (e, sa) := storeStage(e, stg, written, k.c, ch, co)""",
    ),
    dict(
        name="epilogue_misaligned", expect="EvidenceNotDischarged", mentions="aligned of Core.takeStore",
        why="Takes the storing side on warps 5 to 8: a warp reads the tensor-memory lanes of its rank in its aligned "
            "warpgroup, so an unaligned group would store rows of C from another warp's lanes. `takeStore` asks for "
            "the alignment as evidence.",
        old="""  def kernel : Program :=""",
        new="""  def misaligned {s: Lifetime}(stg: Staging(s))(side: StoreSide(s))(m: Lifetime)(e: Ctx(m, Group.warps(5, 4)))
      : Pair(Ctx(m, Group.warps(5, 4)), StoreAt(s, m, 5)) := takeStore(e, stg, side)

  def kernel : Program :=""",
    ),
]
