# TinyGEMM with one mistake each: every rule of the Blackwell layer (gpu/DESIGN.md) refuses the program that breaks
# it. Run by check.sh through gpu/mutate.py.

SOURCE = "examples/tinygemm.rac"

MUTANTS = [
    dict(
        name="fill_without_acquire", expect="ImplicitReconstructionFailed", mentions="Slot",
        why="Fills the producer's current stage without waiting for it to be free: `fill` needs the `Slot` that "
            "`acquire` hands out.",
        old="""        let (e, s) := Gpu.acquire(e, ring, p)
        Gpu.fill(e, ring, s, k.a, Gpu.mulC(i, 64), k.m0, k.b, Gpu.mulC(i, 64), k.n0)""",
        new="""        Gpu.fill(e, ring, p, k.a, Gpu.mulC(i, 64), k.m0, k.b, Gpu.mulC(i, 64), k.n0)""",
    ),
    dict(
        name="ring_closed_while_filling", expect="TypeMismatch",
        why="Leaves the ring without the producer's tail: its last copies could still be landing when the ring's "
            "storage goes away. Only `finishProducer` makes the `ProducerDone` the ring requires.",
        old="""      Gpu.finishProducer(e, ring, p)""",
        new="""      (e, p)""",
    ),
    dict(
        name="producer_not_elected", expect="ImplicitReconstructionFailed", mentions="ProducerAt",
        why="Runs the producer on the whole warp, without electing a thread: every lane would wait, arm the barrier "
            "and issue the copies. Only an elected thread can take the endpoint that `acquire` and `fill` need.",
        old="""    Gpu.elect(e, ProducerDone(r), fun (j: Lifetime)(w: Elected(j))(e: Ctx(j, Tiny.One)): Pair(Ctx(j, Tiny.One), ProducerDone(r)) => {
      let step := fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, Tiny.One))(p: ProducerAt(r, j))
          : Pair(Ctx(n, Tiny.One), ProducerAt(r, j)) => {
        let (e, s) := Gpu.acquire(e, ring, p)
        Gpu.fill(e, ring, s, k.a, Gpu.mulC(i, 64), k.m0, k.b, Gpu.mulC(i, 64), k.n0)
      }
      let (e, p) := Gpu.takeProducer(e, w, ring, p)
      let (e, p) := Gpu.loopPeeled(e, steps, Gpu.fixedProducerAt(r, j), p, step, step)
      Gpu.finishProducer(e, ring, p)
    })""",
        new="""  {
    let step := fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, Tiny.Load))(p: Producer(r))
        : Pair(Ctx(n, Tiny.Load), Producer(r)) => {
      let (e, s) := Gpu.acquire(e, ring, p)
      Gpu.fill(e, ring, s, k.a, Gpu.mulC(i, 64), k.m0, k.b, Gpu.mulC(i, 64), k.n0)
    }
    let (e, p) := Gpu.loopPeeled(e, steps, Gpu.fixedProducerAt(r, m), p, step, step)
    Gpu.finishProducer(e, ring, p)
  }""",
    ),
    dict(
        name="producer_changes_thread", expect="TypeMismatch", mentions="ProducerAt",
        why="Takes the producer in one elected thread, fills a stage, and hands the endpoint on for a later elect to "
            "continue. The stage and phase registers belong to the first thread; another would start from stage 0 "
            "and overwrite a stage still being read. An endpoint taken in scope `j` cannot leave it.",
        old="""      let (e, p) := Gpu.takeProducer(e, w, ring, p)
      let (e, p) := Gpu.loopPeeled(e, steps, Gpu.fixedProducerAt(r, j), p, step, step)
      Gpu.finishProducer(e, ring, p)
    })""",
        new="""      let (e, p) := Gpu.takeProducer(e, w, ring, p)
      let (e, p) := Gpu.loopPeeled(e, steps, Gpu.fixedProducerAt(r, j), p, step, step)
      Gpu.finishProducer(e, ring, p)
    })

  def producer2 {l: Lifetime}{r: Lifetime}(k: Tiny.Launch(l))(ring: Ring(r, Tiny.ring))(p: Producer(r))(m: Lifetime)
      (e: Ctx(m, Tiny.Load)): Pair(Ctx(m, Tiny.Load), ProducerAt(r, m)) :=
    Gpu.elect(e, ProducerAt(r, m), fun (j: Lifetime)(w: Elected(j))(e: Ctx(j, Tiny.One)): Pair(Ctx(j, Tiny.One), ProducerAt(r, m)) => {
      let (e, p) := Gpu.takeProducer(e, w, ring, p)
      let (e, s) := Gpu.acquire(e, ring, p)
      Gpu.fill(e, ring, s, k.a, Gpu.lit(0), k.m0, k.b, Gpu.lit(0), k.n0)
    })""",
    ),
    dict(
        name="mma_without_await", expect="TypeMismatch",
        why="Issues the first MMA on the consumer's current stage without waiting for its copies to land: "
            "`mmaFirst` reads a stage through the `Ready` that `await` hands out.",
        old="""        let (e, rd) := Gpu.await(e, ring, c)
        let (e, (used, acc)) := Gpu.mmaFirst(e, w, ring, rd, t, acc)""",
        new="""        let (e, rd) := (e, c)
        let (e, (used, acc)) := Gpu.mmaFirst(e, w, ring, rd, t, acc)""",
    ),
    dict(
        name="accumulate_into_empty", expect="TypeMismatch",
        why="Accumulates into the fresh accumulator: tensor memory is not zeroed, so the first MMA must overwrite it.",
        old="""        let (e, (used, acc)) := Gpu.mmaFirst(e, w, ring, rd, t, acc)""",
        new="""        let (e, (used, acc)) := Gpu.mmaNext(e, w, ring, rd, t, acc)""",
    ),
    dict(
        name="release_twice", expect="LinearReused", mentions="used",
        why="Releases a stage twice: the second commit would free the next stage before its MMAs are issued. A "
            "release consumes the used stage, so the second has none to release (the checker reports one linearity "
            "error per definition, and finds that one before the unused endpoint `c2` the second release hands back).",
        old="""        let (e, (used, acc)) := Gpu.mmaNext(e, w, ring, rd, t, acc)
        let (e, c) := Gpu.releaseByMma(e, w, ring, used)""",
        new="""        let (e, (used, acc)) := Gpu.mmaNext(e, w, ring, rd, t, acc)
        let (e, c) := Gpu.releaseByMma(e, w, ring, used)
        let (e, c2) := Gpu.releaseByMma(e, w, ring, used)""",
    ),
    dict(
        name="loop_changes_accumulator", expect="TypeMismatch",
        why="Runs every K step, the first included, as one loop body that starts from the empty accumulator: the "
            "body is generated once, so its state must keep one type; the first step has to be peeled.",
        old="""      let (e, (c, acc)) := Gpu.loopPeeled(e, steps,
        Gpu.fixedPair(Gpu.fixedConsumerAt(r, j), Gpu.fixedAccPending(a, j)), (c, acc), first, rest)""",
        new="""      let (e, (c, acc)) := Gpu.loop(e, steps,
        Gpu.fixedPair(Gpu.fixedConsumerAt(r, j), Gpu.fixedAccPending(a, j)), (c, acc), first)""",
    ),
    dict(
        name="mma_never_committed", expect="LinearUnused", mentions="acc",
        why="Finishes the issuer without committing its MMAs to the handoff: the epilogue could never observe them "
            "complete, and tensor memory could be freed with MMAs in flight.",
        old="""      (Gpu.sendAcc(e, w, hd, send, acc), Gpu.finishConsumer(c))""",
        new="""      (e, Gpu.finishConsumer(c))""",
    ),
    dict(
        name="store_before_handoff", expect="TypeMismatch",
        why="Reads the accumulator without waiting for the issuer's commit: `storeAcc` needs `Acc(a, ready)`, which "
            "only `recvAcc` makes.",
        old="""    let (e, acc) := Gpu.recvAcc(e, hd, recv)
    Gpu.storeAcc(e, t, acc, k.c, own)""",
        new="""    Gpu.storeAcc(e, t, recv, k.c, own)""",
    ),
    dict(
        name="second_tmem_allocation", expect="LinearReused", mentions="permit",
        why="Allocates tensor memory after giving up the permit: `tcgen05.alloc` after `relinquish_alloc_permit` is "
            "illegal.",
        old="""        let (e, u) := Gpu.withTmem(e, permit, 128, AccState.ready, Unit, body)""",
        new="""        let gone := Gpu.skipTmem(permit)
        let (e, u) := Gpu.withTmem(e, permit, 128, AccState.ready, Unit, body)""",
    ),
    dict(
        name="static_and_dynamic_shared", expect="#error",
        why="Declares a static shared array in a kernel whose TMA stages live in the dynamic buffer: the static array "
            "comes first in the shared window, and the dynamic buffer could lose the 1024-byte alignment the 128-byte "
            "swizzle needs.",
        old="""        let (e, u) := Gpu.withTmem(e, permit, 128, AccState.ready, Unit, body)
        e""",
        new="""        Gpu.shared(e, DType.f32, 256, fun (a2: Lifetime)(sa: Smem(a2, DType.f32, 256))(ta: Tile(a2, DType.f32, 256, TileState.empty))
            (e: Ctx(l, Tiny.Cta)): Ctx(l, Tiny.Cta) => {
          let gone := Gpu.release(ta)
          let (e, u) := Gpu.withTmem(e, permit, 128, AccState.ready, Unit, body)
          e
        })""",
    ),
    dict(
        name="kernel_name_not_identifier", expect="#error",
        why="Names the kernel with text that is not a C identifier: the name is printed as written, so it could "
            "inject code of its own.",
        old="""    Gpu.tmaGemmKernel("tinygemm",""",
        new="""    Gpu.tmaGemmKernel("tinygemm(float* C) { C[0] = 0.0f; } __global__ void evil",""",
    ),
    dict(
        name="literal_wider_than_u32", expect="#error",
        why="Scales the K coordinate by a constant that does not fit the 32-bit value it is typed as.",
        old="""        Gpu.fill(e, ring, s, k.a, Gpu.mulC(i, 64), k.m0, k.b, Gpu.mulC(i, 64), k.n0)""",
        new="""        Gpu.fill(e, ring, s, k.a, Gpu.mulC(i, 4294967296), k.m0, k.b, Gpu.mulC(i, 64), k.n0)""",
    ),
    dict(
        name="box_narrower_than_swizzle", expect="#error",
        why="Loads 32-element (64-byte) boxes of A with the 128-byte swizzle, which needs 128-byte rows and "
            "1024-byte-aligned stages.",
        old="""  def boxA : TmaSpec := TmaSpec.mk(64, 128)""",
        new="""  def boxA : TmaSpec := TmaSpec.mk(32, 128)""",
    ),
    dict(
        name="mma_m64", expect="#error",
        why="Loads 64-row boxes of A: an M=64 accumulator is not laid out one row per tensor-memory lane, as the "
            "epilogue reads it.",
        old="""  def boxA : TmaSpec := TmaSpec.mk(64, 128)""",
        new="""  def boxA : TmaSpec := TmaSpec.mk(64, 64)""",
    ),
    dict(
        name="epilogue_misaligned", expect="EvidenceNotDischarged", mentions="aligned",
        why="Runs the epilogue on warps 5 to 8: a warp reads the tensor-memory lanes of its rank in its aligned "
            "warpgroup, so an unaligned group would store rows of C from another warp's lanes. `storeAcc` asks for "
            "the alignment as evidence.",
        old="""  def Wg1 : Group := Group.warps(4, 4)""",
        new="""  def Wg1 : Group := Group.warps(5, 4)""",
    ),
    dict(
        name="k_steps_by_zero", expect="EvidenceNotDischarged", mentions="positive",
        why="Counts the K slices by dividing by zero: `ceilDivC` asks for a positive divisor as evidence.",
        old="""Gpu.ceilDivC(k.k, 64)""",
        new="""Gpu.ceilDivC(k.k, 0)""",
    ),
]
