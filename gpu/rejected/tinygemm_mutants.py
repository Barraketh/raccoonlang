# TinyGEMM with one mistake each: every rule of the Blackwell layer (gpu/DESIGN.md) refuses the program that breaks
# it. Run by check.sh through gpu/mutate.py.

SOURCE = "examples/tinygemm.rac"

MUTANTS = [
    dict(
        name="fill_without_acquire", expect="ImplicitReconstructionFailed", mentions="Slot",
        why="Fills the producer's current stage without waiting for it to be free: `fill` needs the `Slot` that "
            "`acquire` hands out.",
        old="""        match Gpu.acquire(e, ring, p) returning Pair(Ctx(n, Tiny.One), ProducerAt(r, j)) with
        | Pair.mk e s => Gpu.fill(e, ring, s, k.a, Gpu.mulC(i, 64), k.m0, k.b, Gpu.mulC(i, 64), k.n0)""",
        new="""        Gpu.fill(e, ring, p, k.a, Gpu.mulC(i, 64), k.m0, k.b, Gpu.mulC(i, 64), k.n0)""",
    ),
    dict(
        name="ring_closed_while_filling", expect="TypeMismatch",
        why="Leaves the ring without the producer's tail: its last copies could still be landing when the ring's "
            "storage goes away. Only `finishProducer` makes the `ProducerDone` the ring requires.",
        old="""        | Pair.mk e p => Gpu.finishProducer(e, ring, p)""",
        new="""        | Pair.mk e p => Pair.mk(e, p)""",
    ),
    dict(
        name="producer_not_elected", expect="ImplicitReconstructionFailed", mentions="ProducerAt",
        why="Runs the producer on the whole warp, without electing a thread: every lane would wait, arm the barrier "
            "and issue the copies. Only an elected thread can take the endpoint that `acquire` and `fill` need.",
        old="""    Gpu.elect(e, ProducerDone(r), fun (j: Lifetime)(w: Elected(j))(e: Ctx(j, Tiny.One)): Pair(Ctx(j, Tiny.One), ProducerDone(r)) => {
      let step := fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, Tiny.One))(p: ProducerAt(r, j))
          : Pair(Ctx(n, Tiny.One), ProducerAt(r, j)) => {
        match Gpu.acquire(e, ring, p) returning Pair(Ctx(n, Tiny.One), ProducerAt(r, j)) with
        | Pair.mk e s => Gpu.fill(e, ring, s, k.a, Gpu.mulC(i, 64), k.m0, k.b, Gpu.mulC(i, 64), k.n0)
      }
      match Gpu.takeProducer(e, w, ring, p) returning Pair(Ctx(j, Tiny.One), ProducerDone(r)) with
      | Pair.mk e p => {
        match Gpu.loopPeeled(e, steps, p, step, step) returning Pair(Ctx(j, Tiny.One), ProducerDone(r)) with
        | Pair.mk e p => Gpu.finishProducer(e, ring, p)
      }
    })""",
        new="""  {
    let step := fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, Tiny.Load))(p: Producer(r))
        : Pair(Ctx(n, Tiny.Load), Producer(r)) => {
      match Gpu.acquire(e, ring, p) returning Pair(Ctx(n, Tiny.Load), Producer(r)) with
      | Pair.mk e s => Gpu.fill(e, ring, s, k.a, Gpu.mulC(i, 64), k.m0, k.b, Gpu.mulC(i, 64), k.n0)
    }
    match Gpu.loopPeeled(e, steps, p, step, step) returning Pair(Ctx(m, Tiny.Load), ProducerDone(r)) with
    | Pair.mk e p => Gpu.finishProducer(e, ring, p)
  }""",
    ),
    dict(
        name="producer_changes_thread", expect="TypeMismatch", mentions="ProducerAt",
        why="Takes the producer in one elected thread, fills a stage, and hands the endpoint on for a later elect to "
            "continue. The stage and phase registers belong to the first thread; another would start from stage 0 "
            "and overwrite a stage still being read. An endpoint taken in scope `j` cannot leave it.",
        old="""      match Gpu.takeProducer(e, w, ring, p) returning Pair(Ctx(j, Tiny.One), ProducerDone(r)) with
      | Pair.mk e p => {
        match Gpu.loopPeeled(e, steps, p, step, step) returning Pair(Ctx(j, Tiny.One), ProducerDone(r)) with
        | Pair.mk e p => Gpu.finishProducer(e, ring, p)
      }
    })""",
        new="""      match Gpu.takeProducer(e, w, ring, p) returning Pair(Ctx(j, Tiny.One), ProducerDone(r)) with
      | Pair.mk e p => {
        match Gpu.loopPeeled(e, steps, p, step, step) returning Pair(Ctx(j, Tiny.One), ProducerDone(r)) with
        | Pair.mk e p => Gpu.finishProducer(e, ring, p)
      }
    })

  def producer2 {l: Lifetime}{r: Lifetime}(k: Tiny.Launch(l))(ring: Ring(r, Tiny.ring))(p: Producer(r))(m: Lifetime)
      (e: Ctx(m, Tiny.Load)): Pair(Ctx(m, Tiny.Load), ProducerAt(r, m)) :=
    Gpu.elect(e, ProducerAt(r, m), fun (j: Lifetime)(w: Elected(j))(e: Ctx(j, Tiny.One)): Pair(Ctx(j, Tiny.One), ProducerAt(r, m)) => {
      match Gpu.takeProducer(e, w, ring, p) returning Pair(Ctx(j, Tiny.One), ProducerAt(r, m)) with
      | Pair.mk e p => {
        match Gpu.acquire(e, ring, p) returning Pair(Ctx(j, Tiny.One), ProducerAt(r, m)) with
        | Pair.mk e s => Gpu.fill(e, ring, s, k.a, Gpu.lit(0), k.m0, k.b, Gpu.lit(0), k.n0)
      }
    })""",
    ),
    dict(
        name="mma_without_await", expect="TypeMismatch",
        why="Issues the first MMA on the consumer's current stage without waiting for its copies to land: "
            "`mmaFirst` reads a stage through the `Ready` that `await` hands out.",
        old="""          match Gpu.await(e, ring, c) returning Pair(Ctx(n, Tiny.One), Pair(ConsumerAt(r, j), AccPending(a, j))) with
          | Pair.mk e rd => {
            match Gpu.mmaFirst(e, w, ring, rd, t, acc)""",
        new="""          match Pair.mk(e, c) returning Pair(Ctx(n, Tiny.One), Pair(ConsumerAt(r, j), AccPending(a, j))) with
          | Pair.mk e rd => {
            match Gpu.mmaFirst(e, w, ring, rd, t, acc)""",
    ),
    dict(
        name="accumulate_into_empty", expect="TypeMismatch",
        why="Accumulates into the fresh accumulator: tensor memory is not zeroed, so the first MMA must overwrite it.",
        old="""            match Gpu.mmaFirst(e, w, ring, rd, t, acc)""",
        new="""            match Gpu.mmaNext(e, w, ring, rd, t, acc)""",
    ),
    dict(
        name="release_twice", expect="LinearUnused", mentions="c2",
        why="Releases a stage twice: the second commit would free the next stage before its MMAs are issued. Each "
            "release hands the endpoint back, so the second leaves an endpoint nothing can finish (the checker reports "
            "one linearity error per definition, and finds that one before the reuse of `used`).",
        old="""            match Gpu.mmaNext(e, w, ring, rd, t, acc) returning Pair(Ctx(n, Tiny.One), Pair(ConsumerAt(r, j), AccPending(a, j))) with
            | Pair.mk e both => {
              match both returning Pair(Ctx(n, Tiny.One), Pair(ConsumerAt(r, j), AccPending(a, j))) with
              | Pair.mk used acc => {
                match Gpu.releaseByMma(e, w, ring, used) returning Pair(Ctx(n, Tiny.One), Pair(ConsumerAt(r, j), AccPending(a, j))) with
                | Pair.mk e c => Pair.mk(e, Pair.mk(c, acc))""",
        new="""            match Gpu.mmaNext(e, w, ring, rd, t, acc) returning Pair(Ctx(n, Tiny.One), Pair(ConsumerAt(r, j), AccPending(a, j))) with
            | Pair.mk e both => {
              match both returning Pair(Ctx(n, Tiny.One), Pair(ConsumerAt(r, j), AccPending(a, j))) with
              | Pair.mk used acc => {
                match Gpu.releaseByMma(e, w, ring, used) returning Pair(Ctx(n, Tiny.One), Pair(ConsumerAt(r, j), AccPending(a, j))) with
                | Pair.mk e c => {
                  match Gpu.releaseByMma(e, w, ring, used) returning Pair(Ctx(n, Tiny.One), Pair(ConsumerAt(r, j), AccPending(a, j))) with
                  | Pair.mk e c2 => Pair.mk(e, Pair.mk(c, acc))
                }""",
    ),
    dict(
        name="loop_changes_accumulator", expect="TypeMismatch",
        why="Runs every K step, the first included, as one loop body that starts from the empty accumulator: the "
            "body is generated once, so its state must keep one type; the first step has to be peeled.",
        old="""        match Gpu.loopPeeled(e, steps, Pair.mk(c, acc), first, rest)""",
        new="""        match Gpu.loop(e, steps, Pair.mk(c, acc), first)""",
    ),
    dict(
        name="mma_never_committed", expect="LinearUnused", mentions="acc",
        why="Finishes the issuer without committing its MMAs to the handoff: the epilogue could never observe them "
            "complete, and tensor memory could be freed with MMAs in flight.",
        old="""          | Pair.mk c acc => Pair.mk(Gpu.sendAcc(e, w, hd, send, acc), Gpu.finishConsumer(c))""",
        new="""          | Pair.mk c acc => Pair.mk(e, Gpu.finishConsumer(c))""",
    ),
    dict(
        name="store_before_handoff", expect="TypeMismatch",
        why="Reads the accumulator without waiting for the issuer's commit: `storeAcc` needs `Acc(a, ready)`, which "
            "only `recvAcc` makes.",
        old="""    match Gpu.recvAcc(e, hd, recv) returning Pair(Ctx(m, Tiny.Wg1), Acc(a, AccState.ready)) with
    | Pair.mk e acc => Gpu.storeAcc(e, Eq.refl(0), t, acc, k.c, own)""",
        new="""    Gpu.storeAcc(e, Eq.refl(0), t, recv, k.c, own)""",
    ),
    dict(
        name="second_tmem_allocation", expect="LinearReused", mentions="permit",
        why="Allocates tensor memory after giving up the permit: `tcgen05.alloc` after `relinquish_alloc_permit` is "
            "illegal.",
        old="""        match Gpu.withTmem(e, permit, 128, Unit, body) returning Ctx(l, Tiny.Cta) with""",
        new="""        let gone := Gpu.skipTmem(permit)
        match Gpu.withTmem(e, permit, 128, Unit, body) returning Ctx(l, Tiny.Cta) with""",
    ),
    dict(
        name="mma_m64", expect="#error",
        why="Loads 64-row boxes of A: an M=64 accumulator is not laid out one row per tensor-memory lane, as the "
            "epilogue reads it.",
        old="""  def boxA : TmaSpec := TmaSpec.mk(64, 128)""",
        new="""  def boxA : TmaSpec := TmaSpec.mk(64, 64)""",
    ),
]
