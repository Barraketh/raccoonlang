# The A1 attention example with one mistake each (gpu/ATTENTION.md §5): every mutant breaks a rule of the attention
# core and is refused for that rule. Run by check.sh through gpu/mutate.py.
#
# §5's rows that are not refusals, and so have no mutant here:
# - Publishing P without `tcgen05.wait::st`, or without the fences: not expressible, since `publishP` and `awaitP`
#   emit them (M13).
# - Spinning in `awaitAcc` between the last `storeP` and `publishP`: allowed, and safe, since `publishP` reconverges
#   the warp before `wait::st`; `checks/emitted.rac` checks the `__syncwarp` it emits.
# - Writing a chunk of P twice: not expressible, since `storeP` takes no chunk index and writes chunk `next` of its
#   `PFree`. An extra store, at index 16 or later, is refused (`store_past_last_chunk`), and a missing one too
#   (`publish_chunk_unwritten`); a store from the wrong chunk of S is not checked (§5's "storing P chunk c from S
#   chunk c' ≠ c").
# - Using the upper half of a `splitTmem` as if it started at column 0: not expressible, since every address use adds
#   the offset through `tmemBase`; `checks/emitted.rac` checks that an MMA into the upper half carries it.
# - Storing rows of O that another CTA owns: not expressible, since `storeO` computes the rows from the block and
#   thread indices and takes none from its caller.

SOURCE = "encoding/examples/attention.rac"

MUTANTS = [
    dict(
        name="load_s_before_commit", expect="ImplicitReconstructionFailed",
        mentions="Core.loadAcc8: expected an application of Core.AccFull",
        why="Reads a chunk of S_0 before waiting for the MMA thread's commit: the tensor cores may still be writing "
            "it. `loadAcc8` reads a buffer through the `AccFull` that only `awaitAcc` makes.",
        old="""      let (e, full) := Core.awaitAcc(e, accs, c)
      let (e, lowest) := Core.fconst(e, Attn.minusInfinity)""",
        new="""      let (e, (c, early)) := Core.loadAcc8(e, accs, c, 0)
      let (e, full) := Core.awaitAcc(e, accs, c)
      let (e, lowest) := Core.fconst(e, Attn.minusInfinity)""",
    ),
    dict(
        name="load_s_after_release", expect="LinearReused", mentions="full has a linear type",
        why="Releases S_0 after pass 1, then loads it again in pass 2: the MMA thread may already be writing S_2 into "
            "the released buffer. `releaseAcc` consumes the `AccFull` that pass 2's loads need.",
        old="""      let e := Core.set(e, lReg, Core.zero(DType.f32))
      let (e, (full, p)) := Attn.pass2(accs, ex, g.scale, mNew, lReg, e, (full, p))
      let (e, c) := Core.releaseAcc(e, accs, full)""",
        new="""      let e := Core.set(e, lReg, Core.zero(DType.f32))
      let (e, c) := Core.releaseAcc(e, accs, full)
      let (e, (full, p)) := Attn.pass2(accs, ex, g.scale, mNew, lReg, e, (full, p))""",
    ),
    dict(
        name="scores_into_busy_buffer", expect="TypeMismatch", mentions="expected: Core.AccFree",
        why="Issues the next S into its buffer without waiting for the softmax warpgroup's 128 releases: the "
            "warpgroup may still be reading S_{j-1} there. `mmaScores` writes the buffer through the `AccFree` that "
            "only `acquireAcc` makes.",
        old="""        let (e, free) := Core.acquireAcc(e, accs, ap)""",
        new="""        let (e, free) := (e, ap)""",
    ),
    dict(
        name="store_p_without_acquire", expect="ImplicitReconstructionFailed",
        mentions="Core.storeP: expected an application of Core.PFree",
        why="Writes a chunk of P_j (j > 0) before waiting on P empty, while PV_{j-1} may still be reading P. `storeP` "
            "writes through the `PFree` that only `acquireP`'s wait makes.",
        old="""      let (e, p) := Core.acquireP(e, ex, wa)
      let (e, sum) := Core.reg(e, Core.zero(DType.f32))""",
        new="""      let (e, (full, early)) := Core.loadAcc8(e, accs, full, 0)
      let (e, wa) := Core.storeP(e, ex, wa, early)
      let (e, p) := Core.acquireP(e, ex, wa)
      let (e, sum) := Core.reg(e, Core.zero(DType.f32))""",
    ),
    dict(
        name="rescale_during_product", expect="ImplicitReconstructionFailed",
        mentions="Core.rescaleO: expected an application of Core.PFree",
        why="Rescales Ô before waiting on P empty, while PV_{j-1} may still be accumulating into it: a read-modify-write "
            "racing the tensor cores. `rescaleO` needs `PFree`, which only `acquireP`'s wait makes.",
        old="""      let (e, p) := Core.acquireP(e, ex, wa)
      let (e, sum) := Core.reg(e, Core.zero(DType.f32))""",
        new="""      let (e, early) := Core.ex2(e, Core.fsub(mOld, mNew))
      let (e, wa) := Core.rescaleO(e, ex, wa, early)
      let (e, p) := Core.acquireP(e, ex, wa)
      let (e, sum) := Core.reg(e, Core.zero(DType.f32))""",
    ),
    dict(
        name="rescale_first_block", expect="TypeMismatch", mentions="expected: Core.PFree(x, m, 4, Core.OState.held, 16)",
        why="Rescales Ô in the first block, before any MMA has written it: its contents are undefined. `rescaleO` "
            "needs a `PFree` whose `OState` is `held`, and the first `acquireP` gives `fresh`.",
        old="""      let (e, (full, p)) := Attn.pass2(accs, ex, g.scale, mNew, lReg, e, (full, p))
      let (e, c) := Core.releaseAcc(e, accs, full)
      let (e, wa) := Core.publishP(e, ex, p)
      (e, (c, wa))""",
        new="""      let (e, (full, p)) := Attn.pass2(accs, ex, g.scale, mNew, lReg, e, (full, p))
      let (e, c) := Core.releaseAcc(e, accs, full)
      let (e, p) := Core.rescaleO(e, ex, p, mNew)
      let (e, wa) := Core.publishP(e, ex, p)
      (e, (c, wa))""",
    ),
    dict(
        name="accumulate_first_product", expect="TypeMismatch", mentions="expected: Core.PReady(x, j, Core.OState.held)",
        why="Accumulates the first product into Ô, whose contents are undefined (tensor memory is not zeroed): the "
            "first product must overwrite. `mmaPVNext` needs `PReady(…, held)`, and the first `awaitP` gives `fresh`.",
        old="""Core.mmaPVFirst(e, w, ex, p, vr, vReady)""",
        new="""Core.mmaPVNext(e, w, ex, p, vr, vReady)""",
    ),
    dict(
        name="product_before_publish", expect="TypeMismatch", mentions="expected: Core.PReady",
        why="Issues PV_0 without waiting for the softmax warpgroup to publish P_0: the tensor cores would read P while "
            "it is being written. `mmaPVFirst` reads P through the `PReady` that only `awaitP` makes.",
        old="""        let (e, p) := Core.awaitP(e, ex, rd)
        let (e, vReady) := Core.await(e, vr, cv)
        let (e, (pUsed, vUsed)) := Core.mmaPVFirst(e, w, ex, p, vr, vReady)""",
        new="""        let (e, p) := (e, rd)
        let (e, vReady) := Core.await(e, vr, cv)
        let (e, (pUsed, vUsed)) := Core.mmaPVFirst(e, w, ex, p, vr, vReady)""",
    ),
    dict(
        name="publish_chunk_unwritten", expect="TypeMismatch", mentions="Core.PFree(x, m, 4, Core.OState.fresh, 15)",
        why="Writes chunks 0 to 14 of P and publishes: the MMA would read the previous block's probabilities in the "
            "last chunk. `publishP` needs `PFree(…, 16)`, every chunk written.",
        old="""      : Pair(Ctx(n, Attn.Wg1), Pair(AccFull(q, mm, Attn.softmaxWarp), PFree(x, mm, Attn.softmaxWarp, o, 16))) := {
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 0, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 1, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 2, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 3, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 4, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 5, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 6, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 7, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 8, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 9, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 10, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 11, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 12, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 13, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 14, e, st)
    Attn.expChunk(accs, ex, scale, mx, sum, 15, e, st)
  }""",
        new="""      : Pair(Ctx(n, Attn.Wg1), Pair(AccFull(q, mm, Attn.softmaxWarp), PFree(x, mm, Attn.softmaxWarp, o, 15))) := {
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 0, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 1, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 2, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 3, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 4, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 5, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 6, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 7, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 8, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 9, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 10, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 11, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 12, e, st)
    let (e, st) := Attn.expChunk(accs, ex, scale, mx, sum, 13, e, st)
    Attn.expChunk(accs, ex, scale, mx, sum, 14, e, st)
  }""",
    ),
    dict(
        name="store_past_last_chunk", expect="EvidenceNotDischarged", mentions="Evidence fits of Core.storeP",
        why="Writes a seventeenth chunk after P's sixteen: its store would land past P's 64 columns of tensor memory. "
            "`storeP` asks for the chunk index below 16 as evidence.",
        old="""      let (e, (full, p)) := Attn.pass2(accs, ex, g.scale, mNew, lReg, e, (full, p))
      let (e, c) := Core.releaseAcc(e, accs, full)""",
        new="""      let (e, (full, p)) := Attn.pass2(accs, ex, g.scale, mNew, lReg, e, (full, p))
      let (e, (full, extra)) := Core.loadAcc8(e, accs, full, 15)
      let (e, p) := Core.storeP(e, ex, p, extra)
      let (e, c) := Core.releaseAcc(e, accs, full)""",
    ),
    dict(
        name="store_o_before_last_product", expect="ImplicitReconstructionFailed",
        mentions="Core.storeO: expected an application of Core.OFinal",
        why="Stores O without waiting for the last product: Ô may still be accumulating PV_{n-1}. `storeO` reads Ô "
            "through the `OFinal` that only `finishExWriter`'s wait makes.",
        old="""    let (e, final) := Core.finishExWriter(e, ex, wa)""",
        new="""    let (e, final) := (e, wa)""",
    ),
    dict(
        name="store_o_twice", expect="LinearReused", mentions="own has a linear type",
        why="Stores the CTA's rows of O and LSE twice. `OOwn` is linear, and `storeO` consumes it.",
        old="""    let (e, final) := Core.storeO(e, ex, final, inv, Core.fmul(Core.fadd(mMax, logSum), ln2), g.out, own)""",
        new="""    let (e, final) := Core.storeO(e, ex, final, inv, Core.fmul(Core.fadd(mMax, logSum), ln2), g.out, own)
    let (e, final) := Core.storeO(e, ex, final, inv, Core.fmul(Core.fadd(mMax, logSum), ln2), g.out, own)""",
    ),
    dict(
        name="writer_on_one_thread", expect="ImplicitReconstructionFailed",
        mentions="Core.takeExWriter: expected a Core.Group.warps value",
        why="Takes the exchange's writing side in one thread. P full counts 128 arrivals, one per row, and each "
            "thread writes its own row of P: one thread can neither publish nor write the tile. `takeExWriter` needs "
            "a four-warp group.",
        old="""  // ---- The CTA ---""",
        new="""  def oneWriter {x: Lifetime}(ex: Exchange(x))(wr: ExWriter(x))(m: Lifetime)(e: Ctx(m, Attn.One))
      : Pair(Ctx(m, Attn.One), ExWriterAt(x, m, 0, OState.fresh)) :=
    Core.takeExWriter(e, ex, wr)

  // ---- The CTA ---""",
    ),
    dict(
        name="writer_on_warps_3_to_6", expect="EvidenceNotDischarged", mentions="Evidence aligned of Core.takeExWriter",
        why="Takes the exchange's writing side in warps 3 to 6. A warp may access only the tensor-memory lanes of its "
            "rank in an aligned warpgroup, so warp 3 would write rows 96–127 and warp 4 rows 0–31 of P: the rows "
            "would not be the warpgroup's. `takeExWriter` asks for the alignment as evidence.",
        old="""  // ---- The CTA ---""",
        new="""  def misalignedWriter {x: Lifetime}(ex: Exchange(x))(wr: ExWriter(x))(m: Lifetime)(e: Ctx(m, Group.warps(3, 4)))
      : Pair(Ctx(m, Group.warps(3, 4)), ExWriterAt(x, m, 3, OState.fresh)) :=
    Core.takeExWriter(e, ex, wr)

  // ---- The CTA ---""",
    ),
    dict(
        name="mask_by_thread_branch", expect="TypeMismatch", mentions="Core.Group.diverged(128)",
        why="Loads a chunk of S under a per-thread condition, as a causal or tail mask by `if` would: the "
            "`.sync.aligned` load would run with part of the warp. The arm's group is `diverged`, and `loadAcc8` "
            "needs an aligned warpgroup.",
        old="""    let (e, (full, s)) := Core.loadAcc8(e, accs, full, c)[fits]
    let (e, old) := Core.get(e, mx)""",
        new="""    let (e, old) := Core.get(e, mx)
    let (e, full) := Core.branch(e, Core.lt(old, Core.zero(DType.f32)), Core.fixedAccFull(q, mm, Attn.softmaxWarp), full,
      fun (b: Lifetime)(e: Ctx(b, Group.arm(Attn.Wg1, Grain.thread)))(full: AccFull(q, mm, Attn.softmaxWarp))
          : Pair(Ctx(b, Group.arm(Attn.Wg1, Grain.thread)), AccFull(q, mm, Attn.softmaxWarp)) => {
        let (e, (full, t)) := Core.loadAcc8(e, accs, full, c)[fits]
        (e, full)
      },
      fun (b: Lifetime)(e: Ctx(b, Group.arm(Attn.Wg1, Grain.thread)))(full: AccFull(q, mm, Attn.softmaxWarp))
          : Pair(Ctx(b, Group.arm(Attn.Wg1, Grain.thread)), AccFull(q, mm, Attn.softmaxWarp)) => (e, full))
    let (e, (full, s)) := Core.loadAcc8(e, accs, full, c)[fits]""",
    ),
    dict(
        name="q_released_inside_loop", expect="LinearReused", mentions="qu has a linear type",
        why="Releases the held Q stage after the first S and keeps issuing MMAs that read it: once the commit "
            "completes, the loader may overwrite the stage. `releaseByMma` consumes the `ReadyUsed` that later "
            "`mmaScores` calls need.",
        old="""        let (e, (qu, (kUsed, filling))) := Core.mmaScores(e, w, qr, qu, kr, kReady, accs, free)""",
        new="""        let (e, (qu, (kUsed, filling))) := Core.mmaScores(e, w, qr, qu, kr, kReady, accs, free)
        let (e, cq) := Core.releaseByMma(e, w, qr, qu)""",
    ),
    dict(
        name="close_with_product_in_flight", expect="TypeMismatch", mentions="Core.ExWriterDone(x)",
        why="Hands the exchange back without waiting for the last product: its tensor memory could be freed with an "
            "MMA still writing Ô. `withExchange` closes only on `ExWriterDone`, reached through `finishExWriter`'s "
            "wait.",
        old="""    let (e, final) := Core.finishExWriter(e, ex, wa)
    let (e, lSum) := Core.get(e, lReg)
    let (e, mMax) := Core.get(e, mReg)
    let (e, inv) := Core.rcp(e, lSum)
    let (e, logSum) := Core.lg2(e, lSum)
    let (e, ln2) := Core.fconst(e, Attn.ln2)
    let (e, final) := Core.storeO(e, ex, final, inv, Core.fmul(Core.fadd(mMax, logSum), ln2), g.out, own)
    (e, (Core.finishAccConsumer(c), Core.closeExWriter(final)))""",
        new="""    (e, (Core.finishAccConsumer(c), wa))""",
    ),
]
