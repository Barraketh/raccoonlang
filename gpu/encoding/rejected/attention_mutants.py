# The attention roles (encoding/Attention.rac, which the attention examples run) with one mistake each
# (gpu/ATTENTION.md §5): every mutant breaks a rule of the attention core and is refused for that rule. Run by check.sh
# through gpu/mutate.py.
#
# §5's rows that are not refusals, and so have no mutant here:
# - Publishing P without `tcgen05.wait::st`, or without the fences: not expressible, since `publishP` and `awaitP`
#   emit them (M13).
# - Spinning in `awaitAcc` between writing P and `publishP`: allowed, and safe, since `publishP` reconverges the warp
#   before `wait::st`; `checks/emitted.rac` checks the `__syncwarp` it emits.
# - Writing a chunk of P twice, or past P's 16 (formerly `store_past_last_chunk`), or publishing with a chunk unwritten
#   after the others: not expressible. `writeP` writes the 16 chunks itself, in order, once each, and the per-chunk
#   store it unrolls is internal; the only way to a publishable `PFree(…, 16)` is `writeP` from `acquireP`'s
#   `PFree(…, 0)`. What remains expressible, publishing before writing P at all, is `publish_chunk_unwritten`.
# - Reading S chunk c′ ≠ c for P's chunk c: a step of `writeP` is handed chunk c of S only; another chunk's values
#   could reach it only through a register, a wrong result (§5's "storing P chunk c from S chunk c′ ≠ c").
# - Rescaling Ô in the first block (formerly `rescale_first_block`): no longer a mistake. `rescaleO` on a `fresh` Ô,
#   which holds nothing, emits no code, so the softmax role writes one body for every block.
# - Accumulating the first product into undefined Ô (formerly `accumulate_first_product`): not expressible. One
#   `mmaPV` overwrites exactly when its `PReady` is `fresh`, so the issuer writes one body for every block.
# - Closing the exchange, the S ring or a stage ring with a side unfinished: with no `…Done` token to return, a side
#   is linear and belongs to its protocol's scope, so it must be used up inside the callback, and only its finisher
#   uses it up without handing it on. `close_with_product_in_flight` and `close_s_ring_undrained` leave one unfinished
#   and are refused as unused; returning one out of a role or a callback cannot even be written, since no result type
#   bound outside the role or protocol can name its scope.
# - Loading one half of a stage from the other tensor's map, or at another row or column (the examples' loaders): not
#   expressible. `fillBlock` takes one head map and one row for both 64-wide halves, at columns 0 and 64, as
#   `fillPage` does; `fill`, which takes two maps and four coordinates, takes `TMap`s, which an attention kernel has
#   none of. Loading V into the K ring is still a wrong result (§5, "the wrong data in a ring").
# - Using the upper half of a `splitTmem` as if it started at column 0: not expressible, since every address use adds
#   the offset through `tmemBase`; `checks/emitted.rac` checks that an MMA into the upper half carries it.
# - Storing rows of O that another CTA owns, or a row past `seq` (the next head's): not expressible, since `storeO`
#   computes the rows and their guard from the block and thread indices and the kernel's `seq`, and takes none from
#   its caller.
# - Omitting the mask, or masking against the wrong block or chunk: a wrong result, not a refusal (§5, "what the design
#   cannot refuse"); the harness's causal and tail sizes catch it.

SOURCE = "encoding/Attention.rac"

MUTANTS = [
    dict(
        name="load_s_before_commit", expect="ImplicitReconstructionFailed",
        mentions="Core.eachChunk: expected an application of Core.AccFull",
        why="Reads the chunks of S_j before waiting for the MMA thread's commit: the tensor cores may still be writing "
            "them. `eachChunk` reads a buffer through the `AccFull` that only `awaitAcc` makes.",
        old="""      let (e, full) := awaitAcc(e, accs, c)
      let (e, mOld) := get(e, mReg)""",
        new="""      let (e, c) := eachChunk(e, accs, c, fun (ch: Nat)(s: F32x8(n, Grain.thread))(e: Ctx(n, Wg)): Ctx(n, Wg) => e)
      let (e, full) := awaitAcc(e, accs, c)
      let (e, mOld) := get(e, mReg)""",
    ),
    dict(
        name="load_s_after_release", expect="LinearReused", mentions="full has a linear type",
        why="Releases S_j after pass 1, then reads it again in pass 2: the MMA thread may already be writing S_{j+2} "
            "into the released buffer. `releaseAcc` consumes the `AccFull` that pass 2's `writeP` needs.",
        old="""      let (e, sum) := reg(e, zero(DType.f32))""",
        new="""      let (e, sum) := reg(e, zero(DType.f32))
      let (e, c) := releaseAcc(e, accs, full)""",
    ),
    dict(
        name="scores_into_busy_buffer", expect="TypeMismatch", mentions="expected: Core.AccFree",
        why="Issues the next S into its buffer without waiting for the softmax warpgroup's 128 releases: the "
            "warpgroup may still be reading S_{j-1} there. `mmaScores` writes the buffer through the `AccFree` that "
            "only `acquireAcc` makes.",
        old="""        let (e, free) := acquireAcc(e, accs, ap)""",
        new="""        let (e, free) := (e, ap)""",
    ),
    dict(
        name="store_p_without_acquire", expect="ImplicitReconstructionFailed",
        mentions="Core.writeP: expected an application of Core.PFree",
        why="Writes P_j (j > 0) without waiting on P empty, while PV_{j-1} may still be reading P. `writeP` writes "
            "through the `PFree` that only `acquireP`'s wait makes.",
        old="""      let (e, p) := acquireP(e, ex, wa)
      let (e, sum) := reg(e, zero(DType.f32))""",
        new="""      let (e, p) := (e, wa)
      let (e, sum) := reg(e, zero(DType.f32))""",
    ),
    dict(
        name="rescale_during_product", expect="ImplicitReconstructionFailed",
        mentions="Core.rescaleO: expected an application of Core.PFree",
        why="Rescales Ô before waiting on P empty, while PV_{j-1} may still be accumulating into it: a read-modify-write "
            "racing the tensor cores. `rescaleO` needs `PFree`, which only `acquireP`'s wait makes.",
        old="""      let (e, p) := acquireP(e, ex, wa)
      let (e, sum) := reg(e, zero(DType.f32))""",
        new="""      let (e, early) := ex2(e, fsub(mOld, mNew))
      let (e, wa) := rescaleO(e, ex, wa, early)
      let (e, p) := acquireP(e, ex, wa)
      let (e, sum) := reg(e, zero(DType.f32))""",
    ),
    dict(
        name="product_before_publish", expect="ImplicitReconstructionFailed",
        mentions="Core.mmaPV: expected an application of Core.PReady",
        why="Issues PV_j without waiting for the softmax warpgroup to publish P_j: the tensor cores would read P while "
            "it is being written. `mmaPV` reads P through the `PReady` that only `awaitP` makes.",
        old="""        let (e, p) := awaitP(e, ex, rd)""",
        new="""        let (e, p) := (e, rd)""",
    ),
    dict(
        name="publish_chunk_unwritten", expect="TypeMismatch", mentions="Core.PFree(x, m, 4, o, 0)",
        why="Publishes P before writing it: the MMA would read the previous block's probabilities, or, in the first "
            "block, uninitialized tensor memory. `publishP` needs `PFree(…, 16)`, which only `writeP` makes, from "
            "`acquireP`'s `PFree(…, 0)`.",
        old="""      let (e, sum) := reg(e, zero(DType.f32))""",
        new="""      let (e, wa) := publishP(e, ex, p)
      let (e, sum) := reg(e, zero(DType.f32))""",
    ),
    dict(
        name="store_o_before_last_product", expect="ImplicitReconstructionFailed",
        mentions="Core.storeO: expected an application of Core.OFinal",
        why="Stores O without waiting for the last product: Ô may still be accumulating PV_{n-1}. `storeO` reads Ô "
            "through the `OFinal` that only `finishExWriter`'s wait makes.",
        old="""    let (e, final) := finishExWriter(e, ex, wa)""",
        new="""    let (e, final) := (e, wa)""",
    ),
    dict(
        name="store_o_twice", expect="LinearReused", mentions="own has a linear type",
        why="Stores the CTA's rows of O and LSE twice. `OOwn` is linear, and `storeO` consumes it.",
        old="""    let (e, final) := storeO(e, ex, final, inv, fmul(fadd(mMax, logSum), ln2), out, own)""",
        new="""    let (e, final) := storeO(e, ex, final, inv, fmul(fadd(mMax, logSum), ln2), out, own)
    let (e, final) := storeO(e, ex, final, inv, fmul(fadd(mMax, logSum), ln2), out, own)""",
    ),
    dict(
        name="writer_on_one_thread", expect="ImplicitReconstructionFailed",
        mentions="Core.takeExWriter: expected a Core.Group.warps value",
        why="Takes the exchange's writing side in one thread. P full counts 128 arrivals, one per row, and each "
            "thread writes its own row of P: one thread can neither publish nor write the tile. `takeExWriter` needs "
            "a four-warp group.",
        old="""  // ---- The CTA ---""",
        new="""  def oneWriter {x: Lifetime}(ex: Exchange(x))(wr: ExWriter(x))(m: Lifetime)(e: Ctx(m, One))
      : Pair(Ctx(m, One), ExWriterAt(x, m, 0, OState.fresh)) :=
    takeExWriter(e, ex, wr)

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
    takeExWriter(e, ex, wr)

  // ---- The CTA ---""",
    ),
    dict(
        name="mask_by_thread_branch", expect="TypeMismatch", mentions="Core.Group.diverged(128)",
        why="Reads the chunks of S under a per-thread condition, as a causal or tail mask by `if` would (instead of "
            "`maskedScores`' selects): the `.sync.aligned` loads would run with part of the warp. The arm's group is "
            "`diverged`, and `eachChunk` needs an aligned warpgroup.",
        old="""      let (e, mOld) := get(e, mReg)""",
        new="""      let (e, mOld) := get(e, mReg)
      let (e, full) := branch(e, Core.lt(mOld, zero(DType.f32)), fixedAccFull(q, m, groupWarp), full,
        fun (b: Lifetime)(e: Ctx(b, Group.arm(Wg, Grain.thread)))(full: AccFull(q, m, groupWarp))
            : Pair(Ctx(b, Group.arm(Wg, Grain.thread)), AccFull(q, m, groupWarp)) =>
          eachChunk(e, accs, full, fun (ch: Nat)(s: F32x8(b, Grain.thread))(e: Ctx(b, Group.arm(Wg, Grain.thread))): Ctx(b, Group.arm(Wg, Grain.thread)) => e),
        fun (b: Lifetime)(e: Ctx(b, Group.arm(Wg, Grain.thread)))(full: AccFull(q, m, groupWarp))
            : Pair(Ctx(b, Group.arm(Wg, Grain.thread)), AccFull(q, m, groupWarp)) => (e, full))""",
    ),
    dict(
        name="mask_in_thread_branch", expect="ImplicitReconstructionFailed",
        mentions="Core.maskedScores: expected a Core.Group.warps value, got Core.Group.diverged(128)",
        why="Masks a chunk inside a per-thread branch: in the causal kernel `maskedScores` runs `__syncwarp` and a "
            "full-mask `__shfl_sync` for the thread's row, which part of a warp must not run alone. The arm's group is "
            "`diverged`, and `maskedScores` needs a converged `warps(f, 4)` group.",
        old="""        let (e, t) := scores(mask, i, scale, ch, s, e)
        raiseMax(mReg, t, e)""",
        new="""        let (e, t) := scores(mask, i, scale, ch, s, e)
        let (e, old) := get(e, mReg)
        let (e, u) := branch(e, Core.lt(old, zero(DType.f32)), fixedUnit, Unit.unit,
          fun (b: Lifetime)(e: Ctx(b, Group.arm(Wg, Grain.thread)))(u: Unit): Pair(Ctx(b, Group.arm(Wg, Grain.thread)), Unit) => {
            let (e, again) := maskedScores(e, mask, i, ch, t)
            (e, u)
          },
          fun (b: Lifetime)(e: Ctx(b, Group.arm(Wg, Grain.thread)))(u: Unit): Pair(Ctx(b, Group.arm(Wg, Grain.thread)), Unit) => (e, u))
        raiseMax(mReg, t, e)""",
    ),
    dict(
        name="forged_mask", expect="SealedConstructor", mentions="Core.Mask",
        why="Masks the scores with a mask of its own, non-causal and with a sequence length of its choosing, in the "
            "causal kernel: rows would attend to later keys, or to keys past `seq` (the next head's). Only the "
            "kernel builders make a `Mask`.",
        old="""    maskedScores(e, mask, block, c, F32x8.mk(""",
        new="""    maskedScores(e, Mask.mk(n, Expr.param("BH"), Bool.false, Expr.param("seq"), Core.rowInHead), block, c, F32x8.mk(""",
    ),
    dict(
        name="q_released_inside_loop", expect="LinearReused", mentions="qu has a linear type",
        why="Releases the held Q stage after the first S and keeps issuing MMAs that read it: once the commit "
            "completes, the loader may overwrite the stage. `releaseByMma` consumes the `ReadyUsed` that later "
            "`mmaScores` calls need.",
        old="""        let (e, (qu, (kUsed, filling))) := mmaScores(e, w, qr, qu, kr, kReady, accs, free)""",
        new="""        let (e, (qu, (kUsed, filling))) := mmaScores(e, w, qr, qu, kr, kReady, accs, free)
        let (e, cq) := releaseByMma(e, w, qr, qu)""",
    ),
    dict(
        name="close_with_product_in_flight", expect="LinearUnused", mentions="wa",
        why="Ends the softmax role without waiting for the last product: the exchange would close, and its tensor "
            "memory be freed, with an MMA still writing Ô. The writing side is linear and belongs to the exchange's "
            "scope, and only `finishExWriter`'s wait (then `closeExWriter`) uses it up.",
        old="""    let (e, final) := finishExWriter(e, ex, wa)
    let (e, lSum) := get(e, lReg)
    let (e, mMax) := get(e, mReg)
    let (e, inv) := rcp(e, lSum)
    let (e, logSum) := lg2(e, lSum)
    let (e, ln2) := fconst(e, ln2)
    let (e, final) := storeO(e, ex, final, inv, fmul(fadd(mMax, logSum), ln2), out, own)
    let e := finishAccConsumer(e, c)
    (closeExWriter(e, final), Unit.unit)""",
        new="""    let e := finishAccConsumer(e, c)
    (e, Unit.unit)""",
    ),
    dict(
        name="close_s_ring_undrained", expect="LinearUnused", mentions="ap",
        why="Ends the issuer without waiting until the softmax warpgroup has read every S buffer: the S ring would "
            "close, and its tensor memory be reused, while the warpgroup still reads S. The issuing side is linear "
            "and belongs to the ring's scope, and only `finishAccProducer`'s drain uses it up.",
        old="""      let e := finishAccProducer(e, accs, ap)""",
        new="""""",
    ),
    dict(
        name="scores_before_product", expect="TypeMismatch", mentions="Core.Holding",
        why="Issues tile 0's next scores before its product in the two-tile issuer (`pairIssuer`, A3a and A3b): S_{i+1} would overwrite P_i while PV_i has not yet read it. "
            "After `awaitProbs` the buffer is `Published`, which only `issuePV` takes; `issueScores` needs the `Holding` "
            "that the product gives back.",
        old="""        let (e, (s0, v)) := product(e, b0, s0, v)
        let (e, k) := hold(e, kr, ck)
        let (e, (s0, (q0, k))) := issueS(e, b0, s0, q0r, q0, k)""",
        new="""        let (e, published) := awaitProbs(e, b0, s0)
        let (e, k) := hold(e, kr, ck)
        let (e, (s0, (q0, k))) := issueScores(e, w, b0, published, q0r, q0, kr, k)
        let (e, (s0, v)) := issuePV(e, w, b0, s0, vr, v)
        let (e, s0) := commitBuffer(e, w, b0, s0)""",
    ),
]
