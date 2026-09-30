# The persistent GEMM with one mistake each: the tile schedule's output authority, the accumulator ring's rules and the
# staging protocol of the TMA stores (gpu/DESIGN.md §2, §4, §6) refuse the program that breaks them. Run by check.sh through gpu/mutate.py.

SOURCE = "examples/persistent_gemm.rac"

MUTANTS = [
    dict(
        name="store_tile_twice", expect="LinearReused", mentions="o",
        why="Stores a tile twice in one iteration: an iteration owns its tile once.",
        old="""      let (e, (full, sa)) := Gpu.forChunks(e, t, o, Gpu.fixedPair(Gpu.fixedAccFull(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (full, sa), chunk)
""",
        new="""      let (e, (full, sa)) := Gpu.forChunks(e, t, o, Gpu.fixedPair(Gpu.fixedAccFull(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (full, sa), chunk)
      let (e, (full, sa)) := Gpu.forChunks(e, t, o, Gpu.fixedPair(Gpu.fixedAccFull(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (full, sa), chunk)
""",
    ),
    dict(
        name="forged_tile", expect="SealedConstructor",
        why="Stores the accumulator to a tile of the program's choosing rather than the iteration's: another CTA may "
            "own it.",
        old="""      let (e, (full, sa)) := Gpu.forChunks(e, t, o, Gpu.fixedPair(Gpu.fixedAccFull(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (full, sa), chunk)
""",
        new="""      let (e, (full, sa)) := Gpu.forChunks(e, TileAt.mk(128, Gpu.tileRow0(t), Gpu.lit(0)), o,
        Gpu.fixedPair(Gpu.fixedAccFull(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (full, sa), chunk)
""",
    ),
    dict(
        name="second_output_loop", expect="LinearReused", mentions="own",
        why="Loops over the CTA's tiles twice with the authority to write them: every tile would be written twice.",
        old="""    let (e, (c, sa)) := Gpu.forOwnedTiles(e, sched, own, Gpu.fixedPair(Gpu.fixedAccConsumerAt(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (c, sa), tile)
""",
        new="""    let (e, (c, sa)) := Gpu.forOwnedTiles(e, sched, own, Gpu.fixedPair(Gpu.fixedAccConsumerAt(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (c, sa), tile)
    let (e, (c, sa)) := Gpu.forOwnedTiles(e, sched, own, Gpu.fixedPair(Gpu.fixedAccConsumerAt(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (c, sa), tile)
""",
    ),
    dict(
        name="store_before_await", expect="TypeMismatch", mentions="AccFull",
        why="Reads the current accumulator without waiting for its tensor-core work: `stageAccFull` needs the "
            "`AccFull` that `awaitAcc` hands out.",
        old="""      let (e, full) := Gpu.awaitAcc(e, accs, c)
      let (e, (full, sa)) := Gpu.forChunks(e, t, o, Gpu.fixedPair(Gpu.fixedAccFull(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (full, sa), chunk)
""",
        new="""      let (e, (full, sa)) := Gpu.forChunks(e, t, o, Gpu.fixedPair(Gpu.fixedAccFull(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (c, sa), chunk)
""",
    ),
    dict(
        name="release_before_store", expect="LinearReused", mentions="full",
        why="Hands the buffer back to the issuer before reading it: the next tile's MMAs could overwrite it under the "
            "loads. Releasing consumes the buffer, so the chunks that follow have none.",
        old="""      let (e, (full, sa)) := Gpu.forChunks(e, t, o, Gpu.fixedPair(Gpu.fixedAccFull(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (full, sa), chunk)
      let (e, c) := Gpu.releaseAcc(e, accs, full)
""",
        new="""      let (e, c) := Gpu.releaseAcc(e, accs, full)
      let (e, (full, sa)) := Gpu.forChunks(e, t, o, Gpu.fixedPair(Gpu.fixedAccFull(q, m, 4), Gpu.fixedStoreAt(s, m, 4)), (full, sa), chunk)
""",
    ),
    dict(
        name="mma_into_busy_buffer", expect="TypeMismatch",
        why="Issues a tile's MMAs without waiting for the epilogue to free the buffer: `mmaFirstInto` needs the "
            "`AccFree` that `acquireAcc` hands out.",
        old="""        let (e, acc) := Gpu.acquireAcc(e, accs, ap)
        let (e, (c, acc)) := Gpu.loopPeeled(e, steps,
          Gpu.fixedPair(Gpu.fixedConsumerAt(r, j), Gpu.fixedAccFilling(q, j)), (c, acc), first, rest)
""",
        new="""        let (e, (c, acc)) := Gpu.loopPeeled(e, steps,
          Gpu.fixedPair(Gpu.fixedConsumerAt(r, j), Gpu.fixedAccFilling(q, j)), (c, ap), first, rest)
""",
    ),
    dict(
        name="stage_before_wait", expect="ImplicitReconstructionFailed", mentions="StageFree",
        why="Writes the staging buffer without waiting for the store that last read it, two stores ago: lane 0's "
            "`cp.async.bulk.wait_group.read` is what frees it, and `stageAccFull` needs the `StageFree` that "
            "`acquireStage` hands out.",
        old="""      let (e, free) := Gpu.acquireStage(e, stg, sa)
      let (e, (full, written)) := Gpu.stageAccFull(e, accs, full, stg, free, ch)
""",
        new="""      let (e, (full, written)) := Gpu.stageAccFull(e, accs, full, stg, sa, ch)
""",
    ),
    dict(
        name="store_before_fence", expect="ImplicitReconstructionFailed", mentions="StageFenced",
        why="Issues the TMA store without the proxy fence: the threads' `st.shared` writes are not ordered before "
            "the async proxy's reads of the buffer. `storeStage` needs the `StageFenced` that `fenceStage` makes.",
        old="""      let (e, fenced) := Gpu.fenceStage(e, written)
      let (e, sa) := Gpu.storeStage(e, stg, fenced, g.c, ch, co)
""",
        new="""      let (e, sa) := Gpu.storeStage(e, stg, written, g.c, ch, co)
""",
    ),
    dict(
        name="stores_waited_by_one_warp", expect="TypeMismatch", mentions="warps",
        why="Waits for the stores on warp 4 alone: bulk async-groups are counted per thread, so lane 0 of warp 4 "
            "cannot wait for the stores lanes 0 of warps 5 to 7 issued, which could still be reading their staging "
            "buffers. The storing side is the whole warpgroup's; `finishStores` needs its context.",
        old="""    let (e, done) := Gpu.finishStores(e, stg, sa)
""",
        new="""    let (e, (done, u)) := Gpu.split(e, 1, StoreDone(s), Unit,
      fun (n: Lifetime)(e: Ctx(n, Group.warps(4, 1))): Pair(Ctx(n, Group.warps(4, 1)), StoreDone(s)) => Gpu.finishStores(e, stg, sa),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(5, 3))): Pair(Ctx(n, Group.warps(5, 3)), Unit) => (e, Unit.unit))
""",
    ),
    dict(
        name="stores_in_flight_at_exit", expect="TypeMismatch", mentions="StoreDone",
        why="Ends the epilogue without waiting for its stores: they could still be reading the staging buffers when "
            "their shared memory is released, and writing C when the kernel ends. Only `finishStores` makes the "
            "`StoreDone` that `withStaging` requires.",
        old="""    let (e, done) := Gpu.finishStores(e, stg, sa)
    (e, (Gpu.finishAccConsumer(c), done))
""",
        new="""    (e, (Gpu.finishAccConsumer(c), sa))
""",
    ),
    dict(
        name="band_of_no_rows", expect="EvidenceNotDischarged", mentions="schedule: a band must have at least one tile row",
        why="Orders the tiles in bands of zero tile rows: tile index t would lie in band t / 0, so the order would be "
            "no bijection onto the tiles. The schedule is the builder's; a program chooses only the band's height, "
            "which must be positive.",
        old="""  def band : Nat := 16
""",
        new="""  def band : Nat := 0
""",
    ),
    dict(
        name="accumulators_not_drained", expect="TypeMismatch",
        why="Finishes the issuer without waiting for the epilogue to read every buffer: tensor memory could be freed "
            "under the last loads. Only `finishAccProducer` makes `AccProducerDone`.",
        old="""      let (e, apDone) := Gpu.finishAccProducer(e, accs, ap)
""",
        new="""      let apDone := ap
""",
    ),
]
