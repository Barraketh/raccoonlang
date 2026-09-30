# The persistent GEMM with one mistake each: the tile schedule's output authority and the accumulator ring's rules
# (gpu/DESIGN.md §7) refuse the program that breaks them. Run by check.sh through gpu/mutate.py.

SOURCE = "examples/persistent_gemm.rac"

MUTANTS = [
    dict(
        name="store_tile_twice", expect="LinearReused", mentions="o",
        why="Stores a tile twice in one iteration: an iteration owns its tile once.",
        old="""      let (e, full) := Gpu.storeTile(e, accs, full, t, o, g.c)
""",
        new="""      let (e, full) := Gpu.storeTile(e, accs, full, t, o, g.c)
      let (e, full) := Gpu.storeTile(e, accs, full, t, o, g.c)
""",
    ),
    dict(
        name="forged_tile", expect="SealedConstructor",
        why="Stores the accumulator to a tile of the program's choosing rather than the iteration's: another CTA may "
            "own it.",
        old="""      let (e, full) := Gpu.storeTile(e, accs, full, t, o, g.c)
""",
        new="""      let (e, full) := Gpu.storeTile(e, accs, full, TileAt.mk(128, Gpu.tileRow0(t), Gpu.lit(0)), o, g.c)
""",
    ),
    dict(
        name="second_output_loop", expect="LinearReused", mentions="own",
        why="Loops over the CTA's tiles twice with the authority to write them: every tile would be written twice.",
        old="""    let (e, c) := Gpu.forOwnedTiles(e, sched, own, c, tile)
""",
        new="""    let (e, c) := Gpu.forOwnedTiles(e, sched, own, c, tile)
    let (e, c) := Gpu.forOwnedTiles(e, sched, own, c, tile)
""",
    ),
    dict(
        name="store_before_await", expect="ImplicitReconstructionFailed", mentions="AccFull",
        why="Reads the current accumulator without waiting for its tensor-core work: `storeTile` needs the `AccFull` "
            "that `awaitAcc` hands out.",
        old="""      let (e, full) := Gpu.awaitAcc(e, accs, c)
      let (e, full) := Gpu.storeTile(e, accs, full, t, o, g.c)
""",
        new="""      let (e, full) := Gpu.storeTile(e, accs, c, t, o, g.c)
""",
    ),
    dict(
        name="release_before_store", expect="LinearReused", mentions="full",
        why="Hands the buffer back to the issuer before reading it: the next tile's MMAs could overwrite it under the "
            "loads. Releasing consumes the buffer, so the store that follows has none.",
        old="""      let (e, full) := Gpu.storeTile(e, accs, full, t, o, g.c)
      Gpu.releaseAcc(e, accs, full)
""",
        new="""      let (e, c) := Gpu.releaseAcc(e, accs, full)
      let (e, full) := Gpu.storeTile(e, accs, full, t, o, g.c)
      Pair.mk(e, c)
""",
    ),
    dict(
        name="mma_into_busy_buffer", expect="TypeMismatch",
        why="Issues a tile's MMAs without waiting for the epilogue to free the buffer: `mmaFirstInto` needs the "
            "`AccFree` that `acquireAcc` hands out.",
        old="""        let (e, acc) := Gpu.acquireAcc(e, accs, ap)
        let (e, (c, acc)) := Gpu.loopPeeled(e, steps, Pair.mk(c, acc), first, rest)
""",
        new="""        let (e, (c, acc)) := Gpu.loopPeeled(e, steps, Pair.mk(c, ap), first, rest)
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
