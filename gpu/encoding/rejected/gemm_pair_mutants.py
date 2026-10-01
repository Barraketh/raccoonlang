# The persistent pair GEMM (encoding/examples/gemm_pair.rac, gpu/encoding/TWO_CTA.md §6 step 4) with one mistake each
# in its schedule, its accumulator ring or its TMA-store epilogue: every mutant breaks a rule and is refused, by the
# types or at generation. Run by check.sh through gpu/mutate.py. The pair protocols' own mutants are
# tinygemm_pair_mutants.py's.
#
# What is not a refusal, and so has no mutant here:
# - A tile sequence of the client's that differs between the CTAs of a pair: not expressible. The tile loops take the
#   pair's schedule, whose first tile and step (`%clusterid.x`, `%nclusterid.x`) are the core's and the same in both
#   CTAs, and no operation hands a client the rank (M18) or another value that differs between them; every uniform
#   value a client holds is a parameter, a literal or a loop index. `single_cta_schedule` tries the nearest thing, the
#   single-CTA loop from `blockIdx.x` in steps of `gridDim.x`, which differ between the CTAs.
# - A staging buffer written before the store that last read it has finished reading: not expressible. Every write
#   into a buffer needs a `StageFree`, which only `acquireStage`, the wait, makes, and which is linear.
#   `stage_twice_per_acquire` tries to write a second chunk under one wait.
# - A trip count that differs between roles: a deadlock (M11, M18), not a race.

SOURCE = "encoding/examples/gemm_pair.rac"

MUTANTS = [
    dict(
        name="store_other_rows", expect="SealedConstructor", mentions="Core.PairTile",
        why="Stores the accumulator's chunks through a tile of the caller's making, at the other CTA's rows: two CTAs "
            "would write one row of C, and this CTA's rows would stay unwritten. A chunk's rows come from the "
            "schedule's `PairTile`, computed by the core from the rank, and `PairTile` is sealed.",
        old="""      let (e, (full, sa)) := forHalfChunks(e, accs, t, o, fixedPair(fixedAccFull(q, m, 4), fixedStoreAt(s, m, 4)), (full, sa), chunk)""",
        new="""      let (e, (full, sa)) := forHalfChunks(e, accs, PairTile.mk(lit(1).expr, lit(128).expr, lit(0).expr, lit(0).expr, 256), o,
        fixedPair(fixedAccFull(q, m, 4), fixedStoreAt(s, m, 4)), (full, sa), chunk)""",
    ),
    dict(
        name="release_before_loads", expect="LinearReused", mentions="full has a linear type",
        why="Hands the accumulator back to the leader before the tile's chunks are loaded from it: the leader's next "
            "tile could overwrite the buffer while this CTA's warpgroup still reads it. `releasePairAcc` uses the "
            "buffer's `AccFull` up, and every chunk's load needs it.",
        old="""      let (e, (full, sa)) := forHalfChunks(e, accs, t, o, fixedPair(fixedAccFull(q, m, 4), fixedStoreAt(s, m, 4)), (full, sa), chunk)
      let (e, c) := releasePairAcc(e, accs, full)""",
        new="""      let (e, c) := releasePairAcc(e, accs, full)
      let (e, (full, sa)) := forHalfChunks(e, accs, t, o, fixedPair(fixedAccFull(q, m, 4), fixedStoreAt(s, m, 4)), (full, sa), chunk)""",
    ),
    dict(
        name="stage_twice_per_acquire", expect="LinearReused", mentions="free has a linear type",
        why="Writes a second chunk into the staging buffer right after issuing the store that reads it, with no wait: "
            "the TMA store could read the second chunk's values, or a mix. A write needs a `StageFree`, which only "
            "`acquireStage`'s wait makes, and which the first write uses up.",
        old="""      let (e, sa) := storeStage(e, stg, fenced, g.c, ch, co)
      (e, (full, sa))""",
        new="""      let (e, sa) := storeStage(e, stg, fenced, g.c, ch, co)
      let (e, (full, again)) := stagePairAcc(e, accs, full, stg, free, ch)
      (e, (full, sa))""",
    ),
    dict(
        name="stores_unfinished", expect="LinearUnused", mentions="sa has a linear type",
        why="Ends the epilogue without waiting for its stores: the pair could close and the CTAs exit while TMA stores "
            "still read the staging buffers. The storing side is linear and belongs to the staging scope, and only "
            "`finishStores`, which waits for every bulk group to complete, uses it up.",
        old="""    (finishAccConsumer(finishStores(e, stg, sa), c), Unit.unit)""",
        new="""    (finishAccConsumer(e, c), Unit.unit)""",
    ),
    dict(
        name="single_cta_schedule", expect="ImplicitReconstructionFailed", mentions="Core.Sched",
        why="Runs the producer's tile loop as a single-CTA kernel's, from `blockIdx.x` in steps of `gridDim.x`: the two "
            "CTAs of a pair would load different tiles' halves into one stage. The pair's schedule is a `PairSched`, "
            "which only the pair loops take.",
        old="""      let (e, p) := forPairTiles(e, sched, fixedProducerAt(r, j), p, tile)""",
        new="""      let (e, p) := forTiles(e, sched, fixedProducerAt(r, j), p, tile)""",
    ),
    dict(
        name="shared_memory_over", expect="EvidenceNotDischarged", mentions="more than sm_100a's 232448",
        why="Deepens the ring to seven stages: 7 × 32 KB of stages and 32 KB of staging buffers exceed what a CTA may "
            "have. The kernel's dynamic shared memory is checked against sm_100a's limit when it is rendered.",
        old="""  def ringCfg : RingCfg := RingCfg.mk(6, boxA, boxB)""",
        new="""  def ringCfg : RingCfg := RingCfg.mk(7, boxA, boxB)""",
    ),
]
