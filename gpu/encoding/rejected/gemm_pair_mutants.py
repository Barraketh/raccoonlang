# The persistent pair GEMM (encoding/examples/gemm_pair.rac, gpu/encoding/TWO_CTA.md §6 step 4) with one mistake each
# in its schedule, its accumulator ring or its TMA-store epilogue: every mutant breaks a rule and is refused, by the
# types or at generation. Run by check.sh through gpu/mutate.py. The pair protocols' own mutants are
# tinygemm_pair_mutants.py's.
#
# What is not a refusal, and so has no mutant here:
# - A tile sequence of the client's that differs between the CTAs of a pair: not expressible. The tile loops take the
#   pair's schedule, whose first tile and step (`%clusterid.x`, `%nclusterid.x`) are the core's and the same in both
#   CTAs; no operation hands a client the rank (M18) or another value that differs between them; and code that runs
#   in one CTA only, an `onLeader` arm, uses up only leader-only sides, so it cannot run a role's tile loop, whose sides
#   both CTAs must finish. `single_cta_schedule` tries the single-CTA loop from `blockIdx.x` in steps of `gridDim.x`,
#   which differ between the CTAs; `producer_extra_on_leader` and `epilogue_on_leader` run a role's loop in the leader
#   only.
# - A staging buffer written before the store that last read it has finished reading: not expressible. Every write
#   into a buffer needs a `StageFree`, which only `acquireStage`, the wait, makes, and which is linear.
#   `stage_twice_per_acquire` tries to write a second chunk under one wait.
# - A trip count that differs between roles: a deadlock (M11, M18), not a race.

SOURCE = "encoding/examples/gemm_pair.rac"

# The pair threaded into the producer and the epilogue, for the mutants that give them an `onLeader` arm.
PRODUCER_SIG = '  def producer {l: Lifetime}{L: Lifetime}{r: Lifetime}(g: Gemm(l))', '  def producer {l: Lifetime}{L: Lifetime}{r: Lifetime}(pair: CtaPair(l))(g: Gemm(l))'
PRODUCER_CALL = 'producer(g, sched, ring, steps, p, m, e)', 'producer(pair, g, sched, ring, steps, p, m, e)'
EPILOGUE_SIG = '  def epilogue {l: Lifetime}{q: Lifetime}{s: Lifetime}(g: Gemm(l))', '  def epilogue {l: Lifetime}{q: Lifetime}{s: Lifetime}(pair: CtaPair(l))(g: Gemm(l))'
EPILOGUE_CALL = 'epilogue(g, sched, own, accs, ac, stg, side, m, e)', 'epilogue(pair, g, sched, own, accs, ac, stg, side, m, e)'

MUTANTS = [
    dict(
        name="store_other_rows", expect="SealedConstructor", mentions="Core.PairTile",
        why="Stores the accumulator's chunks through a tile of the caller's making, at the other CTA's rows: two CTAs "
            "would write one row of C, and this CTA's rows would stay unwritten. A chunk's rows come from the "
            "schedule's `PairTile`, computed by the core from the rank, and `PairTile` is sealed.",
        old="""      let (e, (full, sa)) := forHalfChunks(e, t, o, fixedPair(fixedAccFull(q, m, 4), fixedStoreAt(s, m, 4)), (full, sa), chunk)""",
        new="""      let (e, (full, sa)) := forHalfChunks(e, PairTile.mk(lit(1).expr, lit(128).expr, lit(0).expr, lit(0).expr), o,
        fixedPair(fixedAccFull(q, m, 4), fixedStoreAt(s, m, 4)), (full, sa), chunk)""",
    ),
    dict(
        name="release_before_loads", expect="LinearReused", mentions="full has a linear type",
        why="Hands the accumulator back to the leader before the tile's chunks are loaded from it: the leader's next "
            "tile could overwrite the buffer while this CTA's warpgroup still reads it. `releasePairAcc` uses the "
            "buffer's `AccFull` up, and every chunk's load needs it.",
        old="""      let (e, (full, sa)) := forHalfChunks(e, t, o, fixedPair(fixedAccFull(q, m, 4), fixedStoreAt(s, m, 4)), (full, sa), chunk)
      let (e, c) := releasePairAcc(e, accs, full)""",
        new="""      let (e, c) := releasePairAcc(e, accs, full)
      let (e, (full, sa)) := forHalfChunks(e, t, o, fixedPair(fixedAccFull(q, m, 4), fixedStoreAt(s, m, 4)), (full, sa), chunk)""",
    ),
    dict(
        name="stage_twice_per_acquire", expect="LinearReused", mentions="free has a linear type",
        why="Writes a second chunk into the staging buffer right after issuing the store that reads it, with no wait: "
            "the TMA store could read the second chunk's values, or a mix. A write needs a `StageFree`, which only "
            "`acquireStage`'s wait makes, and which the first write uses up.",
        old="""      let (e, sa) := storeStage(e, stg, fenced, g.c, ch, co)
      (e, (full, sa))""",
        new="""      let (e, sa) := storeStage(e, stg, fenced, g.c, ch, co)
      let (e, again) := writeStage(e, stg, free, regs)
      (e, (full, sa))""",
    ),
    dict(
        name="stores_unfinished", expect="LinearUnused", mentions="sa has a linear type",
        why="Ends the epilogue without waiting for its stores: the pair could close and the CTAs exit while TMA stores "
            "still read the staging buffers. The storing side is linear and belongs to the staging scope, and only "
            "`finishStores`, which waits for every bulk group to complete, uses it up, in code both CTAs run "
            "(`peer_skips_store_wait`).",
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
    dict(
        name="peer_skips_store_wait", expect="TypeMismatch", mentions="closures differ in kind",
        why="Waits for the epilogue's stores in the leader only: the peer's lane 0s would reach the close, the "
            "deallocation and exit with TMA stores still reading their staging buffers. An `onLeader` arm captures no "
            "linear value, so it cannot use up the storing side, which each CTA must finish.",
        edits=[EPILOGUE_SIG, EPILOGUE_CALL,
               ("""    (finishAccConsumer(finishStores(e, stg, sa), c), Unit.unit)""",
                """    (finishAccConsumer(onLeader(e, pair, leaderOnlyUnit, Unit.unit, fun (n: Lifetime)(lead: Leader(n))(e: Ctx(n, Wg))(u: Unit): Ctx(n, Wg) =>
      finishStores(e, stg, sa)), c), Unit.unit)""")],
    ),
    dict(
        name="peer_skips_drain", expect="TypeMismatch", mentions="closures differ in kind",
        why="Runs the producer's tail in the leader only: the peer could invalidate its `empty[s]` while the leader's "
            "multicast commits still arrive there. An `onLeader` arm captures no linear value, so it cannot use up a "
            "producer, which each CTA must drain.",
        edits=[PRODUCER_SIG, PRODUCER_CALL,
               ("""      (finishPairProducer(e, ring, p), Unit.unit)""",
                """      (onLeader(e, pair, leaderOnlyUnit, Unit.unit, fun (n: Lifetime)(lead: Leader(n))(e: Ctx(n, One))(u: Unit): Ctx(n, One) =>
        finishPairProducer(e, ring, p)), Unit.unit)""")],
    ),
    dict(
        name="producer_extra_on_leader", expect="TypeMismatch", mentions="closures differ in kind",
        why="Runs the producer's tile loop a second time in the leader only: the CTAs' producers would fill different "
            "numbers of stages, and the pair would deadlock. An `onLeader` arm captures no linear value, so it cannot "
            "take the producer.",
        edits=[PRODUCER_SIG, PRODUCER_CALL,
               ("""      (finishPairProducer(e, ring, p), Unit.unit)""",
                """      (onLeader(e, pair, leaderOnlyUnit, Unit.unit, fun (n: Lifetime)(lead: Leader(n))(e: Ctx(n, One))(u: Unit): Ctx(n, One) => {
        let (e, p) := forPairTiles(e, sched, fixedProducerAt(r, j), p, tile)
        finishPairProducer(e, ring, p)
      }), Unit.unit)""")],
    ),
    dict(
        name="epilogue_on_leader", expect="TypeMismatch", mentions="closures differ in kind",
        why="Runs the epilogue's tile loop in the leader only: the peer would never store its rows nor release an "
            "accumulator, and the leader would wait for it forever. An `onLeader` arm captures no linear value, so it "
            "cannot use up the epilogue's sides or its tiles' authority.",
        edits=[EPILOGUE_SIG, EPILOGUE_CALL,
               ("""    let (e, (c, sa)) := forOwnedPairTiles(e, sched, own, fixedPair(fixedAccConsumerAt(q, m, 4), fixedStoreAt(s, m, 4)), (c, sa), tile)
    (finishAccConsumer(finishStores(e, stg, sa), c), Unit.unit)""",
                """    (onLeader(e, pair, leaderOnlyUnit, Unit.unit, fun (n: Lifetime)(lead: Leader(n))(e: Ctx(n, Wg))(u: Unit): Ctx(n, Wg) => {
      let (e, (c, sa)) := forOwnedPairTiles(e, sched, own, fixedPair(fixedAccConsumerAt(q, m, 4), fixedStoreAt(s, m, 4)), (c, sa), tile)
      finishAccConsumer(finishStores(e, stg, sa), c)
    }), Unit.unit)""")],
    ),
]
