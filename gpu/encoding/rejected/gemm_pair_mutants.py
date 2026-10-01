# The persistent pair GEMM (encoding/examples/gemm_pair.rac, gpu/encoding/TWO_CTA.md §6 step 4) with one mistake each
# in its schedule, its accumulator ring or its TMA-store epilogue: every mutant breaks a rule and is refused, by the
# types or at generation. Run by check.sh through gpu/mutate.py. The pair protocols' own mutants are
# tinygemm_pair_mutants.py's.
#
# What is not a refusal, and so has no mutant here:
# - A tile sequence of the client's that differs between the CTAs of a pair: not expressible. The tile loops take the
#   pair's schedule, whose first tile and step (`%clusterid.x`, `%nclusterid.x`) are the core's and the same in both
#   CTAs; no operation hands a client the rank (M18) or another value that differs between them; and code that runs
#   in one CTA only, an `onLeader` arm, uses up only leader-only sides and writes no register declared outside it, so
#   it can neither run a role's tile loop itself nor make code both CTAs run take one. `single_cta_schedule` tries the
#   single-CTA loop from `blockIdx.x` in steps of `gridDim.x`, which differ between the CTAs;
#   `producer_extra_on_leader` and `epilogue_on_leader` run a role's loop in the leader's arm; `leader_flag_tile_loop`
#   runs one in both CTAs where a flag the leader set holds.
# - A staging buffer written before the store that last read it has finished reading: not expressible. Every write
#   into a buffer needs a `StageFree`, which only `acquireStage`, the wait, makes, and which is linear.
#   `stage_twice_per_acquire` tries to write a second chunk under one wait.
# - A trip count that differs between roles: a deadlock (M11, M18), not a race.
#
# The `stores_wait_in_…`, `…_captured_by_…` and `…_in_chunk_loop` mutants are M23's: each conditional combinator's
# callback trying to use up an outer linear token.

SOURCE = "encoding/examples/gemm_pair.rac"

# The pair threaded into the producer and the epilogue, for the mutants that give them an `onLeader` arm.
PRODUCER_SIG = '  def producer {l: Lifetime}{L: Lifetime}{r: Lifetime}(g: Gemm(l))', '  def producer {l: Lifetime}{L: Lifetime}{r: Lifetime}(pair: CtaPair(l))(g: Gemm(l))'
PRODUCER_CALL = 'producer(g, sched, ring, steps, p, m, e)', 'producer(pair, g, sched, ring, steps, p, m, e)'
EPILOGUE_SIG = '  def epilogue {l: Lifetime}{q: Lifetime}{s: Lifetime}(g: Gemm(l))', '  def epilogue {l: Lifetime}{q: Lifetime}{s: Lifetime}(pair: CtaPair(l))(g: Gemm(l))'
EPILOGUE_CALL = 'epilogue(g, sched, own, accs, ac, stg, side, m, e)', 'epilogue(pair, g, sched, own, accs, ac, stg, side, m, e)'

# The epilogue's end, which the conditional-combinator mutants wrap: each runs `finishStores` in a callback the
# combinator may not run, or may run more than once.
EPILOGUE_END = """    (finishAccConsumer(finishStores(e, stg, sa), c), Unit.unit)"""


def finish_in(code):
    return [(EPILOGUE_END, code + """
    (finishAccConsumer(e, c), Unit.unit)""")]


# The producer handed to an `onLeader` arm as its sides, under the evidence `evidence`.
def producer_as_sides(evidence):
    return [PRODUCER_SIG, PRODUCER_CALL,
            ("""    elect(e, Unit, fun (j: Lifetime)(w: Elected(j))(e: Ctx(j, One)): Pair(Ctx(j, One), Unit) => {
      let tile :=""", """    (onLeader(e, pair, %s, p, fun (n0: Lifetime)(lead: Leader(n0))(e: Ctx(n0, Load))(p: Producer(r)): Ctx(n0, Load) => {
    let (e, u) := elect(e, Unit, fun (j: Lifetime)(w: Elected(j))(e: Ctx(j, One)): Pair(Ctx(j, One), Unit) => {
      let tile :=""" % evidence),
            ("""      (finishPairProducer(e, ring, p), Unit.unit)
    })

  // The leader's MMA issuer""", """      (finishPairProducer(e, ring, p), Unit.unit)
    })
    e
    }), Unit.unit)

  // The leader's MMA issuer""")]

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
        name="shared_memory_over", expect="EvidenceNotDischarged", mentions="more than sm_100a's 232448",
        why="Deepens the ring to seven stages: 7 × 32 KB of stages and 32 KB of staging buffers exceed what a CTA may "
            "have. The kernel's dynamic shared memory is checked against sm_100a's limit when it is rendered.",
        old="""  def ringCfg : RingCfg := RingCfg.mk(6, boxA, boxB)""",
        new="""  def ringCfg : RingCfg := RingCfg.mk(7, boxA, boxB)""",
    ),
    dict(
        name="leader_flag_tile_loop", expect="EvidenceNotDischarged",
        mentions="set: a register declared outside an `onLeader` arm, written in the leader only",
        why="Sets a register in the leader only, then lets both CTAs' producers read it, vote on it and run their tile "
            "loop a second time where it is set: the leader's producer would fill stages the peer's never fills, and "
            "the pair would deadlock. An `onLeader` arm writes only registers it declared, so no value of the "
            "leader's alone reaches code both CTAs run (M18).",
        edits=[("""  def producer {l: Lifetime}{L: Lifetime}{r: Lifetime}(g: Gemm(l))(sched: PairSched(L, 256))(ring: PairRing(r, ringCfg))
      (steps: Val(l, Grain.uniform, DType.u32))(p: Producer(r))(m: Lifetime)(e: Ctx(m, Load)): Pair(Ctx(m, Load), Unit) :=""",
                """  def producer {l: Lifetime}{L: Lifetime}{r: Lifetime}(flag: Reg(l, DType.u32))(g: Gemm(l))(sched: PairSched(L, 256))(ring: PairRing(r, ringCfg))
      (steps: Val(l, Grain.uniform, DType.u32))(p: Producer(r))(m: Lifetime)(e: Ctx(m, Load)): Pair(Ctx(m, Load), Unit) := {
    let (e, v) := get(e, flag)
    let (e, lead) := voteAny(e, Core.lt(lit(0), v))"""),
               ("""      let (e, p) := forPairTiles(e, sched, fixedProducerAt(r, j), p, tile)
      (finishPairProducer(e, ring, p), Unit.unit)
    })
""", """      let (e, p) := forPairTiles(e, sched, fixedProducerAt(r, j), p, tile)
      let (e, p) := when(e, lead, fixedProducerAt(r, j), p, fun (o: Lifetime)(e: Ctx(o, One))(p: ProducerAt(r, j)): Pair(Ctx(o, One), ProducerAt(r, j)) =>
        forPairTiles(e, sched, fixedProducerAt(r, j), p, tile))
      (finishPairProducer(e, ring, p), Unit.unit)
    })
  }
"""),
               ("""      let steps := ceilDivC(g.k, 64)
""", """      let steps := ceilDivC(g.k, 64)
      let (e, flag) := reg(e, lit(0))
      let e := onLeader(e, pair, leaderOnlyUnit, Unit.unit, fun (n: Lifetime)(lead: Leader(n))(e: Ctx(n, Cta))(u: Unit): Ctx(n, Cta) => set(e, flag, lit(1)))
"""),
               (PRODUCER_CALL[0], """producer(flag, g, sched, ring, steps, p, m, e)""")],
    ),
    dict(
        name="producer_under_consumer_evidence", expect="TypeMismatch", mentions="Core.LeaderOnly(Core.Producer(r))",
        why="Hands the producer to an `onLeader` arm under the pair ring's consumer evidence: the peer would never fill "
            "or drain. The evidence is the consumer's, `LeaderOnly(Consumer(r))`, and a producer is not leader-only.",
        edits=producer_as_sides("leaderOnlyConsumer(ring)"),
    ),
    dict(
        name="producer_forged_evidence", expect="SealedConstructor", mentions="Core.LeaderOnly",
        why="Hands the producer to an `onLeader` arm under evidence of the caller's making. `LeaderOnly` is sealed, and "
            "the core makes it only for leader-only sides.",
        edits=producer_as_sides("LeaderOnly.mk(Producer(r))"),
    ),
    dict(
        name="stores_wait_in_branch", expect="TypeMismatch", mentions="closures differ in kind",
        why="Waits for the stores in one arm of a uniform branch only: where the other arm runs, the CTA closes with "
            "stores in flight. A branch's arms capture no linear value.",
        edits=finish_in("""    let (e, u) := branch(e, Core.lt(lit(0), g.k), fixedUnit, Unit.unit,
      fun (n: Lifetime)(e: Ctx(n, Wg))(u: Unit): Pair(Ctx(n, Wg), Unit) => (finishStores(e, stg, sa), u),
      fun (n: Lifetime)(e: Ctx(n, Wg))(u: Unit): Pair(Ctx(n, Wg), Unit) => (e, u))"""),
    ),
    dict(
        name="stores_wait_in_when", expect="TypeMismatch", mentions="closures differ in kind",
        why="Waits for the stores only where a condition holds. A `when` arm captures no linear value.",
        edits=finish_in("""    let (e, u) := when(e, Core.lt(lit(0), g.k), fixedUnit, Unit.unit,
      fun (n: Lifetime)(e: Ctx(n, Wg))(u: Unit): Pair(Ctx(n, Wg), Unit) => (finishStores(e, stg, sa), u))"""),
    ),
    dict(
        name="stores_wait_in_loop_from", expect="TypeMismatch", mentions="closures differ in kind",
        why="Waits for the stores in a loop's body, which may run no time or many. A loop body captures no linear value.",
        edits=finish_in("""    let (e, u) := loopFrom(e, 1, g.k, fixedUnit, Unit.unit,
      fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, Wg))(u: Unit): Pair(Ctx(n, Wg), Unit) => (finishStores(e, stg, sa), u))"""),
    ),
    dict(
        name="stores_wait_in_peeled_rest", expect="TypeMismatch", mentions="closures differ in kind",
        why="Waits for the stores in a peeled loop's later iterations, which may run no time or many. Both of "
            "`loopPeeled`'s bodies capture no linear value.",
        edits=finish_in("""    let (e, u) := loopPeeled(e, g.k, fixedUnit, Unit.unit,
      fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, Wg))(u: Unit): Pair(Ctx(n, Wg), Unit) => (e, u),
      fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, Wg))(u: Unit): Pair(Ctx(n, Wg), Unit) => (finishStores(e, stg, sa), u))"""),
    ),
    dict(
        name="stores_wait_in_tile_loop", expect="TypeMismatch", mentions="closures differ in kind",
        why="Waits for the stores once per tile of the pair's schedule, so a pair with no tile never waits. A tile "
            "loop's body captures no linear value.",
        edits=finish_in("""    let (e, u) := forPairTiles(e, sched, fixedUnit, Unit.unit,
      fun (n: Lifetime)(t: PairTile(n, 256))(e: Ctx(n, Wg))(u: Unit): Pair(Ctx(n, Wg), Unit) => (finishStores(e, stg, sa), u))"""),
    ),
    dict(
        name="store_side_captured_by_owned_tile_loop", expect="TypeMismatch", mentions="closures differ in kind",
        why="Hands the storing side to the owned tile loop's body by capture, not through its state, and finishes it "
            "per tile: a pair with no tile would never wait for its stores. A tile loop's body captures no linear "
            "value.",
        old="""    let (e, (c, sa)) := forOwnedPairTiles(e, sched, own, fixedPair(fixedAccConsumerAt(q, m, 4), fixedStoreAt(s, m, 4)), (c, sa), tile)
    (finishAccConsumer(finishStores(e, stg, sa), c), Unit.unit)""",
        new="""    let (e, c) := forOwnedPairTiles(e, sched, own, fixedAccConsumerAt(q, m, 4), c,
      fun (n: Lifetime)(t: PairTile(n, 256))(o: HalfOwn(n))(e: Ctx(n, Wg))(c: AccConsumerAt(q, m, 4)): Pair(Ctx(n, Wg), AccConsumerAt(q, m, 4)) => {
        let (e, (c, sa)) := tile(n, t, o, e, (c, sa))
        (finishStores(e, stg, sa), c)
      })
    (finishAccConsumer(e, c), Unit.unit)""",
    ),
    dict(
        name="reader_finished_in_chunk_loop", expect="TypeMismatch", mentions="closures differ in kind",
        why="Ends the accumulator's reading side inside the chunk loop, once per chunk. A chunk loop's body captures no "
            "linear value.",
        old="""      let (e, (full, sa)) := forHalfChunks(e, t, o, fixedPair(fixedAccFull(q, m, 4), fixedStoreAt(s, m, 4)), (full, sa), chunk)""",
        new="""      let (e, (full, sa)) := forHalfChunks(e, t, o, fixedPair(fixedAccFull(q, m, 4), fixedStoreAt(s, m, 4)), (full, sa),
        fun (p: Lifetime)(ch: ChunkAt(p, 256))(co: ChunkOwn(p, 256))(e: Ctx(p, Wg))(st: Pair(AccFull(q, m, 4), StoreAt(s, m, 4)))
            : Pair(Ctx(p, Wg), Pair(AccFull(q, m, 4), StoreAt(s, m, 4))) => chunk(p, ch, co, finishAccConsumer(e, c), st))""",
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
    dict(
        name="band_of_no_rows", expect="EvidenceNotDischarged", mentions="a band must have at least one tile row",
        why="Orders the tiles in bands of zero tile rows: tile index t would lie in band t / 0, so the order would be no "
            "bijection onto the tiles. `schedule` makes a zero band a generation error.",
        old="""  def band : Nat := 8""",
        new="""  def band : Nat := 0""",
    ),
]
