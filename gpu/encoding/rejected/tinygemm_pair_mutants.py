# The pair TinyGEMM (encoding/examples/tinygemm_pair.rac, gpu/encoding/TWO_CTA.md) with one mistake each in its use of
# the pair: every mutant breaks a rule of the pair's protocols and is refused, by the types or at generation. Run by
# check.sh through gpu/mutate.py.
#
# What is not a refusal, and so has no mutant here:
# - A producer or consumer whose trip count differs from the others': a deadlock (M11, M18), not a race. The extra
#   fills wait in their producer's tail for releases that never come, and that CTA never reaches the close's cluster
#   barrier.
# - Swapping A's and B's maps in a fill: both have the ring's boxes, so a wrong result, as in the single-CTA ring.
# - A pair opener under a branch, a loop or a role: not expressible. Its context must be the kernel's own, `Ctx(l, …)`
#   with the kernel's `CtaPair(l)`, and every such scope has a lifetime of its own (`opener_under_leader` tries it in
#   the leader's arm).

SOURCE = "encoding/examples/tinygemm_pair.rac"

MUTANTS = [
    dict(
        name="consumer_outside_leader", expect="SealedConstructor", mentions="Core.Leader",
        why="Runs the issuer in both CTAs: the peer would take the ring's consumer too and issue the pair's MMAs and "
            "commits a second time. Taking the consumer needs a `Leader`, which only `onLeader`'s arm holds; outside it "
            "the only one would be forged, and `Leader` is sealed.",
        old="""    (onLeader(e, pair, leaderOnlyPair(leaderOnlyConsumer(r), leaderOnlyAccProducer(q)), (c, p),
      fun (n: Lifetime)(lead: Leader(n))(e: Ctx(n, Issue))(sides: Pair(Consumer(r), AccProducer(q))): Ctx(n, Issue) =>
        issue(lead, ring, accs, steps, sides, e)), Unit.unit)""",
        new="""    (issue(Leader.mk(m), ring, accs, steps, (c, p), e), Unit.unit)""",
    ),
    dict(
        name="leader_escapes", expect="TypeMismatch", mentions="Core.Leader",
        why="Hands the arm's `Leader` back out of `onLeader`, so that code both CTAs run could take a consumer with it. "
            "The arm hands back only its context, and the `Leader` belongs to the arm's scope.",
        old="""    (onLeader(e, pair, leaderOnlyPair(leaderOnlyConsumer(r), leaderOnlyAccProducer(q)), (c, p),
      fun (n: Lifetime)(lead: Leader(n))(e: Ctx(n, Issue))(sides: Pair(Consumer(r), AccProducer(q))): Ctx(n, Issue) =>
        issue(lead, ring, accs, steps, sides, e)), Unit.unit)""",
        new="""    (onLeader(e, pair, leaderOnlyPair(leaderOnlyConsumer(r), leaderOnlyAccProducer(q)), (c, p),
      fun (n: Lifetime)(lead: Leader(n))(e: Ctx(n, Issue))(sides: Pair(Consumer(r), AccProducer(q))): Pair(Ctx(n, Issue), Leader(n)) =>
        (issue(lead, ring, accs, steps, sides, e), lead)), Unit.unit)""",
    ),
    dict(
        name="single_cta_tmem", expect="EvidenceNotDischarged", mentions="tensor memory: a single-CTA protocol in a pair kernel",
        why="Allocates the accumulator with the single-CTA `withTmem`: a `cta_group::1` allocation in a kernel whose "
            "MMAs are `cta_group::2` (A29), and the peer's tensor memory never allocated. The single-CTA openers read "
            "the kernel's CTA group and refuse at generation.",
        old="""      let (e, u) := withPairTmem(e, pair, permit, AccState.empty, Unit, body)""",
        new="""      let (e, u) := withTmem(e, permit, 512, AccState.empty, Unit, body)""",
    ),
    dict(
        name="fill_own_barrier", expect="ImplicitReconstructionFailed", mentions="Core.Ring",
        why="Fills the stage with the single-CTA `fill`: coordinates of the caller's choosing (here the leader's rows "
            "in both CTAs), a `cta_group::1` copy completing on the CTA's own `full[s]`, which the leader's consumer "
            "never waits on, and the leader arming only its own bytes. `fill` takes a `Ring`, and a pair ring is a "
            "`PairRing`.",
        old="""        fillPair(e, ring, s, k.tile, k.a, k.b, mulC(i, 64))""",
        new="""        fill(e, ring, s, k.a, mulC(i, 64), lit(0), k.b, mulC(i, 64), lit(0))""",
    ),
    dict(
        name="fill_wrong_half", expect="SealedConstructor", mentions="Core.PairTile",
        why="Fills with a tile of the caller's making, whose rows are the leader's in both CTAs: the peer would load "
            "the leader's half. A CTA's half comes only from the builder's `PairTile`, computed from the rank, and "
            "`PairTile` is sealed.",
        old="""        fillPair(e, ring, s, k.tile, k.a, k.b, mulC(i, 64))""",
        new="""        fillPair(e, ring, s, PairTile.mk(lit(1).expr, lit(0).expr, lit(0).expr, lit(0).expr), k.a, k.b, mulC(i, 64))""",
    ),
    dict(
        name="store_other_rows", expect="SealedConstructor", mentions="Core.PairTile",
        why="Stores the buffer through a tile of the caller's making, at the other CTA's rows: two CTAs would write "
            "one row of C. `storeHalf` computes a thread's row from the builder's `PairTile`, so a CTA's rows are its "
            "own, and `PairTile` is sealed.",
        old="""    let (e, full) := storeHalf(e, accs, full, k.tile, k.c, own)""",
        new="""    let (e, full) := storeHalf(e, accs, full, PairTile.mk(lit(1).expr, lit(128).expr, lit(0).expr, lit(0).expr), k.c, own)""",
    ),
    dict(
        name="store_past_the_tile", expect="TypeMismatch", mentions="Core.PairTile(l, 128)",
        why="Halves B's box, so the pair's tile is 128 columns wide while its accumulator buffers stay 256: each CTA "
            "would store 256 columns, the next pair's half of them included. `storeHalf` takes a `PairTile` of the "
            "buffer's width, and the tile's width is in its type (the pair's MMA refuses the shape too).",
        old="""  def boxB : TmaSpec := TmaSpec.mk(64, 128)""",
        new="""  def boxB : TmaSpec := TmaSpec.mk(64, 64)""",
    ),
    dict(
        name="close_with_producer_unfinished", expect="LinearUnused", mentions="p has a linear type",
        why="Ends a CTA's producer without its tail: its last copies could still be landing, and their bytes "
            "completing on the leader's barriers, when the ring closes. The producer is linear and belongs to the "
            "ring's scope, and only `finishPairProducer`'s drain uses it up.",
        old="""      (finishPairProducer(e, ring, p), Unit.unit)""",
        new="""      (e, Unit.unit)""",
    ),
    dict(
        name="close_with_issuer_unfinished", expect="LinearUnused", mentions="p has a linear type",
        why="Ends the leader's issuing side without its tail: the leader could close the accumulator ring, and the "
            "pair its tensor memory, while the warpgroups still read the buffer and arrive on the leader's barriers. "
            "The issuing side is linear, and only `finishPairAccProducer`'s drain uses it up.",
        old="""      (finishConsumer(finishPairAccProducer(e, accs, p), c), Unit.unit)""",
        new="""      (finishConsumer(e, c), Unit.unit)""",
    ),
    dict(
        name="close_with_reader_unfinished", expect="LinearUnused", mentions="full has a linear type",
        why="Ends an epilogue holding its buffer, unreleased: the leader's tail would wait for this CTA's arrivals "
            "forever, and a reader that did not wait for its loads could release the buffer early. The buffer's "
            "`AccFull` is linear, and only `releasePairAcc`, after the loads, hands the reading side back.",
        old="""    let (e, c) := releasePairAcc(e, accs, full)
    (finishAccConsumer(e, c), Unit.unit)""",
        new="""    (e, Unit.unit)""",
    ),
    dict(
        name="opener_under_leader", expect="ImplicitReconstructionFailed", mentions="Core.withPairRing",
        why="Opens a pair ring in the leader only, inside the issuer's arm: the peer would neither lay out nor "
            "initialize its half, and the two CTAs' layouts and cluster barriers would no longer match. A pair opener "
            "takes the kernel's own context: a CTA-wide group, refused here, and the kernel's lifetime, which no branch "
            "arm has. An arm at the kernel's level could not hand the opener the tensor-memory permit either: an arm "
            "captures no linear value.",
        old="""        issue(lead, ring, accs, steps, sides, e)), Unit.unit)""",
        new="""{
        let (e, u) := withPairRing(e, pair, ringCfg, Unit, fun (r2: Lifetime)(ring2: PairRing(r2, ringCfg))(p2: Producer(r2))(c2: Consumer(r2))
            (e: Ctx(n, Issue)): Pair(Ctx(n, Issue), Unit) => (e, Unit.unit))
        issue(lead, ring, accs, steps, sides, e)
      }), Unit.unit)""",
    ),
]
