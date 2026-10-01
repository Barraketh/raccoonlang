# The encoding core's TinyGEMM with one side left unfinished: with no `…Done` token to hand back, a protocol's side is
# linear and belongs to its opener's scope, so a role that ends without its finisher is refused as leaving it unused;
# and one finished inside the chunk loop, whose body captures no linear value (M23).
# (gpu/rejected/tinygemm_mutants.py holds the GEMM library's mutants, against gpu/Gpu.rac.) Run by check.sh through
# gpu/mutate.py.

SOURCE = "encoding/examples/tinygemm.rac"

MUTANTS = [
    dict(
        name="ring_closed_while_filling", expect="LinearUnused", mentions="p has a linear type",
        why="Ends the producer without its tail: its last copies could still be landing when the ring's storage goes "
            "away. The producer is linear and belongs to the ring's scope, and only `finishProducer`'s drain uses it "
            "up.",
        old="""      (finishProducer(e, ring, p), Unit.unit)""",
        new="""      (e, Unit.unit)""",
    ),
    dict(
        name="stores_in_flight_at_close", expect="LinearUnused", mentions="sa has a linear type",
        why="Ends the epilogue without waiting for its TMA stores: the staging buffers' shared memory would be released "
            "while a store still reads it. The storing side is linear and belongs to the staging scope, and only "
            "`finishStores`' wait uses it up.",
        old="""    (finishStores(e, stg, sa), acc)""",
        new="""    (e, acc)""",
    ),
    dict(
        name="store_side_captured_by_chunk_loop", expect="TypeMismatch", mentions="closures differ in kind",
        why="Hands the storing side to the chunk loop's body by capture, not through its state, and finishes it per "
            "chunk. A loop's body runs any number of times, so it captures no linear value.",
        old="""    let (e, (acc, sa)) := forChunks(e, k.tile, own, fixedPair(fixedAcc(a, AccState.ready), fixedStoreAt(s, m, groupWarp)), (acc, sa), chunk)
    (finishStores(e, stg, sa), acc)""",
        new="""    let (e, acc) := forChunks(e, k.tile, own, fixedAcc(a, AccState.ready), acc,
      fun (p: Lifetime)(ch: ChunkAt(p, 128))(co: ChunkOwn(p, 128))(e: Ctx(p, Wg))(acc: Acc(a, AccState.ready)): Pair(Ctx(p, Wg), Acc(a, AccState.ready)) => {
        let (e, (acc, sa)) := chunk(p, ch, co, e, (acc, sa))
        (finishStores(e, stg, sa), acc)
      })
    (e, acc)""",
    ),
]
