# The encoding core's TinyGEMM with one side left unfinished: with no `…Done` token to hand back, a protocol's side is
# linear and belongs to its opener's scope, so a role that ends without its finisher is refused as leaving it unused.
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
]
