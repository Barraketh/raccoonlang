# The combine of paged decode (P2.md §4) with one mistake each: the core refuses a row stored twice and an output of
# the caller's making. Run by check.sh through gpu/mutate.py.

SOURCE = "encoding/examples/paged_combine.rac"

MUTANTS = [
    dict(
        name="store_twice", expect="LinearReused", mentions="own",
        why="Stores the row twice, so that one element of O is written twice. The authority to store the warp's row "
            "is linear.",
        old="""    storeCombined(e, g.out, own, F32x4.map(""",
        new="""    storeCombined(storeCombined(e, g.out, own, a, mMax), g.out, own, F32x4.map(""",
    ),
    dict(
        name="forged_output", expect="SealedConstructor", mentions="Combined",
        why="Stores the row into an output of its own making, the partials' array, which other warps read. Only the "
            "kernel builder makes `Combined`.",
        old="""    storeCombined(e, g.out, own, F32x4.map(""",
        new="""    storeCombined(e, Combined.mk(l, "Opart", "LSEpart"), own, F32x4.map(""",
    ),
]
