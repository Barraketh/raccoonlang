# Paged attention (PAGED.md §5) with one mistake each: the core refuses a loader that chooses its own page row and any
# write into the cache or the table. The protocol mutants of A1 (ATTENTION.md §5) are not repeated: the paged example
# shares every role but the loader with A1's. Run by check.sh through gpu/mutate.py.

SOURCE = "encoding/examples/paged_attention.rac"

MUTANTS = [
    dict(
        name="page_row_from_caller", expect="ArityMismatch",
        why="Passes `fillPage` a column and a row of the cache's own choosing, as `fillHead` takes them. `fillPage` "
            "takes only the block index; the sequence, the head, the page and its row are the core's.",
        old="""        let (e, pk) := Core.fillPage(e, kr, s, g.table, g.k, i)""",
        new="""        let (e, pk) := Core.fillPage(e, kr, s, g.table, g.k, Core.lit(0), Core.mulC(i, 128))""",
    ),
    dict(
        name="head_fill_on_cache", expect="ImplicitReconstructionFailed", mentions="PageMap",
        why="Loads K through the cache's map with A1's `fillHead`, at rows `blockIdx.y·seq + 128i` that ignore the "
            "table. Only `fillPage` takes a `PageMap`.",
        old="""        let (e, pk) := Core.fillPage(e, kr, s, g.table, g.k, i)""",
        new="""        let (e, pk) := Core.fillHead(e, kr, s, g.k, Core.lit(0), Core.mulC(i, 128), g.k, Core.lit(64), Core.mulC(i, 128))""",
    ),
    dict(
        name="forged_page_map", expect="SealedConstructor", mentions="PageMap",
        why="Builds a map of the cache with a head count of its own (1, not the kernel's 8), so that `fillPage` "
            "would compute rows of another layout. Only the kernel builder makes a `PageMap`.",
        old="""        let (e, pk) := Core.fillPage(e, kr, s, g.table, g.k, i)""",
        new="""        let (e, pk) := Core.fillPage(e, kr, s, g.table, PageMap.mk(l, Paged.box, "K_map", 1), i)""",
    ),
    dict(
        name="store_into_cache", expect="ImplicitReconstructionFailed", mentions="PageMap",
        why="Stores the output rows through the K cache's map. No operation writes through a `PageMap`.",
        old="""ln2), g.out, own)""",
        new="""ln2), g.k, own)""",
    ),
    dict(
        name="store_into_table", expect="ImplicitReconstructionFailed", mentions="PageTable",
        why="Stores the output rows into the block table. No operation writes a `PageTable`.",
        old="""ln2), g.out, own)""",
        new="""ln2), g.table, own)""",
    ),
    dict(
        name="half_page_box", expect="EvidenceNotDischarged", mentions="fillPage",
        why="Gives the K ring a second box of 64 rows. `fillPage` loads both boxes through the one cache map, whose "
            "box is the first's (a map of the wrong box is a type error), so the stage would expect bytes that do not "
            "match what lands. `fillPage` requires stages of two 64 × 128 boxes, one page of one head, at generation.",
        old="""  def kRing : RingCfg := RingCfg.mk(2, Paged.box, Paged.box)""",
        new="""  def kRing : RingCfg := RingCfg.mk(2, Paged.box, TmaSpec.mk(64, 64))""",
    ),
]
