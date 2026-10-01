# Paged attention (PAGED.md §5) with one mistake each: the core refuses a loader that chooses its own page row, any
# write into the cache or the table, and a ring closed with its loads in flight. The protocol mutants of A1
# (ATTENTION.md §5) are in attention_mutants.py: the paged example runs the same roles (encoding/Attention.rac) with its
# own loader. Run by check.sh through gpu/mutate.py.
#
# `half_page_box`, a K ring whose second box is 64 rows, moved to page_box_mutants.py: the rings' configurations are
# now the shared roles', which the paged example does not choose.

SOURCE = "encoding/examples/paged_attention.rac"

MUTANTS = [
    dict(
        name="page_row_from_caller", expect="ArityMismatch",
        why="Passes `fillPage` a column and a row of the cache's own choosing, as `fill` takes them. `fillPage` takes "
            "only the block index; the sequence, the head, the page and its row are the core's.",
        old="""        let (e, pk) := fillPage(e, kr, s, g.table, g.k, i)""",
        new="""        let (e, pk) := fillPage(e, kr, s, g.table, g.k, lit(0), mulC(i, 128))""",
    ),
    dict(
        name="head_fill_on_cache", expect="ImplicitReconstructionFailed", mentions="PageMap",
        why="Loads K through the cache's map with A1's `fillBlock`, at rows `blockIdx.y·seq + 128i` that ignore the "
            "table. Only `fillPage` takes a `PageMap`.",
        old="""        let (e, pk) := fillPage(e, kr, s, g.table, g.k, i)""",
        new="""        let (e, pk) := fillBlock(e, kr, s, g.k, mulC(i, 128))""",
    ),
    dict(
        name="forged_page_map", expect="SealedConstructor", mentions="PageMap",
        why="Builds a map of the cache with a head count of its own (1, not the kernel's 8), so that `fillPage` "
            "would compute rows of another layout. Only the kernel builder makes a `PageMap`.",
        old="""        let (e, pk) := fillPage(e, kr, s, g.table, g.k, i)""",
        new="""        let (e, pk) := fillPage(e, kr, s, g.table, PageMap.mk(l, box, "K_map", 1), i)""",
    ),
    dict(
        name="store_into_cache", expect="ImplicitReconstructionFailed", mentions="PageMap",
        why="Hands the roles the K cache's map as the output, for `storeO` to write through. No operation writes "
            "through a `PageMap`.",
        old="""g.scale, g.out, own""",
        new="""g.scale, g.k, own""",
    ),
    dict(
        name="store_into_table", expect="ImplicitReconstructionFailed", mentions="PageTable",
        why="Hands the roles the block table as the output. No operation writes a `PageTable`.",
        old="""g.scale, g.out, own""",
        new="""g.scale, g.table, own""",
    ),
    dict(
        name="close_ring_undrained", expect="LinearUnused", mentions="pk",
        why="Ends the loader without waiting until every K stage was released: the K ring would close, and its shared "
            "memory be reused, with a copy still landing or an MMA still reading it. The producer is linear and "
            "belongs to the ring's scope, and only `finishProducer`'s drain uses it up.",
        old="""      let e := finishProducer(e, kr, pk)""",
        new="""""",
    ),
]
