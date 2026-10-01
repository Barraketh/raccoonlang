# The split attention of paged decode (P2.md §5) with one mistake each: the core refuses a partial output of the
# caller's making (which could write another CTA's rows), a mask of the caller's making, a query row of the caller's
# choosing, and a write into the cache. The protocol mutants of the roles are in attention_mutants.py; the decode
# example runs the same roles (encoding/Attention.rac) with its own loader. Run by check.sh through gpu/mutate.py.
#
# Not here: a role that runs another trip count than the prologue's. The roles take their count as a `Val`, as A2's
# do, so a loader that loops another number of times type-checks; the roles then disagree and deadlock, which no
# role can turn into a race (OBLIGATIONS.md M11, P2.md §5).

SOURCE = "encoding/examples/paged_decode.rac"

MUTANTS = [
    dict(
        name="partials_of_another_cta", expect="SealedConstructor", mentions="AttnOut",
        why="Hands the roles a partial output whose rows start at `blockIdx.y`, not `blockIdx.x·B·8·G + blockIdx.y·G`, "
            "so that CTA (s, y) would store its G rows over those of every other split, and of the next heads. `storeO` "
            "computes a decode CTA's rows from the `AttnOut` that only the kernel builder makes.",
        old="""g.scale, g.out, own""",
        new="""g.scale, AttnOut.mk(l, DType.f32, "Opart", "LSEpart", Expr.lit(8), rowInTile, Expr.special(Builtin.blockY), Option.none(Expr)), own""",
    ),
    dict(
        name="forged_decode_mask", expect="SealedConstructor", mentions="Mask",
        why="Masks the scores against a mask of its own, keeping every key of every block, whatever the sequence's "
            "length. Only the kernel builders make a `Mask`.",
        old="""cta(e, permit, g.blocks, g.mask,""",
        new="""cta(e, permit, g.blocks, Mask.mk(l, Expr.lit(4294967295), Bool.false, Expr.lit(0), rowInTile),""",
    ),
    dict(
        name="query_row_from_caller", expect="ArityMismatch",
        why="Passes `fillGroup` a row of Q of its own choosing. The row is the core's, from the CTA's head and the "
            "map's group.",
        old="""      let (e, pq) := fillGroup(e, qr, s, g.q)""",
        new="""      let (e, pq) := fillGroup(e, qr, s, g.q, lit(0))""",
    ),
    dict(
        name="store_into_cache", expect="ImplicitReconstructionFailed", mentions="PageMap",
        why="Hands the roles the K cache's map as the output, for `storeO` to write through. No operation writes "
            "through a `PageMap`; only the append writes the cache, under a claim.",
        old="""g.scale, g.out, own""",
        new="""g.scale, g.k, own""",
    ),
]
