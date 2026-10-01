# The append of paged decode (P2.md §5) with one mistake each: the core refuses a cache write without a claim, a claim
# that leaves its arm, a row of the caller's choosing, a second claim, and owners of the caller's making. Run by
# check.sh through gpu/mutate.py.

SOURCE = "encoding/examples/paged_append.rac"

MUTANTS = [
    dict(
        name="write_without_claim", expect="SealedConstructor", mentions="Claimed",
        why="Writes the new row before claiming, with a claim of its own making. A race: two sequences whose tables "
            "name one last page would both write its rows. Only `withClaim` makes a `Claimed`, in the arm that runs "
            "where the claim holds.",
        old="""      withClaim(e, g.lens, g.table, g.claims, own, fun""",
        new="""      withClaim(appendRow(e, Claimed.mk(l, Expr.lit(0)), g.cache, g.knew), g.lens, g.table, g.claims, own, fun""",
    ),
    dict(
        name="claim_leaves_arm", expect="TypeMismatch",
        why="Hands the claim back out of the arm, to write with it where the claim may not hold. The arm returns its "
            "emitter only, and the claim belongs to the arm's scope.",
        old="""        appendRow(e, c, g.cache, g.knew)))""",
        new="""        (appendRow(e, c, g.cache, g.knew), c)))""",
    ),
    dict(
        name="row_from_caller", expect="ArityMismatch",
        why="Passes `appendRow` a cache row of its own choosing, which the claim does not hold. `appendRow` takes the "
            "row from the claim; the caller gives only the claim and the arrays.",
        old="""        appendRow(e, c, g.cache, g.knew)))""",
        new="""        appendRow(e, c, g.cache, g.knew, lit(0))))""",
    ),
    dict(
        name="claim_twice", expect="LinearReused", mentions="own",
        why="Claims twice, so that lane 0 reports twice into one element of `appended`, and the second claim's arm "
            "writes again. The authority to claim and report is linear.",
        old="""      withClaim(e, g.lens, g.table, g.claims, own, fun""",
        new="""      withClaim(withClaim(e, g.lens, g.table, g.claims, own, fun (m: Lifetime)(e: Ctx(m, warpCta))(c: Claimed(m)): Ctx(m, warpCta) =>
        appendRow(e, c, g.cache, g.knew)), g.lens, g.table, g.claims, own, fun""",
    ),
    dict(
        name="forged_owners", expect="SealedConstructor", mentions="Claims",
        why="Claims against owners of its own making, with epoch 0, which the zeroed owners would read as claims of "
            "sequence 0 in this launch, or with another array. Only the kernel builder makes `Claims`.",
        old="""      withClaim(e, g.lens, g.table, g.claims, own, fun""",
        new="""      withClaim(e, g.lens, g.table, Claims.mk(l, "owners", Expr.lit(0), "appended", Expr.param("pages"), 8), own, fun""",
    ),
]
