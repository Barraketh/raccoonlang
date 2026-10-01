# The append of paged decode (P2.md §5) with one mistake each: the core refuses a cache write without a claim, a claim
# that leaves its arm, a row of the caller's choosing, a second claim, owners of the caller's making, a claimed row
# written twice, in a loop, or not at all, and a claim inside the claim's arm. Run by check.sh through gpu/mutate.py.

SOURCE = "encoding/examples/paged_append.rac"

ARM = """        appendRow(e, c, once, g.cache, g.knew)))"""

MUTANTS = [
    dict(
        name="write_without_claim", expect="SealedConstructor", mentions="Claimed",
        why="Writes the new row before claiming, with a claim of its own making. A race: two sequences whose tables "
            "name one last page would both write its rows. Only `withClaim` makes a `Claimed`, in the arm that runs "
            "where the claim holds.",
        old="""      withClaim(e, g.lens, g.table, g.claims, own, fun""",
        new="""      withClaim(appendRow(e, Claimed.mk(l, Expr.lit(0)), AppendOwn.mk(l), g.cache, g.knew), g.lens, g.table, g.claims, own, fun""",
    ),
    dict(
        name="claim_leaves_arm", expect="TypeMismatch",
        why="Hands the claim back out of the arm, to write with it where the claim may not hold. The arm's type "
            "returns the emitter only, so nothing leaves it; the claim also belongs to the arm's scope.",
        old=ARM,
        new="""        (appendRow(e, c, once, g.cache, g.knew), c)))""",
    ),
    dict(
        name="row_from_caller", expect="ArityMismatch",
        why="Passes `appendRow` a cache row of its own choosing, which the claim does not hold. `appendRow` takes the "
            "row from the claim; the caller gives only the claim, its authority and the arrays.",
        old=ARM,
        new="""        appendRow(e, c, once, g.cache, g.knew, lit(0))))""",
    ),
    dict(
        name="claim_twice", expect="LinearReused", mentions="own",
        why="Claims twice, so that lane 0 reports twice into one element of `appended`, and the second claim's arm "
            "writes again. The authority to claim and report is linear.",
        old="""      withClaim(e, g.lens, g.table, g.claims, own, fun""",
        new="""      withClaim(withClaim(e, g.lens, g.table, g.claims, own, fun (m: Lifetime)(e: Ctx(m, warpCta))(c: Claimed(m))
          (once: AppendOwn(m)): Ctx(m, warpCta) => appendRow(e, c, once, g.cache, g.knew)), g.lens, g.table, g.claims, own, fun""",
    ),
    dict(
        name="forged_owners", expect="SealedConstructor", mentions="Claims",
        why="Claims against owners of its own making, with another epoch or another array. Only the kernel builder "
            "makes `Claims`.",
        old="""      withClaim(e, g.lens, g.table, g.claims, own, fun""",
        new="""      withClaim(e, g.lens, g.table, Claims.mk(l, "owners", Expr.lit(0), "appended", Expr.param("pages"), 8), own, fun""",
    ),
    dict(
        name="append_twice", expect="LinearReused", mentions="once",
        why="Writes the claimed row twice, so that its elements are written twice in one launch (S5). The authority to "
            "write the row is linear, and `appendRow` uses it up.",
        old=ARM,
        new="""        appendRow(appendRow(e, c, once, g.cache, g.knew), c, once, g.cache, g.knew)))""",
    ),
    dict(
        name="append_in_loop", expect="TypeMismatch", mentions="closures differ in kind",
        why="Writes the claimed row in every iteration of a loop. A loop body is generated once and runs any number "
            "of times, so it captures no linear value, and the authority to write the row is linear.",
        old=ARM,
        new="""        { let (e, u) := loop(e, lit(1000), fixedUnit, Unit.unit, fun (n: Lifetime)(i: Val(n, Grain.uniform, DType.u32))(e: Ctx(n, warpCta))(u: Unit)
            : Pair(Ctx(n, warpCta), Unit) => (appendRow(e, c, once, g.cache, g.knew), u))
          e }))""",
    ),
    dict(
        name="claim_inside_arm", expect="TypeMismatch", mentions="closures differ in kind",
        why="Claims again inside the claim's arm, with the launch's one authority to claim: the inner claim would run "
            "only where the outer one held. The arm runs under a run-time condition, so it captures no linear value.",
        old=ARM,
        new="""        withClaim(appendRow(e, c, once, g.cache, g.knew), g.lens, g.table, g.claims, own,
          fun (n: Lifetime)(e: Ctx(n, warpCta))(c2: Claimed(n))(once2: AppendOwn(n)): Ctx(n, warpCta) => appendRow(e, c2, once2, g.cache, g.knew))))""",
    ),
    dict(
        name="arm_without_append", expect="LinearUnused", mentions="once",
        why="Claims and writes nothing, so that `appended` reports a new token the cache does not hold. The arm must "
            "use its linear authority to write the row.",
        old=ARM,
        new="""        e))""",
    ),
]
