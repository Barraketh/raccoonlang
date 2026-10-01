# A3a's kernel (encoding/examples/attention_pingpong.rac, gpu/encoding/A3.md) with one mistake each in its use of the
# score buffer (A3.md §3, §5): every mutant breaks a rule of the overlaid buffer and is refused for that rule. Run by
# check.sh through gpu/mutate.py.
#
# What is not a refusal, and so has no mutant here:
# - Reading S again after P is written over it: not expressible. `loadRow` consumes `Scored`, and nothing else reads
#   S, so a block's row is loaded once, and every load completes (`wait::ld`) inside it.
# - Writing a chunk of P twice or not at all: not expressible. `writeProbs` writes one chunk per chunk of the row, and
#   a `Row` comes only from `loadRow` or `mapRow`, so it has 16.
# - Swapping both tiles' buffers between the warpgroups: allowed, and a wrong result, not a race. Each warpgroup then
#   computes the other tile's scores and stores them as its own rows (`rowInPair`), each row once.
# - Committing a buffer with no new scores in it (`commitBuffer` straight after `issuePV` inside the loop): a wrong
#   result, not a race. The commit still follows the product, so Ô is quiescent and S's stale columns are only read.
# - Trip counts that differ between the issuer and a warpgroup: a deadlock (M11), not a race.

SOURCE = "encoding/examples/attention_pingpong.rac"

MUTANTS = [
    dict(
        name="probs_before_load_completes", expect="ImplicitReconstructionFailed",
        mentions="Core.writeProbs: expected an application of Core.Read",
        why="Writes P over S's upper half from the buffer as `awaitScores` gave it, before the row's loads complete: a "
            "store to P could overtake a load of the S columns under it. `writeProbs` writes through the `Read` that "
            "only `loadRow`'s `wait::ld` makes.",
        old="""      let (e, p) := writeProbs(e, buf, read, t, fun""",
        new="""      let (e, p) := writeProbs(e, buf, scored, t, fun""",
    ),
    dict(
        name="rescale_before_scored", expect="ImplicitReconstructionFailed",
        mentions="Core.rescaleRow: expected an application of Core.Probs",
        why="Rescales Ô before waiting for the MMA thread's commit, while the product of the previous block may still "
            "accumulate into it: a read-modify-write racing the tensor cores. `rescaleRow` needs `Probs`, which comes "
            "only after `awaitScores`' wait.",
        old="""      let (e, scored) := awaitScores(e, buf, st)""",
        new="""      let (e, st) := rescaleRow(e, buf, st, lowest)
      let (e, scored) := awaitScores(e, buf, st)""",
    ),
    dict(
        name="scores_before_product", expect="TypeMismatch", mentions="Core.Issued",
        why="Issues tile 0's next scores before its product: S_{i+1} would overwrite P_i while PV_i has not yet read it. "
            "After `awaitProbs` the buffer is `Published`, which only `issuePV` takes; `issueScores` needs the `Issued` "
            "that the product gives back.",
        old="""        let (e, (s0, v)) := product(e, b0, s0, v)
        let (e, k) := hold(e, kr, ck)
        let (e, (s0, (q0, k))) := scores(e, b0, s0, q0r, q0, k)""",
        new="""        let (e, published) := awaitProbs(e, b0, s0)
        let (e, k) := hold(e, kr, ck)
        let (e, (s0, (q0, k))) := issueScores(e, w, b0, published, q0r, q0, kr, k)
        let (e, (s0, v)) := issuePV(e, w, b0, s0, vr, v)
        let (e, s0) := commitBuffer(e, w, b0, s0)""",
    ),
    dict(
        name="store_before_final", expect="ImplicitReconstructionFailed",
        mentions="Core.storeFinal: expected an application of Core.Final",
        why="Stores the tile's rows of O without waiting for the last commit: Ô may still be accumulating the last "
            "product. `storeFinal` reads Ô through the `Final` that only `awaitFinal`'s wait makes.",
        old="""    let (e, final) := awaitFinal(e, buf, st)""",
        new="""    let (e, final) := (e, st)""",
    ),
    dict(
        name="other_tiles_region", expect="TypeMismatch", mentions="RowSide",
        why="Hands warpgroup 0 tile 1's buffer with tile 0's side: it would read and write tile 1's region, which "
            "warpgroup 1 holds, under tile 0's barriers. A buffer's operations take its handle and its side's tokens in "
            "one scope `x`.",
        old="""                  softmax(g.blocks, g.mask, g.scale, g.out, own0, b0, r0, m, e),""",
        new="""                  softmax(g.blocks, g.mask, g.scale, g.out, own0, b1, r0, m, e),""",
    ),
    dict(
        name="publish_before_o_defined", expect="TypeMismatch", mentions="Core.OState.held",
        why="Publishes P without the rescale, so in the first block Ô is still undefined when the product, which always "
            "accumulates, adds into it. `publishProbs` needs `Probs(…, held)`, which in the first block only "
            "`rescaleRow`'s zeroing makes.",
        old="""      let (e, p) := rescaleRow(e, buf, p, alpha)""",
        new="""""",
    ),
    dict(
        name="close_with_product_in_flight", expect="LinearUnused", mentions="st has a linear type",
        why="Ends the softmax role without waiting for the last commit: the buffer would close, and its tensor memory "
            "be freed, with the last product still writing Ô. The warpgroup's side is linear and belongs to the "
            "buffer's scope, and only `awaitFinal` (then `closeRows`) uses it up.",
        old="""    let (e, final) := awaitFinal(e, buf, st)
    let (e, lSum) := get(e, lReg)
    let (e, mMax) := get(e, mReg)
    let (e, inv) := rcp(e, lSum)
    let (e, logSum) := lg2(e, lSum)
    let (e, ln2) := fconst(e, ln2)
    let (e, final) := storeFinal(e, buf, final, inv, fmul(fadd(mMax, logSum), ln2), out, own)
    (closeRows(e, final), Unit.unit)""",
        new="""    (e, Unit.unit)""",
    ),
]
