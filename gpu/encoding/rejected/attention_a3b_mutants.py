# A3b's kernel (encoding/examples/attention_a3b.rac, gpu/encoding/A3B.md) with one mistake each in its use of the
# correction warpgroup, the α ring, `warpwise` and the register split (A3B.md §5): every mutant breaks a rule and is
# refused for that rule. Run by check.sh through gpu/mutate.py.
#
# What is not a refusal, and so has no mutant here:
# - A softmax writing the α slot before its empty wait: not expressible. `publishAlpha` waits for the slot, writes it
#   and arrives on its full barrier in one operation, and it is the only writer of the ring.
# - Reading α from the slot before its full wait: not expressible. `awaitAlpha` waits, fences, reads and frees the slot
#   in one operation.
# - Setting a warpgroup's register count twice: not expressible. Only `splitWarpgroups` emits `setmaxnreg`, once per
#   warpgroup, and it uses up the kernel's one `RegPermit`, which is linear.
# - Rescaling every warp's quadrant, skipping none (`rescaleQuadrant` straight on the warpgroup, no vote): allowed, and
#   correct. `rescaleQuadrant` takes the warpgroup or warps of it under a warp vote, and a row whose α is 1 is
#   multiplied by 1.
# - Swapping the two tiles' buffers between the correction's two calls is refused, not a mutant of a rule of A3b's: a
#   side is indexed by its buffer's scope, so tile 1's buffer does not take tile 0's `CorrectAt`.
# - Trip counts that differ between the correction warpgroup and the other roles: a deadlock (M11), not a race.

SOURCE = "encoding/examples/attention_a3b.rac"

MUTANTS = [
    dict(
        name="rescale_before_alpha", expect="TypeMismatch", mentions="Core.Rescaling",
        why="Rescales Ô without waiting for the block's α: the product of the block before may still be accumulating "
            "into Ô, a read-modify-write racing the tensor cores. The branch's state must be the `Rescaling` that only "
            "`awaitAlpha` (after the α ring's full wait and its fence) or block 0's `zeroQuadrants` gives, and it is "
            "refused at the branch's `Fixed` evidence, `fixedRescaling`, which the side the loop hands on does not "
            "match.",
        old="""      let (e, (r, alpha)) := awaitAlpha(e, b, st)
      let (e, grows) := voteAny(e, Core.lt(alpha, one))""",
        new="""      let (e, grows) := voteAny(e, Core.lt(one, one))
      let (r, alpha) := (st, one)""",
    ),
    dict(
        name="publish_inside_warpwise_arm", expect="TypeMismatch", mentions="Core.Group.warpwise(8, 4)",
        why="A warp that rescales publishes Ô and takes the next block's α inside the branch on its vote: the warps that "
            "skip would not, so the warpgroup's α-ring registers would disagree between warps and P full's phase would "
            "count arrivals of different blocks. Protocol operations need `warps(f, 4)`, which a `warpwise` arm is not.",
        old="""          : Pair(Ctx(k, Group.warpwise(8, 4)), Rescaling(x, m, 8)) => rescaleQuadrant(e, b, r, alpha)""",
        new="""          : Pair(Ctx(k, Group.warpwise(8, 4)), Rescaling(x, m, 8)) => {
            let (e, r) := rescaleQuadrant(e, b, r, alpha)
            let (e, st) := publishRescaled(e, b, r)
            let (e, (r, a)) := awaitAlpha(e, b, st)
            (e, r)
          }""",
    ),
    dict(
        name="softmax_rescales_quadrant", expect="TypeMismatch", mentions="Core.Rescaler.softmax",
        why="The softmax warpgroup rescales Ô itself, as A3a's does: its warp 0 would read and write the lanes of "
            "quadrant 0 that the correction warpgroup's warp 8 rescales at the same time. `rescaleRow` takes a buffer "
            "whose rescaler is the softmax warpgroup, and `withCorrectedBuffer` makes one whose rescaler is the "
            "correction warpgroup.",
        old="""      let (e, st) := publishAlpha(e, buf, p, alpha)""",
        new="""      let (e, p) := rescaleRow(e, buf, p, alpha)
      let (e, st) := publishAlpha(e, buf, p, alpha)""",
    ),
    dict(
        name="alpha_before_scores", expect="ImplicitReconstructionFailed",
        mentions="Core.publishAlpha: expected an application of Core.Probs",
        why="Sends α before awaiting the block's scores: the correction warpgroup would then rescale Ô before the "
            "softmax warpgroup observed the product of the block before complete, so nothing would order the rescale "
            "after it (A57). `publishAlpha` takes `Probs`, which only the block's scores give.",
        old="""      let (e, scored) := awaitScores(e, buf, st)""",
        new="""      let (e, st) := publishAlpha(e, buf, st, lowest)
      let (e, scored) := awaitScores(e, buf, st)""",
    ),
    dict(
        name="publish_twice", expect="LinearReused", mentions="r has a linear type",
        why="The correction warpgroup arrives on P full twice in one block: P full's phase would complete with the "
            "arrivals of two of its blocks and none of the softmax warpgroup's, and the product would read a P not yet "
            "written. `publishRescaled` consumes the block's `Rescaling`.",
        old="""rescaleQuadrant(e, b, r, alpha))
      publishRescaled(e, b, r)""",
        new="""rescaleQuadrant(e, b, r, alpha))
      let (e, st) := publishRescaled(e, b, r)
      publishRescaled(e, b, r)""",
    ),
    dict(
        name="skip_per_thread", expect="TypeMismatch", mentions="Core.Group.diverged(128)",
        why="Decides the rescale skip per thread, on the row's own α rather than the warp's vote: a warp would run "
            "`tcgen05.ld/st`, which are warp-collective, with some of its lanes only. A branch on a thread-grain "
            "condition runs its arms `diverged`, and `rescaleQuadrant` needs `warpwise`, which only a warp-grain "
            "condition (`voteAny`) gives.",
        old="""      let (e, grows) := voteAny(e, Core.lt(alpha, one))""",
        new="""      let grows := Core.lt(alpha, one)""",
    ),
    dict(
        name="registers_on_one_warp", expect="TypeMismatch", mentions="Core.Group.cta(512)",
        why="The issuing warp sets register counts on its own: `setmaxnreg` must be run by every warp of a warpgroup, "
            "identically, and before any of the warpgroup's role. Only `splitWarpgroups` emits it, as the first "
            "instruction of each warpgroup's branch of a 512-thread CTA, so a single warp cannot.",
        old="""  // ---- The CTA ---""",
        new="""  def oneWarp {l: Lifetime}(regs: RegPermit(l))(m: Lifetime)(e: Ctx(m, CorrectedIssue)): Ctx(m, CorrectedIssue) :=
    splitWarpgroups(e, regs, 192, 192, 72, 56,
      fun (n: Lifetime)(e: Ctx(n, Group.warps(0, 4))): Pair(Ctx(n, Group.warps(0, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(4, 4))): Pair(Ctx(n, Group.warps(4, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(8, 4))): Pair(Ctx(n, Group.warps(8, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(12, 4))): Pair(Ctx(n, Group.warps(12, 4)), Unit) => (e, Unit.unit))

  // ---- The CTA ---""",
    ),
]
