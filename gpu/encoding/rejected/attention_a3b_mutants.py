# A3b's kernel (encoding/examples/attention_a3b.rac, gpu/encoding/A3B.md) with one mistake each in its use of the
# correction warpgroup, the α ring, `warpwise` and the register split (A3B.md §5): every mutant breaks a rule and is
# refused for that rule. Run by check.sh through gpu/mutate.py.
#
# What is not a refusal, and so has no mutant here:
# - A softmax writing the α slot before its empty wait: not expressible. `publishAlpha` waits for the slot, writes it
#   and arrives on its full barrier in one operation, and it is the only writer of the ring.
# - Reading α from the slot before its full wait: not expressible. `awaitAlpha` waits, fences, reads and frees the slot
#   in one operation.
# - Setting a warpgroup's register count in the middle of its role: not expressible. Only `splitWarpgroups` emits
#   `setmaxnreg`, through emitters that need the Key and a warpgroup's share, and the shares exist only between a split
#   and its join. Splitting again after the join is allowed and safe (`checks/registers.rac`).
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
        new="""  def oneWarp {l: Lifetime}(regs: Registers.RegPool(l, 512, 128))(m: Lifetime)(e: Ctx(m, CorrectedIssue)): Ctx(m, CorrectedIssue) :=
    splitWarpgroups(e, regs, 192, 192, 72, 56,
      fun (n: Lifetime)(e: Ctx(n, Group.warps(0, 4))): Pair(Ctx(n, Group.warps(0, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(4, 4))): Pair(Ctx(n, Group.warps(4, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(8, 4))): Pair(Ctx(n, Group.warps(8, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(12, 4))): Pair(Ctx(n, Group.warps(12, 4)), Unit) => (e, Unit.unit))

  // ---- The CTA ---""",
    ),
    dict(
        name="registers_over_pool", expect="EvidenceNotDischarged", mentions="Evidence fits of Core.splitWarpgroups",
        why="Gives both softmax warpgroups 256 registers per thread: 128 · (256 + 256 + 72 + 56) is more than the pool's "
            "512 · 128, so a softmax warpgroup's first increase would wait forever for registers no decrease frees. "
            "`Registers.split` requires the counts to fit the pool.",
        old="""  // ---- The CTA ---""",
        new="""  def overPool {l: Lifetime}(regs: Registers.RegPool(l, 512, 128))(e: Ctx(l, CorrectedCta)): Ctx(l, CorrectedCta) :=
    splitWarpgroups(e, regs, 256, 256, 72, 56,
      fun (n: Lifetime)(e: Ctx(n, Group.warps(0, 4))): Pair(Ctx(n, Group.warps(0, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(4, 4))): Pair(Ctx(n, Group.warps(4, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(8, 4))): Pair(Ctx(n, Group.warps(8, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(12, 4))): Pair(Ctx(n, Group.warps(12, 4)), Unit) => (e, Unit.unit))

  // ---- The CTA ---""",
    ),
    dict(
        name="pool_at_other_count", expect="RegisterCheck", mentions="setmaxnreg.inc 72 does not change from the budget 128",
        why="Creates a second pool, at residency 2 (64 registers per thread), and splits it after the kernel's own: "
            "`Registers.pool` is a definition any module can call, and the counts 72/56/64/64 fit a pool at 64, so "
            "the kernel generates. But its warps hold 128, so the split's first changes are from a count they do not "
            "hold, and its way back leaves them at 64. The register check reads every split's `setmaxnreg`s against "
            "the kernel's own budget, from its bounds, and fails it.",
        edits=[
            ("""    let (e, u) := withTmem(e, permit, 512, AccState.empty, Unit, regions)
    e
  }""", """    let (e, u) := withTmem(e, permit, 512, AccState.empty, Unit, regions)
    splitWarpgroups(e, Registers.pool(l, 512, 2), 72, 56, 64, 64,
      fun (n: Lifetime)(e: Ctx(n, Group.warps(0, 4))): Pair(Ctx(n, Group.warps(0, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(4, 4))): Pair(Ctx(n, Group.warps(4, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(8, 4))): Pair(Ctx(n, Group.warps(8, 4)), Unit) => (e, Unit.unit),
      fun (n: Lifetime)(e: Ctx(n, Group.warps(12, 4))): Pair(Ctx(n, Group.warps(12, 4)), Unit) => (e, Unit.unit))
  }"""),
        ],
    ),
    dict(
        name="softmax_starved", expect="RegisterCheck", mentions="in the role at line 73 (setmaxnreg.dec 64)",
        why="Gives the softmax warpgroups 64 registers per thread, where a thread holds a row's 128 scores: the counts "
            "fit the pool, so the kernel generates, but `ptxas` spills the softmax roles to local memory, and the "
            "register check (toolkit/registers.py) attributes the `STL`s and `LDL`s to the first softmax role.",
        edits=[
            ("""              (rolesCorrected(e, regs,""", """              (starved(e, regs,"""),
            ("""  // ---- The CTA ---""", """  def starved {l: Lifetime}{k0: Kind}{S0: Lifetime}{k1: Kind}{S1: Lifetime}{k2: Kind}{S2: Lifetime}{k3: Kind}{S3: Lifetime}
      {k4: Kind}{S4: Lifetime}(e: Ctx(l, CorrectedCta))(regs: Registers.RegPool(l, 512, 128))
      (group0: { kind = k0, scope = S0 } (m: Lifetime) -> Ctx(m, Group.warps(0, 4)) -> Pair(Ctx(m, Group.warps(0, 4)), Unit))
      (group1: { kind = k1, scope = S1 } (m: Lifetime) -> Ctx(m, Group.warps(4, 4)) -> Pair(Ctx(m, Group.warps(4, 4)), Unit))
      (correct: { kind = k2, scope = S2 } (m: Lifetime) -> Ctx(m, Group.warps(8, 4)) -> Pair(Ctx(m, Group.warps(8, 4)), Unit))
      (issue: { kind = k3, scope = S3 } (m: Lifetime) -> Ctx(m, CorrectedIssue) -> Pair(Ctx(m, CorrectedIssue), Unit))
      (load: { kind = k4, scope = S4 } (m: Lifetime) -> Ctx(m, CorrectedLoad) -> Pair(Ctx(m, CorrectedLoad), Unit))
      : Ctx(l, CorrectedCta) := {
    let idle13 := fun (m: Lifetime)(e: Ctx(m, Group.warps(13, 1))): Pair(Ctx(m, Group.warps(13, 1)), Unit) => (e, Unit.unit)
    let idle15 := fun (m: Lifetime)(e: Ctx(m, Group.warps(15, 1))): Pair(Ctx(m, Group.warps(15, 1)), Unit) => (e, Unit.unit)
    let last := fun (m: Lifetime)(e: Ctx(m, Group.warps(14, 2))): Pair(Ctx(m, Group.warps(14, 2)), Pair(Unit, Unit)) =>
      split(e, 1, Unit, Unit, load, idle15)
    let rest := fun (m: Lifetime)(e: Ctx(m, Group.warps(13, 3))): Pair(Ctx(m, Group.warps(13, 3)), Pair(Unit, Pair(Unit, Unit))) =>
      split(e, 1, Unit, Pair(Unit, Unit), idle13, last)
    let tensor := fun (m: Lifetime)(e: Ctx(m, Group.warps(12, 4))): Pair(Ctx(m, Group.warps(12, 4)), Unit) => {
      let (e, u) := split(e, 1, Unit, Pair(Unit, Pair(Unit, Unit)), issue, rest)
      (e, Unit.unit)
    }
    splitWarpgroups(e, regs, 64, 64, 72, 56, group0, group1, correct, tensor)
  }

  // ---- The CTA ---"""),
        ],
    ),
]
