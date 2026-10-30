package com.raccoonlang

import com.raccoonlang.Value.VarId

// Tracks equalities between variables through substitution
final case class EqStore(subst: Map[VarId, Value], refinable: DepSet) {
  @annotation.tailrec
  def force(v: Value): Value = v match {
    case Value.Var(_, id, _) =>
      subst.get(id) match {
        case Some(v) => force(v)
        case None    => v
      }
    case other => other
  }

  def isRefinable(id: VarId): Boolean = refinable.contains(id)

  def allow(ids: DepSet): EqStore = copy(refinable = refinable ++ ids)

  def addLink(id: VarId, v: Value): EqStore = {
    if (subst.contains(id)) throw VarAlreadyLinked(id)
    if (!refinable.contains(id)) throw WTF("Tried to solve a var not in refinable set")
    copy(subst = subst + (id -> v))
  }

  /**
   * Whether `id` occurs in `in` through the solved variables. A proof call's dependencies over-approximate its forced
   * value's, so an occurrence is confirmed through forced values (`Value.forcedDeps`), as eager evaluation found it.
   */
  def occurs(id: VarId, in: Value): Boolean = transitiveDeps(in).contains(id) && occursForced(id, in)

  /**
   * What a link of `id` to `value` holds, or `None` when `id` occurs in it (`occurs`). Where `id` occurs only in the
   * arguments of proof calls, their forced values do not mention it, and the link holds `value` with those calls forced
   * (`ValueOps.forceProofCalls`), as eager evaluation's did: otherwise materializing it would meet `id` again.
   */
  def linkable(id: VarId, value: Value): Option[Value] =
    if (!transitiveDeps(value).contains(id)) Some(value)
    else if (occursForced(id, value)) None
    else Some(ValueOps.forceProofCalls(value, this, DepSet.single(id)))

  private def occursForced(id: VarId, in: Value): Boolean = {
    val wanted = solvedIds + id
    val seen = DepSet.newBuilder
    var frontier = Value.forcedDeps(in, wanted)
    while (frontier.nonEmpty) {
      if (frontier.contains(id)) return true
      seen.unionInPlace(frontier)
      val next = DepSet.newBuilder
      frontier.foreach(solved => next.unionInPlace(Value.forcedDeps(subst(solved), wanted)))
      next.diffInPlace(seen)
      frontier = next.result()
    }
    false
  }

  lazy val solvedIds: DepSet = DepSet.from(subst.keySet)

  private def transitiveDeps(v: Value): DepSet = {
    val seen = DepSet.newBuilder(v.synDeps)
    var frontier = v.synDeps

    while (frontier.nonEmpty) {
      val toExpand = frontier & solvedIds
      val next = DepSet.newBuilder

      toExpand.foreach { id =>
        next.unionInPlace(subst(id).synDeps)
      }

      next.diffInPlace(seen)
      if (next.isEmpty) return seen.result()

      seen.unionInPlace(next)
      frontier = next.result()
    }

    seen.result()
  }

}

object EqStore {
  val empty: EqStore = EqStore(Map(), DepSet.empty)
}
