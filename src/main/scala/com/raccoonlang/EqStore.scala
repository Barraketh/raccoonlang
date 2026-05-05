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

  def occurs(id: VarId, in: Value): Boolean = transitiveDeps(in).contains(id)

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
