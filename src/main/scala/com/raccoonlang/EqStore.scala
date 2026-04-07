package com.raccoonlang

import com.raccoonlang.Value.VarId

import scala.collection.immutable.BitSet

// Tracks equalities between variables through substitution
final case class EqStore(subst: Map[VarId, Value], refinable: BitSet) {
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

  def allow(ids: BitSet): EqStore = copy(refinable = refinable ++ ids)

  def addLink(id: VarId, v: Value): EqStore = {
    if (subst.contains(id)) throw VarAlreadyLinked(id)
    if (!refinable.contains(id)) throw WTF("Tried to solve a var not in refinable set")
    copy(subst = subst + (id -> v))
  }

  def occurs(id: VarId, in: Value): Boolean = transitiveDeps(in).contains(id)

  lazy val solvedIds = BitSet.fromSpecific(subst.keySet)

  private def transitiveDeps(v: Value): BitSet = {
    var seen = v.synDeps
    var frontier = v.synDeps

    while (frontier.nonEmpty) {
      val toExpand = frontier & solvedIds
      val next = scala.collection.mutable.BitSet.empty

      toExpand.foreach { id =>
        next |= subst(id).synDeps
      }

      next --= seen
      if (next.isEmpty) return seen

      val nextImm = next.toImmutable
      seen |= nextImm
      frontier = nextImm
    }

    seen
  }

}

object EqStore {
  val empty: EqStore = EqStore(Map(), BitSet.empty)
}
