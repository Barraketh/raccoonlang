package com.raccoonlang

import com.raccoonlang.Value.VarId

final case class EqStore(subst: Map[VarId, Value], refinable: DepSet) {
  @annotation.tailrec
  def force(value: Value): Value = value match {
    case Value.Var(_, id, _) =>
      subst.get(id) match {
        case Some(next) => force(next)
        case None       => value
      }
    case other => other
  }
  def isRefinable(id: VarId): Boolean = refinable.contains(id)
  def allow(ids: DepSet): EqStore = copy(refinable = refinable ++ ids)
  def addLink(id: VarId, value: Value): EqStore = {
    if (subst.contains(id)) throw WTF(s"Variable $id is already solved")
    if (!refinable.contains(id)) throw WTF(s"Variable $id is not refinable")
    copy(subst = subst.updated(id, value))
  }
  def occurs(id: VarId, value: Value): Boolean = transitiveDeps(value).contains(id)
  lazy val solvedIds: DepSet = DepSet.from(subst.keySet)
  private def transitiveDeps(value: Value): DepSet = {
    var seen = value.synDeps
    var frontier = value.synDeps
    while (frontier.nonEmpty) {
      val solved = frontier & solvedIds
      var next = DepSet.empty
      solved.foreach(id => next = next ++ subst(id).synDeps)
      next = next -- seen
      if (next.isEmpty) return seen
      seen = seen ++ next
      frontier = next
    }
    seen
  }
}
object EqStore { val empty: EqStore = EqStore(Map.empty, DepSet.empty) }
