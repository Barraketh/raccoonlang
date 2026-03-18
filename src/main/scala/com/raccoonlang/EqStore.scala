package com.raccoonlang

import com.raccoonlang.Value.VarId

import scala.collection.immutable.BitSet

// Tracks equalities between variables
final case class EqStore(links: Map[VarId, Value], refinable: BitSet) {
  @annotation.tailrec
  def force(v: Value): Value = v match {
    case Value.Var(_, id, _) =>
      links.get(id) match {
        case Some(v) => force(v)
        case None    => v
      }
    case other => other
  }

  def isRefinable(id: VarId): Boolean = refinable.contains(id)

  def allow(ids: BitSet): EqStore = copy(refinable = refinable ++ ids)

  def addLink(id: VarId, v: Value): EqStore = {
    if (links.contains(id)) throw VarAlreadyLinked(id)
    if (!refinable.contains(id)) throw WTF("Tried to solve a var not in refinable set")
    copy(links = links + (id -> v))
  }
}

object EqStore {
  val empty: EqStore = EqStore(Map(), BitSet.empty)
}
