package com.raccoonlang

import com.raccoonlang.Value.VarId

// Tracks equalities between variables
final case class EqStore(links: Map[VarId, Value]) {
  @annotation.tailrec
  def force(v: Value): Value = v match {
    case Value.Var(_, id, _) =>
      links.get(id) match {
        case Some(v) => force(v)
        case None    => v
      }
    case other => other
  }

  def addLink(id: VarId, v: Value): EqStore = {
    if (links.contains(id)) throw VarAlreadyLinked(id)
    copy(links = links + (id -> v))
  }
}

object EqStore {
  val empty: EqStore = EqStore(Map())
}
