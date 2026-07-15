package com.raccoonlang

import com.raccoonlang.Value.{Var, VarId}

// Global fresh-variable supply. Var identity (and therefore defEq, DepSets and the unifier's
// watermark checks) relies on ids being unique and monotonically increasing; the counter is
// unsynchronized, so the whole pipeline assumes a single checking thread.
object FreshVar {

  private var gensymId: VarId = 0
  def currentId: VarId = gensymId

  def freshVar(name: String, tpe: Value) = {
    gensymId += 1
    Var(name, gensymId, tpe)
  }

  /**
   * A fresh unknown as a Value. Level-typed unknowns must be Level atoms rather than Vars so that level arithmetic
   * (Level.max/imax/succ, unifyLevels) can see them; every producer of fresh unknowns must apply this rule, so it lives
   * here.
   */
  def freshValue(name: String, tpe: Value): (VarId, Value) = {
    val fresh = freshVar(name, tpe)
    val value =
      tpe match {
        case Value.LevelTpe => Value.Level.mk(fresh.id)
        case _              => fresh
      }
    (fresh.id, value)
  }
}
