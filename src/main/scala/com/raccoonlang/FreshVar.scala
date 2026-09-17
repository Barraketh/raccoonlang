package com.raccoonlang

import com.raccoonlang.Value.{Var, VarId}

object FreshVar {
  private var nextId: VarId = 0
  def currentId: VarId = nextId
  def freshVar(name: String, tpe: Value): Var = {
    nextId += 1
    Var(name, nextId, tpe)
  }
  def freshValue(name: String, tpe: Value): (VarId, Value) = {
    val value = freshVar(name, tpe)
    value.id -> value
  }
}
