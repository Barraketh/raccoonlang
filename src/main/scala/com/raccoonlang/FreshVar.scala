package com.raccoonlang

import com.raccoonlang.Value.{Var, VarId}

object FreshVar {

  // Fresh symbol name helper
  private var gensymId: VarId = 0
  def freshVar(name: String, tpe: Value) = {
    gensymId += 1
    Var(name, gensymId, tpe)
  }
}
