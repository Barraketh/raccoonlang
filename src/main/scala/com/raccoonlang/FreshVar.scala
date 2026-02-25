package com.raccoonlang

import com.raccoonlang.Interpreter._

object FreshVar {

  // Fresh symbol name helper
  private var gensymId: VarId = 0
  def freshVar(name: String, tpe: Value) = {
    gensymId += 1
    Var(name, gensymId, tpe)
  }

  def assignFreshVars(vpi: VPi, meta: EqStore): (Vector[Value], Env) =
    vpi.binders.foldLeft(Vector.empty[Value] -> vpi.env.newScope) { case ((curValues, curEnv), binder) =>
      val tyV = evalTerm(binder.ty, meta)(curEnv) // vpi has been typechecked already - no need to typecheck the binders
      val fresh = freshVar(binder.name, tyV)
      (curValues :+ fresh, curEnv.putLocal(binder.name, fresh))
    }

}
