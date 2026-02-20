package com.raccoonlang

import com.raccoonlang.Interpreter.{Env, Meta, MetaId, MetaStore, VPi, Value, evalTerm}

object FreshVar {

  // Fresh symbol name helper
  private var gensymId: MetaId = 0
  def freshVar(name: String, tpe: Value) = {
    gensymId += 1
    Meta(name, gensymId, tpe)
  }

  def assignFreshVars(vpi: VPi, meta: MetaStore): (Vector[Value], Env) =
    vpi.binders.foldLeft(Vector.empty[Value] -> vpi.env) { case ((curValues, curEnv), binder) =>
      val tyV = evalTerm(binder.ty, meta)(curEnv) // vpi has been typechecked already - no need to typecheck the binders
      val fresh = freshVar(binder.name, tyV)
      (curValues :+ fresh, curEnv.put(binder.name, fresh))
    }


}
