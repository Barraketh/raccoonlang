package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value.{VPi, Var, VarId}

object FreshVar {

  // Fresh symbol name helper
  private var gensymId: VarId = 0
  def freshVar(name: String, tpe: Value) = {
    gensymId += 1
    Var(name, gensymId, tpe)
  }

  def assignFreshVars(binders: NEL[CoreAst.Binder], env: Env, meta: EqStore): (Vector[Var], Env) =
    binders.foldLeft(Vector.empty[Var] -> env.newScope) { case ((curValues, curEnv), binder) =>
      val tyV =
        evalTypeTerm(binder.ty, curEnv)(meta) // vpi has been typechecked already - no need to typecheck the binders
      val fresh = freshVar(binder.name, tyV)
      (curValues :+ fresh, curEnv.putLocal(binder.name, fresh))
    }

  def assignFreshVars(binders: Vector[CoreAst.Binder], env: Env, meta: EqStore): (Vector[Var], Env) = {
    if (binders.isEmpty) (Vector.empty, env)
    else assignFreshVars(NEL.mk(binders), env, meta)
  }

  def assignFreshVars(vpi: VPi, meta: EqStore): (Vector[Var], Env) = assignFreshVars(vpi.binders, vpi.env, meta)

}
