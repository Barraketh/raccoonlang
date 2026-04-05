package com.raccoonlang

import com.raccoonlang.Util.NEL
import com.raccoonlang.Value.{VPi, Var, VarId}

import scala.collection.immutable.BitSet

object FreshVar {

  // Fresh symbol name helper
  private var gensymId: VarId = 0
  def freshVar(name: String, tpe: Value) = {
    gensymId += 1
    Var(name, gensymId, tpe)
  }

  def assignFreshVars(binders: NEL[CoreAst.Binder], env: Env, meta: EqStore): (Vector[Var], Env, BitSet) = {
    val res = BinderOps.freshen(binders, env, meta)
    (res.vars, res.env, res.newVars)
  }

  def assignFreshVars(binders: Vector[CoreAst.Binder], env: Env, meta: EqStore): (Vector[Var], Env, BitSet) = {
    if (binders.isEmpty) (Vector.empty, env, BitSet.empty)
    else assignFreshVars(NEL.mk(binders), env, meta)
  }

  def assignFreshVars(vpi: VPi, meta: EqStore): (Vector[Var], Env, BitSet) =
    assignFreshVars(vpi.binders, vpi.env, meta)

}
