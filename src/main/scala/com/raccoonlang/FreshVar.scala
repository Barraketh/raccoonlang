package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value.{VPi, VSort, Var, VarId}

import scala.collection.immutable.BitSet

object FreshVar {

  // Fresh symbol name helper
  private var gensymId: VarId = 0
  def freshVar(name: String, tpe: Value) = {
    gensymId += 1
    Var(name, gensymId, tpe)
  }

  // Fresh name helper for binder/capture names
  private var freshNameId: Int = 0
  def freshName(base: String): String = {
    freshNameId += 1
    s"${base}${freshNameId}"
  }

  def assignFreshVars(binders: NEL[CoreAst.Binder], env: Env, meta: EqStore): (Vector[Var], Env, BitSet) =
    binders.foldLeft((Vector.empty[Var], env.newScope, BitSet.empty)) {
      case ((curValues, curEnv, curNewVars), binder) =>
        val (openedEnv, tyV, newVars) = TypePatternOps.freshOpen(curEnv, binder.ty, meta)

        resolveInEqStore(tyV.tpe)(meta) match {
          case _: VSort =>
          case _        => throw NotAType(tyV, Some(binder.span))
        }
        val fresh = freshVar(binder.name, tyV)
        (curValues :+ fresh, openedEnv.putLocal(binder.name, fresh), curNewVars ++ newVars + fresh.id)
    }

  def assignFreshVars(binders: Vector[CoreAst.Binder], env: Env, meta: EqStore): (Vector[Var], Env, BitSet) = {
    if (binders.isEmpty) (Vector.empty, env, BitSet.empty)
    else assignFreshVars(NEL.mk(binders), env, meta)
  }

  def assignFreshVars(vpi: VPi, meta: EqStore): (Vector[Var], Env, BitSet) =
    assignFreshVars(vpi.binders, vpi.env, meta)

}
