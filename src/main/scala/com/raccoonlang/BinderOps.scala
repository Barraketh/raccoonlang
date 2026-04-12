package com.raccoonlang

import com.raccoonlang.Value.VPi

object BinderOps {
  import com.raccoonlang.Util.NEL
  import com.raccoonlang.Value.Var

  import scala.collection.immutable.BitSet

  final case class Freshened(vars: Vector[Value], env: Env, newVars: BitSet)

  def freshen(binders: NEL[CoreAst.Binder], baseEnv: Env, eqStore: EqStore): Freshened = {
    val (vars, env, newVars) =
      binders.foldLeft((Vector.empty[Var], baseEnv.newScope, BitSet.empty)) {
        case ((curVars, curEnv, curNewVars), binder) =>
          val opened = TypePatternOps.openPattern(curEnv, binder.ty, eqStore)
          val fresh = FreshVar.freshVar(binder.name, opened.value)
          (
            curVars :+ fresh,
            opened.env.putLocal(binder.name, fresh),
            curNewVars ++ opened.newVars + fresh.id
          )
      }

    Freshened(vars, env, newVars)
  }

  def instantiate(binders: NEL[CoreAst.Binder], baseEnv: Env, args: NEL[Value], eqStore: EqStore): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.toList.zip(args.toList).foldLeft(baseEnv.newScope) { case (curEnv, (binder, value)) =>
      val openedEnv = TypePatternOps.bindValue(curEnv, binder.ty, value.tpe, eqStore)
      openedEnv.putLocal(binder.name, value)
    }
  }

  def checkAndInstantiate(binders: NEL[CoreAst.Binder], baseEnv: Env, args: NEL[Value], eqStore: EqStore)(implicit
      normalizers: NormalizerMap
  ): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.toList.zip(args.toList).foldLeft(baseEnv.newScope) { case (curEnv, (binder, value)) =>
      val openedEnv = TypePatternOps.matchValue(curEnv, binder.ty, value.tpe, eqStore)
      openedEnv.putLocal(binder.name, value)
    }
  }

  // Some alieases for freshen
  def assignFreshVars(binders: NEL[CoreAst.Binder], env: Env, meta: EqStore): (Vector[Value], Env, BitSet) = {
    val res = BinderOps.freshen(binders, env, meta)
    (res.vars, res.env, res.newVars)
  }

  def assignFreshVars(binders: Vector[CoreAst.Binder], env: Env, meta: EqStore): (Vector[Value], Env, BitSet) = {
    if (binders.isEmpty) (Vector.empty, env, BitSet.empty)
    else assignFreshVars(NEL.mk(binders), env, meta)
  }

  def assignFreshVars(vpi: VPi, meta: EqStore): (Vector[Value], Env, BitSet) =
    assignFreshVars(vpi.binders, vpi.env, meta)
}
