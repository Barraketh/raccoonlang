package com.raccoonlang

object BinderOps {
  import com.raccoonlang.Util.NEL
  import com.raccoonlang.Value.Var

  import scala.collection.immutable.BitSet

  final case class Freshened(vars: Vector[Var], env: Env, newVars: BitSet)

  def freshen(binders: NEL[CoreAst.Binder], baseEnv: Env, eqStore: EqStore): Freshened = {
    val (vars, env, newVars) =
      binders.foldLeft((Vector.empty[Var], baseEnv.newScope, BitSet.empty)) {
        case ((curVars, curEnv, curNewVars), binder) =>
          val (openedEnv, tyV, openedNewVars) = TypePatternOps.freshOpen(curEnv, binder.ty, eqStore)
          val fresh = FreshVar.freshVar(binder.name, tyV)
          (
            curVars :+ fresh,
            openedEnv.putLocal(binder.name, fresh),
            curNewVars ++ openedNewVars + fresh.id
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
}
