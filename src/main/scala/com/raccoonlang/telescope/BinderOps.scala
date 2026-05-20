package com.raccoonlang.telescope

import com.raccoonlang.Value.{VBinder, VPi}
import com.raccoonlang._

object BinderOps {
  def freshen[E <: EnvLike[E]](binders: Vector[VBinder], baseEnv: E)(implicit eqStore: EqStore): E = {
    var env = baseEnv
    binders.foreach { binder =>
      env = TypePatternOps.freshenBinder(env, binder)
    }

    env
  }

  def freshen(vpi: VPi)(implicit eqStore: EqStore): RuntimeEnv = freshen(vpi.binders, vpi.env)

  def toVBinders(binders: Vector[CoreAst.Binder], baseEnv: TypecheckEnv)(implicit
      eqStore: EqStore
  ): (Vector[VBinder], Vector[ElabAst.Binder]) = {
    val vBinders = Vector.newBuilder[VBinder]
    val checkedBinders = Vector.newBuilder[ElabAst.Binder]
    var env = baseEnv

    binders.foreach { binder =>
      val (vBinder, checkedBinder) = TypePatternOps.toVBinder(binder, env)
      vBinders += vBinder
      checkedBinders += checkedBinder
      env = freshen(Vector(vBinder), env)
    }

    (vBinders.result(), checkedBinders.result())
  }

  def instantiateFull(binders: Vector[VBinder], baseEnv: RuntimeEnv, args: Vector[Value])(implicit
      eqStore: EqStore
  ): RuntimeEnv = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(baseEnv) { case (curEnv, (binder, value)) =>
      TypePatternOps.bindValue(curEnv, binder, value)
    }
  }

  def checkAndInstantiate(
      binders: Vector[VBinder],
      runtimeEnv: RuntimeEnv,
      args: Vector[Value],
      normalizerMap: Normalizers.NormalizerMap
  )(implicit
      eqStore: EqStore
  ): RuntimeEnv = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(runtimeEnv) { case (curRuntimeEnv, (binder, value)) =>
      TypePatternOps.bindValueAndCheck(curRuntimeEnv, binder, value, normalizerMap)
    }
  }
}
