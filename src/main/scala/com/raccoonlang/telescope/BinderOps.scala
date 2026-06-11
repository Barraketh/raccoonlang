package com.raccoonlang.telescope

import com.raccoonlang.Value.{VBinder, VPi}
import com.raccoonlang._

object BinderOps {
  def freshen(binders: Vector[VBinder], baseEnv: Env): Env = {
    var env = baseEnv
    binders.foreach { binder =>
      env = TypePatternOps.freshenBinder(env, binder)
    }

    env
  }

  def freshen(vpi: VPi): Env = freshen(vpi.binders, vpi.env)

  def toVBinders(binders: Vector[CoreAst.Binder], baseEnv: Env): (Vector[VBinder], Vector[ElabAst.Binder]) = {
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

  def instantiateFull(binders: Vector[VBinder], baseEnv: Env, args: Vector[Value], argEnv: Env): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(baseEnv) { case (curEnv, (binder, value)) =>
      TypePatternOps.bindValue(curEnv, binder, value, argEnv)
    }
  }

  def checkAndInstantiate(
      binders: Vector[VBinder],
      runtimeEnv: Env,
      args: Vector[Value],
      argEnv: Env,
      normalizerMap: Normalizers.NormalizerMap
  ): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(runtimeEnv) { case (curRuntimeEnv, (binder, value)) =>
      TypePatternOps.bindValueAndCheck(curRuntimeEnv, binder, value, argEnv, normalizerMap)
    }
  }
}
