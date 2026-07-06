package com.raccoonlang.telescope

import com.raccoonlang.Value.{VBinder, VPi}
import com.raccoonlang._

object BinderOps {
  final case class CheckedBinders(
      vBinders: Vector[VBinder],
      elabBinders: Vector[ElabAst.Binder],
      context: TypingContext
  )

  def freshen(binders: Vector[VBinder], baseEnv: Env[Value]): Env[Value] = {
    var env = baseEnv
    binders.foreach { binder =>
      env = TypePatternOps.freshenBinder(env, binder)
    }

    env
  }

  def freshen(binders: Vector[VBinder], baseContext: TypingContext): TypingContext = {
    var context = baseContext
    binders.foreach { binder =>
      val env = TypePatternOps.freshenBinder(context.env, binder)
      context = context.withEnv(env)
      if (binder.isInstance)
        context = context.registerLocalInstance(binder.localRef)
    }

    context
  }

  def freshen(vpi: VPi): Env[Value] = freshen(vpi.binders, vpi.env)

  def toVBinders(
      binders: Vector[CoreAst.Binder],
      baseContext: TypingContext
  ): CheckedBinders = {
    val vBinders = Vector.newBuilder[VBinder]
    val checkedBinders = Vector.newBuilder[ElabAst.Binder]
    var context = baseContext

    binders.foreach { binder =>
      val (vBinder, checkedBinder) = TypePatternOps.toVBinder(binder, context)
      vBinders += vBinder
      checkedBinders += checkedBinder
      context = freshen(Vector(vBinder), context)
    }

    CheckedBinders(vBinders.result(), checkedBinders.result(), context)
  }

  def instantiateFull(binders: Vector[VBinder], baseEnv: Env[Value], args: Vector[Value]): Env[Value] = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(baseEnv) { case (curEnv, (binder, value)) =>
      TypePatternOps.bindValue(curEnv, binder, value)
    }
  }

  def checkAndInstantiate(
      binders: Vector[VBinder],
      runtimeEnv: Env[Value],
      args: Vector[Value]
  ): Env[Value] = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(runtimeEnv) { case (curEnv, (binder, value)) =>
      TypePatternOps.bindValueAndCheck(curEnv, binder, value)
    }
  }
}
