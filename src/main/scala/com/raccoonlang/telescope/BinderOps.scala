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
      env = freshenBinder(env, binder)
    }

    env
  }

  def freshen(binders: Vector[VBinder], baseContext: TypingContext): TypingContext = {
    var context = baseContext
    binders.foreach { binder =>
      val env = freshenBinder(context.env, binder)
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
      val checkedTy = TypeChecker.checkTypeTerm(binder.ty, context)
      TypeChecker.assertType(checkedTy.value)
      val checkedBinder = ElabAst.Binder(binder.localRef, checkedTy.residual, binder.span, binder.isInstance)
      val vBinder = VBinder(binder.localRef, checkedTy.residual, binder.isImplicit, binder.isInstance)
      vBinders += vBinder
      checkedBinders += checkedBinder
      context = freshen(Vector(vBinder), context)
    }

    CheckedBinders(vBinders.result(), checkedBinders.result(), context)
  }

  def instantiateFull(binders: Vector[VBinder], baseEnv: Env[Value], args: Vector[Value]): Env[Value] = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(baseEnv) { case (curEnv, (binder, value)) =>
      bindValue(curEnv, binder, value)
    }
  }

  def checkAndInstantiate(
      binders: Vector[VBinder],
      runtimeEnv: Env[Value],
      args: Vector[Value]
  ): Env[Value] = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(runtimeEnv) { case (curEnv, (binder, value)) =>
      bindValueAndCheck(curEnv, binder, value)
    }
  }

  def toVBinder(binder: ElabAst.Binder): VBinder =
    VBinder(binder.localRef, binder.ty, isImplicit = false, binder.isInstance)

  private def freshenBinder(env: Env[Value], binder: VBinder): Env[Value] = {
    val expectedTy = Interpreter.evalTypeTerm(binder.ty, env)
    val fresh = FreshVar.freshVar(binder.name, expectedTy)
    val value =
      expectedTy match {
        case Value.LevelTpe => Value.Level.mk(fresh.id)
        case _              => fresh
      }
    env.putLocal(binder.localRef, value)
  }

  def bindValue(env: Env[Value], binder: VBinder, actual: Value): Env[Value] =
    env.putLocal(binder.localRef, actual)

  def bindValueAndCheck(env: Env[Value], binder: VBinder, actual: Value): Env[Value] = {
    val expectedTy = Interpreter.evalTypeTerm(binder.ty, env)
    TypeChecker.checkType(actual, expectedTy)
    env.putLocal(binder.localRef, Value.ascribe(actual, expectedTy))
  }
}
