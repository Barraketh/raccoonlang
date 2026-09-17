package com.raccoonlang.telescope

import com.raccoonlang.{ArityMismatch, CoreAst, Env, FreshVar, Interpreter, TypeMismatch, Value, ValueEquivalence}
import com.raccoonlang.Value.VPi

/** Telescope operations shared by checking and later projection/refinement passes. */
object BinderOps {
  def freshen(binders: Vector[CoreAst.Binder], baseEnv: Env): Env =
    binders.foldLeft(baseEnv) { case (env, binder) =>
      env.putLocal(binder.localRef, freshBinderValue(binder.name, Interpreter.evalTerm(binder.ty, env)))
    }

  def freshen(pi: VPi): Env = freshen(pi.binders, pi.env)

  def freshBinderValue(name: String, expectedType: Value): Value =
    FreshVar.freshValue(name, expectedType)._2

  def instantiateFull(binders: Vector[CoreAst.Binder], baseEnv: Env, args: Vector[Value]): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)
    binders.zip(args).foldLeft(baseEnv) { case (env, (binder, value)) => env.putLocal(binder.localRef, value) }
  }

  def checkAndInstantiate(
      binders: Vector[CoreAst.Binder],
      runtimeEnv: Env,
      args: Vector[Value]
  ): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)
    binders.zip(args).foldLeft(runtimeEnv) { case (env, (binder, value)) =>
      val expected = Interpreter.evalTerm(binder.ty, env)
      if (!ValueEquivalence.defEq(value.tpe, expected)) throw TypeMismatch(expected, value.tpe)
      env.putLocal(binder.localRef, value)
    }
  }
}
