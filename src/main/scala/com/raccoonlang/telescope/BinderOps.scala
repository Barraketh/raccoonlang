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

  final case class CheckedBinders(binders: Vector[CoreAst.Binder], env: Env)

  /** Compile projections for runtime-only values produced by the deliberately unchecked evaluator. */
  def compileRuntime(binders: Vector[CoreAst.Binder], baseEnv: Env): Vector[CoreAst.Binder] = {
    var env = baseEnv
    val inputs = binders.map { binder =>
      val value = freshBinderValue(binder.name, Interpreter.evalTerm(binder.ty, env))
      env = env.putLocal(binder.localRef, value)
      val hole = value match { case Value.Var(_, id, _) => Some(id); case _ => None }
      Projection.BinderInput(binder.name, binder.span, binder.isImplicit, value, hole)
    }
    val compiled = Projection.compile(inputs)
    binders.indices
      .map(i => binders(i).copy(isImplicit = compiled(i).isImplicit, projection = compiled(i).projection))
      .toVector
  }

  /** Check binder types and compile forced-implicit projection specifications. */
  def checkBinders(
      binders: Vector[CoreAst.Binder],
      baseEnv: Env,
      familyParams: Int = 0
  ): CheckedBinders = {
    var env = baseEnv
    val checkedTys = binders.map { binder =>
      val checked = com.raccoonlang.TypeChecker.checkTerm(binder.ty, env)
      com.raccoonlang.TypeChecker.assertType(checked.value)
      val provisional = binder.copy(ty = checked.residual, projection = None)
      val fresh = freshBinderValue(binder.name, checked.value)
      env = env.putLocal(binder.localRef, fresh)
      provisional -> checked
    }
    val inputs = checkedTys.map { case (binder, _) =>
      val fresh = env(binder.localRef)
      val hole = fresh match { case Value.Var(_, id, _) => Some(id); case _ => None }
      Projection.BinderInput(binder.name, binder.span, binder.isImplicit, fresh, hole)
    }
    val compiled = Projection.compile(inputs, familyParams)
    val result = binders.indices.map { i =>
      val (binder, checked) = checkedTys(i)
      binder.copy(ty = checked.residual, isImplicit = compiled(i).isImplicit, projection = compiled(i).projection)
    }.toVector
    CheckedBinders(result, env)
  }

  /** Fresh constructor telescope arguments and its result, including erased family parameters. */
  def freshCtorArgsAndResult(head: Value.ConstructorHead): (Vector[Value], Value) =
    head.tpe match {
      case pi: VPi =>
        val fresh = freshen(pi)
        (pi.binders.map(binder => fresh(binder.localRef)), pi.codomain(fresh))
      case _ => (Vector.empty, head.tpe)
    }

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
