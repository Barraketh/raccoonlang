package com.raccoonlang.telescope

import com.raccoonlang.{ArityMismatch, CoreAst, Env, FreshVar, Interpreter, TypeMismatch, Value, ValueEquivalence}
import com.raccoonlang.Value.VPi

/** Telescope operations shared by checking and later projection/refinement passes. */
object BinderOps {
  private final case class FreshenedBinder(value: Value, holeId: Option[Value.VarId])

  def freshen(binders: Vector[CoreAst.Binder], baseEnv: Env): Env = {
    var env = baseEnv
    binders.foreach { binder =>
      env = env.putLocal(binder.localRef, freshenBinder(env, binder).value)
    }
    env
  }

  def freshen(pi: VPi): Env = freshen(pi.binders, pi.env)

  final case class CheckedBinders(binders: Vector[CoreAst.Binder], env: Env)

  /** Compile projections for runtime-only values produced by the deliberately unchecked evaluator. */
  def compileRuntime(binders: Vector[CoreAst.Binder], baseEnv: Env): Vector[CoreAst.Binder] = {
    var env = baseEnv
    val inputs = binders.map { binder =>
      val freshened = freshenBinder(env, binder)
      env = env.putLocal(binder.localRef, freshened.value)
      Projection.BinderInput(binder.name, binder.span, binder.isImplicit, freshened.value, freshened.holeId)
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
    val holeIds = Vector.newBuilder[Option[Value.VarId]]
    val checkedTys = binders.map { binder =>
      val checked = com.raccoonlang.TypeChecker.checkTerm(binder.ty, env)
      com.raccoonlang.TypeChecker.assertType(checked.value)
      val provisional = binder.copy(ty = checked.residual, projection = None)
      val freshened = freshenBinder(env, provisional)
      env = env.putLocal(binder.localRef, freshened.value)
      holeIds += freshened.holeId
      provisional -> checked
    }
    val inputs = binders.zip(holeIds.result()).map { case (binder, holeId) =>
      Projection.BinderInput(binder.name, binder.span, binder.isImplicit, env(binder.localRef), holeId)
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

  private def freshenBinder(env: Env, binder: CoreAst.Binder): FreshenedBinder = {
    val expectedType = Interpreter.evalTerm(binder.ty, env)
    val (id, fresh) = FreshVar.freshValue(binder.name, expectedType)
    val canonical = Value.canonicalizeRigidBinder(expectedType, fresh)
    FreshenedBinder(canonical, Option.when(!Value.isPropositionType(expectedType))(id))
  }

  def freshBinderValue(name: String, expectedType: Value): Value = {
    val (_, fresh) = FreshVar.freshValue(name, expectedType)
    Value.canonicalizeRigidBinder(expectedType, fresh)
  }

  def instantiateFull(binders: Vector[CoreAst.Binder], baseEnv: Env, args: Vector[Value]): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)
    binders.zip(args).foldLeft(baseEnv) { case (env, (binder, value)) => bindValue(env, binder, value) }
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
      bindValue(env, binder, value)
    }
  }

  def bindValue(env: Env, binder: CoreAst.Binder, actual: Value): Env =
    env.putLocal(binder.localRef, Value.canonicalizeProof(actual))
}
