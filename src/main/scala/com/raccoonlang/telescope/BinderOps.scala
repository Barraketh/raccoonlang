package com.raccoonlang.telescope

import com.raccoonlang.Value.{VBinder, VPi}
import com.raccoonlang._

object BinderOps {
  final case class CheckedBinders(
      vBinders: Vector[VBinder],
      elabBinders: Vector[ElabAst.Binder],
      env: Env[Value]
  )

  def freshen(binders: Vector[VBinder], baseEnv: Env[Value]): Env[Value] = {
    var env = baseEnv
    binders.foreach { binder =>
      env = freshenBinder(env, binder)
    }

    env
  }

  def freshen(vpi: VPi): Env[Value] = freshen(vpi.binders, vpi.env)

  // Fresh copy of a constructor's telescope: a fresh value per binder plus the instantiated result
  // type. Shared by MatchChecker (reachability, the large-elimination permit) and
  // Interpreter.reduceSubsingletonMatch — the runtime diagonal check is sound only because it
  // re-derives exactly the telescope the checker validated (proof-collapse.md §10).
  def freshCtorArgsAndResult(head: Value.ConstructorHead): (Vector[Value], Value) =
    head.tpe match {
      case pi: VPi =>
        val fresh = freshen(pi)
        (pi.binders.map(binder => fresh(binder.localRef)), pi.codomain(fresh))
      case _ => (Vector.empty, head.tpe)
    }

  /**
   * Check a telescope's binder types and compile the implicit projection specs (Projection.compile).
   * Every implicit binder must be forced by later non-implicit binders; the leading `familyParams`
   * binders of a constructor telescope are demoted to explicit instead of erroring when unforced.
   */
  def toVBinders(
      binders: Vector[CoreAst.Binder],
      baseEnv: Env[Value],
      familyParams: Int = 0
  ): CheckedBinders = {
    var env = baseEnv
    val checkedTys = binders.map { binder =>
      val checkedTy = TypeChecker.checkTypeTerm(binder.ty, env)
      TypeChecker.assertType(checkedTy.value)
      val provisional = VBinder(binder.localRef, checkedTy.residual, binder.isImplicit)
      env = freshen(Vector(provisional), env)
      checkedTy
    }

    val inputs = binders.map { binder =>
      Projection.BinderInput(binder.name, binder.span, binder.isImplicit, env(binder.localRef))
    }
    val compiled = Projection.compile(inputs, familyParams)

    val vBinders = Vector.newBuilder[VBinder]
    val checkedBinders = Vector.newBuilder[ElabAst.Binder]
    binders.indices.foreach { idx =>
      val binder = binders(idx)
      val residualTy = checkedTys(idx).residual
      val result = compiled(idx)
      vBinders += VBinder(binder.localRef, residualTy, result.isImplicit, result.projection)
      checkedBinders += ElabAst.Binder(
        binder.localRef,
        residualTy,
        binder.span,
        result.isImplicit,
        result.projection
      )
    }

    CheckedBinders(vBinders.result(), checkedBinders.result(), env)
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
    VBinder(binder.localRef, binder.ty, binder.isImplicit, binder.projection)

  private def freshenBinder(env: Env[Value], binder: VBinder): Env[Value] = {
    val expectedTy = Interpreter.evalTypeTerm(binder.ty, env)
    val (_, fresh) = FreshVar.freshValue(binder.name, expectedTy)
    env.putLocal(binder.localRef, Value.collapseBinderWitness(expectedTy, fresh))
  }

  def bindValue(env: Env[Value], binder: VBinder, actual: Value): Env[Value] =
    env.putLocal(binder.localRef, actual)

  def bindValueAndCheck(env: Env[Value], binder: VBinder, actual: Value): Env[Value] = {
    val expectedTy = Interpreter.evalTypeTerm(binder.ty, env)
    TypeChecker.checkType(actual, expectedTy)
    env.putLocal(binder.localRef, Value.ascribe(actual, expectedTy))
  }
}
