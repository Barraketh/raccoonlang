package com.raccoonlang.telescope

import com.raccoonlang.Value.VPi
import com.raccoonlang._

object BinderOps {
  final case class CheckedBinders(
      binders: Vector[ElabAst.Binder],
      env: Env
  )

  def freshen(binders: Vector[ElabAst.Binder], baseEnv: Env): Env = {
    var env = baseEnv
    binders.foreach { binder =>
      env = freshenBinder(env, binder)
    }

    env
  }

  def freshen(vpi: VPi): Env = freshen(vpi.binders, vpi.env)

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
  def checkBinders(
      binders: Vector[CoreAst.Binder],
      baseEnv: Env,
      familyParams: Int = 0
  ): CheckedBinders = {
    var env = baseEnv
    val checkedTys = binders.map { binder =>
      val checkedTy = TypeChecker.checkTerm(binder.ty, env)
      TypeChecker.assertType(checkedTy.value)
      val provisional = ElabAst.Binder(binder.localRef, checkedTy.residual, binder.span, binder.isImplicit)
      env = freshen(Vector(provisional), env)
      checkedTy
    }

    val inputs = binders.map { binder =>
      Projection.BinderInput(binder.name, binder.span, binder.isImplicit, env(binder.localRef))
    }
    val compiled = Projection.compile(inputs, familyParams)

    val checkedBinders = binders.indices.toVector.map { idx =>
      val binder = binders(idx)
      val result = compiled(idx)
      ElabAst.Binder(
        binder.localRef,
        checkedTys(idx).residual,
        binder.span,
        result.isImplicit,
        result.projection
      )
    }

    CheckedBinders(checkedBinders, env)
  }

  def instantiateFull(binders: Vector[ElabAst.Binder], baseEnv: Env, args: Vector[Value]): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(baseEnv) { case (curEnv, (binder, value)) =>
      bindValue(curEnv, binder, value)
    }
  }

  def checkAndInstantiate(
      binders: Vector[ElabAst.Binder],
      runtimeEnv: Env,
      args: Vector[Value]
  ): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(runtimeEnv) { case (curEnv, (binder, value)) =>
      bindValueAndCheck(curEnv, binder, value)
    }
  }

  // A rigid binder enters in canonical form: struct-typed binders are the constructor applied to
  // fresh field witnesses (StructEta — eta holds by representation), prop-typed ones collapse
  // (the binder is its own witness), everything else is a bare fresh Var.
  private def freshenBinder(env: Env, binder: ElabAst.Binder): Env = {
    val expectedTy = Interpreter.evalTerm(binder.ty, env)
    val witness = StructEta.freshStructWitness(expectedTy).getOrElse {
      val (_, fresh) = FreshVar.freshValue(binder.name, expectedTy)
      Value.collapseBinderWitness(expectedTy, fresh)
    }
    env.putLocal(binder.localRef, witness)
  }

  def bindValue(env: Env, binder: ElabAst.Binder, actual: Value): Env =
    env.putLocal(binder.localRef, actual)

  def bindValueAndCheck(env: Env, binder: ElabAst.Binder, actual: Value): Env = {
    val expectedTy = Interpreter.evalTerm(binder.ty, env)
    TypeChecker.checkType(actual, expectedTy)
    env.putLocal(binder.localRef, Value.ascribe(actual, expectedTy))
  }
}
