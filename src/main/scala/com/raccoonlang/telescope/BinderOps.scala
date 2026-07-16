package com.raccoonlang.telescope

import com.raccoonlang.Value.VPi
import com.raccoonlang._

object BinderOps {
  private final case class FreshenedBinder(value: Value, holeId: Option[Value.VarId])

  final case class CheckedBinders(
      binders: Vector[ElabAst.Binder],
      env: Env
  )

  def freshen(binders: Vector[ElabAst.Binder], baseEnv: Env): Env = {
    var env = baseEnv
    binders.foreach { binder =>
      env = env.putLocal(binder.localRef, freshenBinder(env, binder).value)
    }

    env
  }

  def freshen(vpi: VPi): Env = freshen(vpi.binders, vpi.env)

  // Fresh copy of a constructor's telescope: a fresh value per binder plus the instantiated result
  // type. Used by MatchChecker for reachability and branch refinement.
  def freshCtorArgsAndResult(head: Value.ConstructorHead): (Vector[Value], Value) =
    head.tpe match {
      case pi: VPi =>
        val fresh = freshen(pi)
        (pi.binders.map(binder => fresh(binder.localRef)), pi.codomain(fresh))
      case _ => (Vector.empty, head.tpe)
    }

  /**
   * Check a telescope's binder types and compile the implicit projection specs (Projection.compile). Every implicit
   * binder must be forced by later non-implicit binders; the leading `familyParams` binders of a constructor telescope
   * are demoted to explicit instead of erroring when unforced.
   */
  def checkBinders(
      binders: Vector[CoreAst.Binder],
      baseEnv: Env,
      familyParams: Int = 0
  ): CheckedBinders = {
    var env = baseEnv
    val holeIds = Vector.newBuilder[Option[Value.VarId]]
    val checkedTys = binders.map { binder =>
      val checkedTy = TypeChecker.checkTerm(binder.ty, env)
      TypeChecker.assertType(checkedTy.value)
      val provisional = ElabAst.Binder(binder.localRef, checkedTy.residual, binder.span, binder.isImplicit)
      val freshened = freshenBinder(env, provisional)
      env = env.putLocal(binder.localRef, freshened.value)
      holeIds += freshened.holeId
      checkedTy
    }

    val inputs = binders.zip(holeIds.result()).map { case (binder, holeId) =>
      Projection.BinderInput(binder.name, binder.span, binder.isImplicit, env(binder.localRef), holeId)
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
  // fresh field witnesses (StructEta — eta holds by representation), prop-typed ones enter their
  // type-determined canonical proof form, everything else is a bare fresh Var. Non-proof binders
  // expose either a fresh id or their whole eta-expanded pattern to implicit-projection
  // compilation; proof binders are recognized there by proposition instead, so runtime proof
  // representation carries no witness metadata.
  private def freshenBinder(env: Env, binder: ElabAst.Binder): FreshenedBinder = {
    val expectedTy = Interpreter.evalTerm(binder.ty, env)
    StructEta.freshStructWitness(expectedTy) match {
      case Some(witness) => FreshenedBinder(witness, None)
      case None =>
        val (id, fresh) = FreshVar.freshValue(binder.name, expectedTy)
        val canonical = Value.canonicalizeRigidBinder(expectedTy, fresh)
        FreshenedBinder(canonical, Option.when(!Value.isPropositionType(expectedTy))(id))
    }
  }

  def bindValue(env: Env, binder: ElabAst.Binder, actual: Value): Env =
    env.putLocal(binder.localRef, Value.canonicalizeProof(actual))

  def bindValueAndCheck(env: Env, binder: ElabAst.Binder, actual: Value): Env = {
    val expectedTy = Interpreter.evalTerm(binder.ty, env)
    TypeChecker.checkType(actual, expectedTy)
    env.putLocal(binder.localRef, Value.ascribe(actual, expectedTy))
  }
}
