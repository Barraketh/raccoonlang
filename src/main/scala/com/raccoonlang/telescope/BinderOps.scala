package com.raccoonlang.telescope

import com.raccoonlang.Value.VPi
import com.raccoonlang._

object BinderOps {
  private final case class FreshenedBinder(value: Value, holeId: Option[Value.VarId])

  final case class CheckedBinders(
      binders: Vector[CoreAst.Binder],
      env: Env
  )

  def freshen(binders: Vector[CoreAst.Binder], baseEnv: Env): Env = {
    var env = baseEnv
    binders.foreach { binder =>
      env = env.putLocal(binder.localRef, freshenBinder(env, binder, binder.name).value)
    }

    env
  }

  def freshen(vpi: VPi): Env = freshen(vpi.binders, vpi.env)

  // Fresh copy of a constructor's telescope: a fresh value per binder plus the instantiated result
  // type. Used by MatchChecker for reachability and branch refinement. `fieldNames` are a pattern's
  // names for the stored fields, so a branch's variables print as the user wrote them.
  def freshCtorArgsAndResult(
      head: Value.ConstructorHead,
      fieldNames: Vector[Option[String]]
  ): (Vector[Value], Value) =
    head.pi match {
      case Some(pi) =>
        val fresh = pi.binders.zipWithIndex.foldLeft(pi.env) { case (env, (binder, idx)) =>
          val name = fieldNames.lift(idx - head.numErasedFamilyArgs).flatten.getOrElse(binder.name)
          env.putLocal(binder.localRef, freshenBinder(env, binder, name).value)
        }
        (pi.binders.map(binder => fresh(binder.localRef)), pi.codomain(fresh))
      case None => (Vector.empty, head.tpe)
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
      val provisional = CoreAst.Binder(binder.localRef, checkedTy.residual, binder.span, binder.isImplicit)
      val freshened = freshenBinder(env, provisional, provisional.name)
      env = env.putLocal(binder.localRef, freshened.value)
      holeIds += freshened.holeId
      checkedTy
    }

    val inputs = binders.zip(holeIds.result()).map { case (binder, holeId) =>
      Projection.BinderInput(binder.name, binder.span, binder.isImplicit, env(binder.localRef), holeId)
    }
    val compiled = Projection.compile(inputs, familyParams)

    checked(compiled, binders, checkedTys, env)
  }

  private def checked(
      compiled: Vector[Projection.BinderResult],
      binders: Vector[CoreAst.Binder],
      checkedTys: Vector[TypeChecker.CheckedTerm],
      env: Env
  ): CheckedBinders = {

    val checkedBinders = binders.indices.toVector.map { idx =>
      val binder = binders(idx)
      val result = compiled(idx)
      CoreAst.Binder(
        binder.localRef,
        checkedTys(idx).residual,
        binder.span,
        result.isImplicit,
        result.projection
      )
    }

    CheckedBinders(checkedBinders, env)
  }

  def instantiateFull(binders: Vector[CoreAst.Binder], baseEnv: Env, args: Vector[Value]): Env = {
    if (binders.length != args.length) fail(ArityMismatch(binders.length, args.length))

    binders.zip(args).foldLeft(baseEnv) { case (curEnv, (binder, value)) =>
      bindValue(curEnv, binder, value)
    }
  }

  // A rigid binder enters as a bare fresh Var, or — when its type is a proposition — as the
  // type-determined canonical proof form. Struct-typed binders are ordinary Vars: structure eta is
  // a rule over them, not a representation they have to be built in. Non-proof binders expose
  // their fresh id to implicit-projection compilation; proof binders are recognized there by
  // proposition instead, so runtime proof representation carries no witness metadata.
  private def freshenBinder(env: Env, binder: CoreAst.Binder, name: String): FreshenedBinder = {
    val expectedTy = Interpreter.evalTerm(binder.ty, env)
    val (id, fresh) = FreshVar.freshValue(name, expectedTy)
    val canonical = Value.canonicalizeRigidBinder(expectedTy, fresh)
    // A proof binder exposes no hole: VProof carries no witness id to project from.
    FreshenedBinder(canonical, Option.when(!Value.isPropositionType(expectedTy))(id))
  }

  /**
   * The rigid value a binder of this already-evaluated type enters with, without binding it anywhere. Same canonical
   * form `freshenBinder` produces; callers that walk two telescopes in lockstep need the value alone so they can share
   * one witness between both sides.
   */
  def freshBinderValue(name: String, expectedTy: Value): Value = {
    val (_, fresh) = FreshVar.freshValue(name, expectedTy)
    Value.canonicalizeRigidBinder(expectedTy, fresh)
  }

  def bindValue(env: Env, binder: CoreAst.Binder, actual: Value): Env =
    env.putLocal(binder.localRef, Value.canonicalizeProof(actual))

  def bindValueAndCheck(env: Env, binder: CoreAst.Binder, actual: Value): Env = {
    TypeChecker.checkType(actual, Interpreter.evalTerm(binder.ty, env))
    bindValue(env, binder, actual)
  }
}
