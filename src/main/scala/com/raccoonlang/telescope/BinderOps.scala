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

  /**
   * A constructor's telescope at a family instance: its parameters bound to the instance's arguments `familyArgs`
   * (`ConstructorHead.fieldEnv`), and a fresh value for each stored field. Returns the fields and the constructor's
   * result type there. Parameters are uniform, so that result carries the instance's own parameter arguments, and only
   * its indices, over the fresh fields, can differ from the instance's. `fieldRefs` are a pattern's locals for the
   * fields, so a branch's variables print as the user wrote them; an anonymous or absent one prints as the
   * constructor's field.
   */
  def freshCtorFields(
      head: Value.ConstructorHead,
      familyArgs: Vector[Value],
      fieldRefs: Vector[CoreAst.LocalRef]
  ): (Vector[Value], Value) =
    head.pi match {
      case Some(pi) =>
        val fresh = head.fieldBinders.zipWithIndex.foldLeft(head.fieldEnv(familyArgs)) { case (env, (binder, idx)) =>
          val name = fieldRefs.lift(idx).map(_.name).filter(_ != "_").getOrElse(binder.name)
          env.putLocal(binder.localRef, freshenBinder(env, binder, name).value)
        }
        (head.fieldBinders.map(binder => fresh(binder.localRef)), pi.codomain(fresh))
      case None => (Vector.empty, head.tpe)
    }

  /**
   * Check a telescope's binder types and compile the implicit projection specs (Projection.compile). A binder's site
   * decides whether it may bind a level, and an evidence binder's type must be a proposition
   * (TypeChecker.checkBinderType). Every implicit binder must be forced by later explicit binders; the leading
   * `familyParams` binders of a constructor telescope are demoted to explicit instead of erroring when unforced. `span`
   * is the telescope's, whose module decides which sealed fields forcing may read.
   */
  def checkBinders(
      binders: Vector[CoreAst.Binder],
      baseEnv: Env,
      familyParams: Int,
      span: Span
  ): CheckedBinders = {
    var env = baseEnv
    val holeIds = Vector.newBuilder[Option[Value.VarId]]
    val checkedTys = binders.map { binder =>
      val checkedTy = TypeChecker.checkBinderType(binder, env)
      val provisional = binder.copy(ty = checkedTy.residual)
      val freshened = freshenBinder(env, provisional, provisional.name)
      env = env.putLocal(binder.localRef, freshened.value)
      holeIds += freshened.holeId
      checkedTy
    }

    val inputs = binders.zip(holeIds.result()).map { case (binder, holeId) =>
      Projection.BinderInput(binder.name, binder.span, binder.mode, env(binder.localRef), holeId)
    }
    val compiled = Projection.compile(inputs, familyParams, span)

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
      binder.copy(ty = checkedTys(idx).residual, mode = result.mode, projection = result.projection)
    }

    CheckedBinders(checkedBinders, env)
  }

  def instantiateFull(binders: Vector[CoreAst.Binder], baseEnv: Env, args: Vector[Value]): Env = {
    if (binders.length != args.length) fail(ArityMismatch(binders.length, args.length, ArityMismatch.Arguments))

    baseEnv.bindLocals(binders, args)(_.localRef)
  }

  /** Runtime counterpart to `instantiateFull`, using the checked Pi's precomputed local-slot layout. */
  private[raccoonlang] def instantiateFullRuntime(
      binders: Vector[CoreAst.Binder],
      layout: RuntimeSlotLayout,
      baseEnv: Env,
      args: Vector[Value]
  ): Env = {
    if (binders.length != args.length) fail(ArityMismatch(binders.length, args.length, ArityMismatch.Arguments))
    if (layout.size != binders.length) wtf("Runtime Pi slot layout has inconsistent arity")
    baseEnv.bindRuntimeLocals(layout, args)
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
    FreshenedBinder(canonical, Option.when(!Sorts.isProposition(expectedTy))(id))
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
