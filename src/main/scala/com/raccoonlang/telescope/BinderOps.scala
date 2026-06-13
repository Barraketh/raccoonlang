package com.raccoonlang.telescope

import com.raccoonlang.Value.{VBinder, VPi}
import com.raccoonlang._

object BinderOps {
  def freshen(binders: Vector[VBinder], baseEnv: Env): Env = {
    var env = baseEnv
    binders.foreach { binder =>
      env = TypePatternOps.freshenBinder(env, binder)
    }

    env
  }

  def freshen(vpi: VPi): Env = freshen(vpi.binders, vpi.env)

  def toVBinders(binders: Vector[CoreAst.Binder], baseEnv: Env): (Vector[VBinder], Vector[ElabAst.Binder]) = {
    val vBinders = Vector.newBuilder[VBinder]
    val checkedBinders = Vector.newBuilder[ElabAst.Binder]
    var env = baseEnv

    binders.foreach { binder =>
      val (vBinder, checkedBinder) = TypePatternOps.toVBinder(binder, env)
      vBinders += vBinder
      checkedBinders += checkedBinder
      env = freshen(Vector(vBinder), env)
    }

    (vBinders.result(), checkedBinders.result())
  }

  def instantiateFull(binders: Vector[VBinder], baseEnv: Env, args: Vector[Value], argEnv: Env): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    try
      binders.zip(args).foldLeft(baseEnv) { case (curEnv, (binder, value)) =>
        TypePatternOps.bindValue(curEnv, binder, value, argEnv)
      }
    catch {
      case _: PatternCaptureEscapesScope | _: PatternCaptureNeedsExpectedType =>
        solveTelescope(binders, baseEnv, args, check = false, baseEnv.normalizers)
    }
  }

  def checkAndInstantiate(
      binders: Vector[VBinder],
      runtimeEnv: Env,
      args: Vector[Value],
      argEnv: Env,
      normalizerMap: Normalizers.NormalizerMap
  ): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    try
      binders.zip(args).foldLeft(runtimeEnv) { case (curRuntimeEnv, (binder, value)) =>
        TypePatternOps.bindValueAndCheck(curRuntimeEnv, binder, value, argEnv, normalizerMap)
      }
    catch {
      case _: PatternCaptureEscapesScope | _: PatternCaptureNeedsExpectedType =>
        solveTelescope(binders, runtimeEnv, args, check = true, normalizerMap)
    }
  }

  /**
   * Application-scoped binding (docs/type-patterns.md section 6, rule A): the fallback when per-binder
   * matching underdetermines a capture. One unification store is threaded across the whole telescope, so
   * information may flow between binders in both directions — in particular a pattern-typed argument (a
   * polymorphic function) has its own pattern openings made refinable by the unifier's Pi rule and can be
   * instantiated by a later binder's constraint. Per-binder matching is the degenerate case of this
   * judgment where every binder's captures are determined by its own argument, so the fallback changes
   * nothing for programs the eager pass accepts; it only runs after that pass fails.
   *
   * The solved/closed checks (M2, against a watermark taken at the start of the application) and the
   * certificate (M3) run once at the end of the telescope. Binders are bound at their instantiated
   * expected types (M4): the ascription is taken at the opened pattern value and resolved by the final
   * materialization.
   */
  private def solveTelescope(
      binders: Vector[VBinder],
      baseEnv: Env,
      args: Vector[Value],
      check: Boolean,
      normalizerMap: Normalizers.NormalizerMap
  ): Env = {
    val watermark = FreshVar.currentId
    var store = EqStore.empty
    var env = baseEnv
    val flexBinders = Vector.newBuilder[(VBinder, TypePatternOps.OpenedBinderPattern, Value)]

    binders.zip(args).foreach { case (binder, value) =>
      val opened = TypePatternOps.openBinderPattern(env, binder)
      val expectedNow = ValueOps.materialize(opened.value, store)
      if (binder.captures.isEmpty && !expectedNow.synDeps.intersects(store.refinable)) {
        // No flexibility at this binder: the ordinary checking discipline (cumulativity, §7 instantiation).
        if (check) TypeChecker.checkType(value, expectedNow, normalizerMap)
        val bound = if (check) Value.ascribe(value, expectedNow) else value
        env = opened.env.putLocal(binder.localRef, bound)
      } else {
        store =
          ValueEquivalence.tryUnify(opened.value, value.tpe, store.allow(opened.captureDeps), normalizerMap) match {
            case Right(next)         => next
            case Left((left, right)) => throw TypeMismatch(left, right)
          }
        env = opened.env.putLocal(binder.localRef, Value.ascribe(value, opened.value))
        flexBinders += ((binder, opened, value))
      }
    }

    val materializedEnv = ValueOps.materializeEnv(env, store)

    flexBinders.result().foreach { case (binder, opened, value) =>
      binder.captures.foreach { capture =>
        val before = opened.env(capture.localRef)
        val after = materializedEnv(capture.localRef)
        if (TypePatternOps.isUnsolvedCapture(before, after))
          throw PatternCaptureNeedsExpectedType(capture.localRef.name)
        val deps = after.synDeps
        if (deps.nonEmpty && deps.max > watermark)
          throw PatternCaptureEscapesScope(capture.localRef.name)
      }
      if (check) TypeChecker.checkType(value, ValueOps.materialize(opened.value, store), normalizerMap)
    }

    materializedEnv
  }
}
