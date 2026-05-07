package com.raccoonlang.telescope

import com.raccoonlang.Value.{VBinder, VPi}
import com.raccoonlang._

object BinderOps {
  final case class Freshened(vars: Vector[Value], env: Env, newVars: DepSet)
  final case class FreshenedRawBinders(
      vars: Vector[Value],
      env: Env,
      newVars: DepSet,
      vBinders: Vector[VBinder],
      checkedBinders: Vector[CoreAst.CheckedBinder]
  )
  final case class CheckedArg(value: Value, term: CoreAst.CheckedTerm)
  final case class CompletedArgs(env: Env, values: Vector[Value], terms: Vector[CoreAst.CheckedTerm])

  private def putBinderLocal(env: Env, binder: VBinder, value: Value)(implicit eqStore: EqStore): Env = {
    val instanceKey =
      if (binder.isInstance) Some(InstanceSearch.instanceKey(binder.name, value, eqStore))
      else None
    env.putLocal(binder.localRef, value, instanceKey)
  }

  def freshen(binders: Vector[VBinder], baseEnv: Env)(implicit eqStore: EqStore): Freshened = {
    if (binders.isEmpty) return Freshened(Vector.empty, baseEnv, DepSet.empty)

    val vars = Vector.newBuilder[Value]
    var env = baseEnv
    val newVars = DepSet.newBuilder

    binders.foreach { binder =>
      val fresh = TypePatternOps.freshenBinder(env, binder)
      vars += fresh.value
      env = putBinderLocal(fresh.env, binder, fresh.value)
      newVars.unionInPlace(fresh.newVars)
    }

    Freshened(vars.result(), env, newVars.result())
  }

  def freshen(vpi: VPi)(implicit eqStore: EqStore): Freshened = freshen(vpi.binders, vpi.env)

  def freshenRawBinders(binders: Vector[CoreAst.RawBinder], baseEnv: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): FreshenedRawBinders = {
    if (binders.isEmpty)
      return FreshenedRawBinders(Vector.empty, baseEnv, DepSet.empty, Vector.empty, Vector.empty)

    val vars = Vector.newBuilder[Value]
    val vBinders = Vector.newBuilder[VBinder]
    val checkedBinders = Vector.newBuilder[CoreAst.CheckedBinder]
    var env = baseEnv
    val newVars = DepSet.newBuilder

    binders.foreach { binder =>
      val fresh = TypePatternOps.freshenRawBinder(env, binder)
      vars += fresh.value
      env = putBinderLocal(fresh.env, fresh.binder, fresh.value)
      newVars.unionInPlace(fresh.newVars)
      vBinders += fresh.binder
      checkedBinders += fresh.checkedBinder
    }

    FreshenedRawBinders(vars.result(), env, newVars.result(), vBinders.result(), checkedBinders.result())
  }

  def instantiateFull(binders: Vector[VBinder], baseEnv: Env, args: Vector[Value])(implicit eqStore: EqStore): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(baseEnv) { case (curEnv, (binder, value)) =>
      TypePatternOps.bindValue(curEnv, binder, value)
    }
  }

  def checkAndInstantiateFull(binders: Vector[VBinder], baseEnv: Env, args: Vector[Value])(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.zip(args).foldLeft(baseEnv) { case (curEnv, (binder, value)) =>
      TypePatternOps.bindValueAndCheck(curEnv, binder, value)
    }
  }

  def checkAndInstantiate(binders: Vector[VBinder], baseEnv: Env, args: Vector[CheckedArg], searchEnv: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): CompletedArgs = {
    var argIdx = 0
    var telescopeEnv = baseEnv
    val values = Vector.newBuilder[Value]
    val terms = Vector.newBuilder[CoreAst.CheckedTerm]

    val binderV = binders
    val explicitArgCount = binderV.count(!_.isDerived)

    binderV.foreach { binder =>
      val arg =
        if (binder.isDerived) {
          solveBinder(telescopeEnv, binder, searchEnv)
        } else {
          if (argIdx >= args.length) throw ArityMismatch(explicitArgCount, args.length)
          val next = args(argIdx)
          argIdx += 1
          next
        }

      val nextTelescope = TypePatternOps.bindValueAndCheck(telescopeEnv, binder, arg.value, Some(arg.term))

      telescopeEnv = nextTelescope
      values += arg.value
      terms += arg.term
    }

    if (argIdx != args.length) throw ArityMismatch(explicitArgCount, args.length)
    CompletedArgs(telescopeEnv, values.result(), terms.result())
  }

  private[telescope] def solveBinder(env: Env, binder: VBinder, searchEnv: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): BinderOps.CheckedArg = {
    if (binder.isDerived && binder.captures.nonEmpty) throw CannotDirectlyApplyCapturedDerivedBinder(binder.name)

    val goal = Interpreter.evalTypeTerm(binder.expectedTy, env)
    InstanceSearch.solve(goal, searchEnv)
  }
}
