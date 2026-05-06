package com.raccoonlang

import com.raccoonlang.CoreAst.Binder
import com.raccoonlang.Value.{VBinder, VPi}

object BinderOps {
  import com.raccoonlang.Util.NEL

  final case class Freshened(vars: Vector[Value], env: Env, newVars: DepSet)
  final case class FreshenedRawBinders(vars: Vector[Value], env: Env, newVars: DepSet, vBinders: Vector[VBinder])
  final case class CheckedArg(value: Value, term: ElabAst.Term)
  final case class CompletedArgs(env: Env, values: Vector[Value], terms: Vector[ElabAst.Term])

  private def putBinderLocal(env: Env, binder: VBinder, value: Value)(implicit eqStore: EqStore): Env = {
    val instanceKey =
      if (binder.isInstance || binder.isDerived) Some(InstanceSearch.instanceKey(binder.name, value, eqStore))
      else None
    env.putLocal(binder.localRef, value, instanceKey)
  }

  def freshen(binders: NEL[VBinder], baseEnv: Env)(implicit eqStore: EqStore): Freshened = {
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

  def freshen(binders: Vector[VBinder], baseEnv: Env)(implicit eqStore: EqStore): Freshened =
    if (binders.isEmpty) Freshened(Vector.empty, baseEnv, DepSet.empty)
    else freshen(NEL.mk(binders), baseEnv)

  def freshen(vpi: VPi)(implicit eqStore: EqStore): Freshened = freshen(vpi.binders, vpi.env)

  def freshenRawBinders(binders: NEL[Binder], baseEnv: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): FreshenedRawBinders = {
    val vars = Vector.newBuilder[Value]
    val vBinders = Vector.newBuilder[VBinder]
    var env = baseEnv
    val newVars = DepSet.newBuilder

    binders.foreach { binder =>
      val fresh = TypePatternOps.freshenRawBinder(env, binder)
      vars += fresh.value
      env = putBinderLocal(fresh.env, fresh.binder, fresh.value)
      newVars.unionInPlace(fresh.newVars)
      vBinders += fresh.binder
    }

    FreshenedRawBinders(vars.result(), env, newVars.result(), vBinders.result())
  }

  def freshenRawBinders(binders: Vector[Binder], baseEnv: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): FreshenedRawBinders =
    if (binders.isEmpty) FreshenedRawBinders(Vector.empty, baseEnv, DepSet.empty, Vector.empty)
    else freshenRawBinders(NEL.mk(binders), baseEnv)

  def freshenRawBindersAndCheck(binders: Vector[Binder], env: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): FreshenedRawBinders = freshenRawBinders(binders, env)

  def instantiateFull(binders: NEL[VBinder], baseEnv: Env, args: NEL[Value])(implicit eqStore: EqStore): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.toList.zip(args.toList).foldLeft(baseEnv) { case (curEnv, (binder, value)) =>
      TypePatternOps.bindValue(curEnv, binder, value)
    }
  }

  def checkAndInstantiateFull(binders: NEL[VBinder], baseEnv: Env, args: Vector[Value])(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.toVector.zip(args).foldLeft(baseEnv) { case (curEnv, (binder, value)) =>
      TypePatternOps.bindValueAndCheck(curEnv, binder, value)
    }
  }

  def checkAndInstantiate(binders: NEL[VBinder], baseEnv: Env, args: Vector[CheckedArg], searchEnv: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): CompletedArgs =
    complete(binders, baseEnv, args, searchEnv)

  private def complete(binders: NEL[VBinder], baseEnv: Env, args: Vector[CheckedArg], searchEnv: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): CompletedArgs = {
    var argIdx = 0
    var telescopeEnv = baseEnv
    val values = Vector.newBuilder[Value]
    val terms = Vector.newBuilder[ElabAst.Term]

    val binderV = binders.toVector
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

  def solveBinder(env: Env, binder: VBinder, searchEnv: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): BinderOps.CheckedArg = {
    val goal = TypePatternOps.expectedType(env, binder)
    InstanceSearch.solve(goal, searchEnv)
  }
}
