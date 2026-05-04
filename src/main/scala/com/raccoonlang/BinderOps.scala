package com.raccoonlang

import com.raccoonlang.CoreAst.Binder
import com.raccoonlang.Value.{VBinder, VPi}

object BinderOps {
  import com.raccoonlang.Util.NEL

  import scala.collection.immutable.BitSet

  final case class Freshened(vars: Vector[Value], env: Env, newVars: BitSet)
  final case class FreshenedRawBinders(vars: Vector[Value], env: Env, newVars: BitSet, vBinders: Vector[VBinder])

  def freshen(binders: NEL[VBinder], baseEnv: Env)(implicit eqStore: EqStore): Freshened = {
    val vars = Vector.newBuilder[Value]
    var env = baseEnv.newScope
    var newVars = BitSet.empty

    binders.foreach { binder =>
      val fresh = TypePatternOps.freshenBinder(env, binder)
      vars += fresh.value
      env = fresh.env.putLocal(binder.name, fresh.value)
      newVars ++= fresh.newVars
    }

    Freshened(vars.result(), env, newVars)
  }

  def freshen(binders: Vector[VBinder], baseEnv: Env)(implicit eqStore: EqStore): Freshened =
    if (binders.isEmpty) Freshened(Vector.empty, baseEnv, BitSet.empty)
    else freshen(NEL.mk(binders), baseEnv)

  def freshen(vpi: VPi)(implicit eqStore: EqStore): Freshened = freshen(vpi.binders, vpi.env)

  def freshenRawBinders(binders: NEL[Binder], baseEnv: Env, evalTypeTerm: (CoreAst.TypeTerm, Env) => Value)(implicit
      eqStore: EqStore
  ): FreshenedRawBinders = {
    val vars = Vector.newBuilder[Value]
    val vBinders = Vector.newBuilder[VBinder]
    var env = baseEnv.newScope
    var newVars = BitSet.empty

    binders.foreach { binder =>
      val fresh = TypePatternOps.freshenRawBinder(env, binder, evalTypeTerm)
      vars += fresh.value
      env = fresh.env.putLocal(binder.name, fresh.value)
      newVars ++= fresh.newVars
      vBinders += fresh.binder
    }

    FreshenedRawBinders(vars.result(), env, newVars, vBinders.result())
  }

  def freshenRawBinders(binders: Vector[Binder], baseEnv: Env, evalTypeTerm: (CoreAst.TypeTerm, Env) => Value)(implicit
      eqStore: EqStore
  ): FreshenedRawBinders =
    if (binders.isEmpty) FreshenedRawBinders(Vector.empty, baseEnv, BitSet.empty, Vector.empty)
    else freshenRawBinders(NEL.mk(binders), baseEnv, evalTypeTerm)

  def freshenRawBindersAndCheck(binders: Vector[Binder], env: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): FreshenedRawBinders =
    freshenRawBinders(binders, env, (tt, env) => TypeChecker.evalTypeTerm(tt, env))

  def instantiate(binders: NEL[VBinder], baseEnv: Env, args: NEL[Value])(implicit eqStore: EqStore): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.toList.zip(args.toList).foldLeft(baseEnv.newScope) { case (curEnv, (binder, value)) =>
      TypePatternOps.bindValue(curEnv, binder, value)
    }
  }

  def checkAndInstantiate(binders: NEL[VBinder], baseEnv: Env, args: NEL[Value])(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Env = {
    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

    binders.toList.zip(args.toList).foldLeft(baseEnv.newScope) { case (curEnv, (binder, value)) =>
      TypePatternOps.bindValueAndCheck(curEnv, binder, value)
    }
  }
}
