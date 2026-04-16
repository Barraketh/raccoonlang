package com.raccoonlang

import com.raccoonlang.Util.NEL
import com.raccoonlang.Value.{ConstructorHead, VCtor, VPi}

import scala.collection.immutable.BitSet

object ConstructorOps {
  final case class Instantiation(head: ConstructorHead, fieldArgs: Vector[Value], resultTy: Value) {
    val value: VCtor = VCtor(head, fieldArgs, resultTy)
  }

  def fromAppliedArgs(head: ConstructorHead, allArgs: Vector[Value], resultTy: Value): Instantiation =
    Instantiation(head, allArgs.drop(head.numParams), resultTy)

  def instantiateParams(pi: VPi, numParams: Int, paramArgs: Vector[Value], eqStore: EqStore): Env = {
    if (paramArgs.length != numParams) throw ArityMismatch(numParams, paramArgs.length)
    if (numParams == 0) pi.env
    else BinderOps.instantiate(pi.binders.take(numParams), pi.env, NEL.mk(paramArgs), eqStore)
  }

  def fieldBinders(pi: VPi, numParams: Int): Vector[CoreAst.Binder] =
    pi.binders.toList.drop(numParams).toVector

  def freshFields(
      pi: VPi,
      numParams: Int,
      envWithParams: Env,
      eqStore: EqStore
  ): BinderOps.Freshened =
    freshFieldPrefix(pi, numParams, envWithParams, fieldBinders(pi, numParams).length, eqStore)

  def freshFieldPrefix(
      pi: VPi,
      numParams: Int,
      envWithParams: Env,
      fieldCount: Int,
      eqStore: EqStore
  ): BinderOps.Freshened = {
    val binders = fieldBinders(pi, numParams).take(fieldCount)
    if (binders.isEmpty) BinderOps.Freshened(Vector.empty, envWithParams, BitSet.empty)
    else BinderOps.freshen(NEL.mk(binders), envWithParams, eqStore)
  }

  def fromFreshFields(
      head: ConstructorHead,
      pi: VPi,
      freshFields: BinderOps.Freshened,
      eqStore: EqStore
  ): Instantiation =
    Instantiation(head, freshFields.vars, pi.codomain(freshFields.env, eqStore))

  def freshFieldsFromParams(head: ConstructorHead, paramArgs: Vector[Value], eqStore: EqStore): Instantiation =
    head.tpe match {
      case pi: VPi =>
        val envWithParams = instantiateParams(pi, head.numParams, paramArgs, eqStore)
        fromFreshFields(head, pi, freshFields(pi, head.numParams, envWithParams, eqStore), eqStore)

      case otherTy => Instantiation(head, Vector.empty, otherTy)
    }

  def freshAllArgs(head: ConstructorHead, eqStore: EqStore)(implicit normalizers: NormalizerMap): Instantiation =
    head.tpe match {
      case pi: VPi =>
        val (freshArgs, ctorEnv, _) = BinderOps.assignFreshVarsAndCheck(pi, eqStore)
        Instantiation(head, freshArgs.drop(head.numParams).map(v => v: Value), pi.codomain(ctorEnv, eqStore))

      case otherTy => Instantiation(head, Vector.empty, otherTy)
    }
}
