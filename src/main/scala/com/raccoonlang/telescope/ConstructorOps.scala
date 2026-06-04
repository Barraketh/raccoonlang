package com.raccoonlang.telescope

import com.raccoonlang.Value.{ConstructorHead, VBinder, VCtor, VPi}
import com.raccoonlang._

object ConstructorOps {
  final case class FreshCtorSpine(head: ConstructorHead, args: Vector[Value], tpe: Value, env: Env) {
    def fields: Vector[Value] = args.drop(head.numErased)

    lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      args.foreach(arg => res.unionInPlace(arg.synDeps))
      res.unionInPlace(tpe.synDeps)
      res.result()
    }

    def value: VCtor = VCtor(head, args, tpe)

    def materialize(eqStore: EqStore): FreshCtorSpine =
      FreshCtorSpine(
        ValueOps.materialize(head, eqStore).asInstanceOf[ConstructorHead],
        args.map(arg => ValueOps.materialize(arg, eqStore)),
        ValueOps.materialize(tpe, eqStore),
        ValueOps.materializeEnv(env, eqStore)
      )
  }

  final case class ConstructorShape private[telescope] (
      private[telescope] val head: ConstructorHead,
      private[telescope] val pi: VPi
  ) {
    private[telescope] val erasedCount: Int = head.numErased

    def fieldBinders: Vector[VBinder] = pi.binders.drop(erasedCount)

    def makeCtor(allArgs: Vector[Value], resultTy: Value): VCtor = VCtor(head, allArgs, resultTy)

    def freshSpine(allArgs: Vector[Value], resultTy: Value, env: Env): FreshCtorSpine =
      FreshCtorSpine(head, allArgs, resultTy, env)
  }

  object ConstructorShape {
    private[telescope] def from(head: ConstructorHead): Option[ConstructorShape] =
      head.tpe match {
        case pi: VPi => Some(ConstructorShape(head, pi))
        case _       => None
      }

    def require(head: ConstructorHead): ConstructorShape = from(head).getOrElse(throw CannotApplyNonFunction(head.tpe))
  }

  def freshSpine(head: ConstructorHead): FreshCtorSpine =
    ConstructorShape.from(head) match {
      case Some(shape) =>
        val fresh = BinderOps.freshen(shape.pi)
        val args = shape.pi.binders.map(binder => fresh(binder.localRef))
        shape.freshSpine(args, shape.pi.codomain(fresh), fresh)

      case None => FreshCtorSpine(head, Vector.empty, head.tpe, Env.empty)
    }
}
