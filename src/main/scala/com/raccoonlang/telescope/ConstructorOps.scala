package com.raccoonlang.telescope

import com.raccoonlang.Value.{ConstructorHead, VBinder, VCtor, VPi}
import com.raccoonlang._

object ConstructorOps {
  final case class FreshCtorSpine(head: ConstructorHead, args: Vector[Value], tpe: Value, env: RuntimeEnv) {
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

    def freshSpine(allArgs: Vector[Value], resultTy: Value, env: RuntimeEnv): FreshCtorSpine =
      FreshCtorSpine(head, allArgs, resultTy, env)

    def projectedFieldType(
        base: Value,
        baseType: Value,
        fieldIdx: Int,
        locationId: AstNodeId,
        normalizerMap: Normalizers.NormalizerMap
    )(implicit eqStore: EqStore): Value = {
      val fresh = ConstructorOps.freshSpine(head)
      val refined = ValueEquivalence.unify(fresh.tpe, baseType, eqStore.allow(fresh.tpe.synDeps), normalizerMap)
      val refinedFresh = fresh.materialize(refined)

      def bindRefinedCaptures(env: RuntimeEnv, binder: VBinder): RuntimeEnv =
        binder.captures.foldLeft(env) { case (curEnv, capture) =>
          curEnv.putLocal(capture.localRef, refinedFresh.env(capture.localRef))
        }

      var ctorEnv = pi.env
      pi.binders.take(erasedCount).zip(refinedFresh.args.take(erasedCount)).foreach { case (binder, arg) =>
        ctorEnv = TypePatternOps.bindValue(ctorEnv, binder, arg)
      }

      fieldBinders.take(fieldIdx).foreach { binder =>
        val previousFieldEnv = bindRefinedCaptures(ctorEnv, binder)
        val previousFieldTy = Interpreter.evalTypeTerm(binder.expectedTy, previousFieldEnv)
        val previousField = Interpreter.evalSelect(base, binder.name, locationId, previousFieldTy)
        ctorEnv = previousFieldEnv.putLocal(binder.localRef, previousField)
      }

      val fieldEnv = bindRefinedCaptures(ctorEnv, fieldBinders(fieldIdx))
      Interpreter.evalTypeTerm(fieldBinders(fieldIdx).expectedTy, fieldEnv)
    }
  }

  object ConstructorShape {
    private[telescope] def from(head: ConstructorHead): Option[ConstructorShape] =
      head.tpe match {
        case pi: VPi => Some(ConstructorShape(head, pi))
        case _       => None
      }

    def require(head: ConstructorHead): ConstructorShape = from(head).getOrElse(throw CannotApplyNonFunction(head.tpe))
  }

  def freshSpine(head: ConstructorHead)(implicit eqStore: EqStore): FreshCtorSpine =
    ConstructorShape.from(head) match {
      case Some(shape) =>
        val fresh = BinderOps.freshen(shape.pi)
        val args = shape.pi.binders.map(binder => fresh(binder.localRef))
        shape.freshSpine(args, shape.pi.codomain(fresh, eqStore), fresh)

      case None => FreshCtorSpine(head, Vector.empty, head.tpe, RuntimeEnv(Map.empty, Vector.empty))
    }
}
