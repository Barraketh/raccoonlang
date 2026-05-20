package com.raccoonlang.telescope

import com.raccoonlang.Value.{ConstructorHead, VBinder, VCtor, VPi}
import com.raccoonlang._

object ConstructorOps {
  final case class FreshCtorSpine(head: ConstructorHead, args: Vector[Value], tpe: Value) {
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
        ValueOps.materialize(tpe, eqStore)
      )
  }

  final case class ConstructorShape private[telescope] (
      private[telescope] val head: ConstructorHead,
      private[telescope] val pi: VPi
  ) {
    private[telescope] val erasedCount: Int = head.numErased

    def fieldBinders: Vector[VBinder] = pi.binders.drop(erasedCount)

    def makeCtor(allArgs: Vector[Value], resultTy: Value): VCtor = VCtor(head, allArgs, resultTy)

    def freshSpine(allArgs: Vector[Value], resultTy: Value): FreshCtorSpine = FreshCtorSpine(head, allArgs, resultTy)

    def projectedFieldType(
        base: Value,
        baseType: Value,
        fieldIdx: Int,
        locationId: AstNodeId,
        normalizerMap: Normalizers.NormalizerMap
    )(implicit eqStore: EqStore): Value = {
      val fresh = ConstructorOps.freshSpine(head)
      val erasedDeps = fresh.args.take(erasedCount).foldLeft(DepSet.empty) { case (deps, arg) =>
        deps ++ arg.synDeps
      }
      val refined = ValueEquivalence.unify(fresh.tpe, baseType, eqStore.allow(erasedDeps), normalizerMap)
      val refinedFresh = fresh.materialize(refined)

      var ctorEnv = pi.env
      pi.binders.take(erasedCount).zip(refinedFresh.args.take(erasedCount)).foreach { case (binder, arg) =>
        ctorEnv = TypePatternOps.bindValue(ctorEnv, binder, arg)
      }

      fieldBinders.take(fieldIdx).foreach { binder =>
        val (previousFieldTy, _) = TypePatternOps.openBinderType(ctorEnv, binder.ty)
        val previousField = Interpreter.evalSelect(base, binder.name, locationId, previousFieldTy)
        ctorEnv = TypePatternOps.bindValue(ctorEnv, binder, previousField)
      }

      TypePatternOps.openBinderType(ctorEnv, fieldBinders(fieldIdx).ty)._1
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
        shape.freshSpine(args, shape.pi.codomain(fresh, eqStore))

      case None => FreshCtorSpine(head, Vector.empty, head.tpe)
    }
}
