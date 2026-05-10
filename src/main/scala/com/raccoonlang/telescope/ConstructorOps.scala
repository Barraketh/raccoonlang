package com.raccoonlang.telescope

import com.raccoonlang.Value.{ConstructorHead, VBinder, VCtor, VPi}
import com.raccoonlang._

object ConstructorOps {
  final case class ConstructorShape private[telescope] (
      private[telescope] val head: ConstructorHead,
      private[telescope] val pi: VPi
  ) {
    private[telescope] val paramCount: Int = head.numParams

    private[telescope] def paramBinders: Vector[VBinder] = pi.binders.take(paramCount)
    def fieldBinders: Vector[VBinder] = pi.binders.drop(paramCount)

    private[telescope] def paramArgs[A](args: Vector[A]): Vector[A] = args.take(paramCount)
    private[telescope] def isParamIndex(idx: Int): Boolean = idx < paramCount

    private[telescope] def instantiateParams(paramArgs: Vector[Value])(implicit eqStore: EqStore): RuntimeEnv = {
      if (paramArgs.length != paramCount) throw ArityMismatch(paramCount, paramArgs.length)
      if (paramCount == 0) pi.env
      else BinderOps.instantiateFull(paramBinders, pi.env, paramArgs)
    }

    def makeCtor(allArgs: Vector[Value], resultTy: Value): VCtor = VCtor(head, allArgs.drop(paramCount), resultTy)
  }

  object ConstructorShape {
    private[telescope] def from(head: ConstructorHead): Option[ConstructorShape] =
      head.tpe match {
        case pi: VPi => Some(ConstructorShape(head, pi))
        case _       => None
      }

    def require(head: ConstructorHead): ConstructorShape = from(head).getOrElse(throw CannotApplyNonFunction(head.tpe))
  }

  def freshFromParams(head: ConstructorHead, paramArgs: Vector[Value])(implicit eqStore: EqStore): VCtor =
    ConstructorShape.from(head) match {
      case Some(shape) =>
        val envWithParams = shape.instantiateParams(paramArgs)
        val fields = shape.fieldBinders
        val fresh = freshFieldPrefix(fields, envWithParams, fields.length)
        val fieldValues = fields.map(binder => fresh(binder.localRef))
        VCtor(head, fieldValues, shape.pi.codomain(fresh, eqStore))

      case None => VCtor(head, Vector.empty, head.tpe)
    }

  def freshAll(head: ConstructorHead)(implicit eqStore: EqStore): VCtor =
    ConstructorShape.from(head) match {
      case Some(shape) =>
        val fresh = BinderOps.freshen(shape.pi)
        val args = shape.pi.binders.map(binder => fresh(binder.localRef))
        shape.makeCtor(args, shape.pi.codomain(fresh, eqStore))

      case None => VCtor(head, Vector.empty, head.tpe)
    }

  def structFieldType(head: ConstructorHead, typeArgs: Vector[Value], field: String)(implicit
      eqStore: EqStore
  ): Value = {
    if (!head.isStruct) throw NotAStruct(head.name)

    ConstructorShape.from(head) match {
      case Some(shape) =>
        val envWithParams = shape.instantiateParams(shape.paramArgs(typeArgs))
        val allFieldBinders = shape.fieldBinders
        val fieldIdx = allFieldBinders.indexWhere(_.name == field)
        if (fieldIdx < 0) throw NotFound(field)

        val fieldRef = allFieldBinders(fieldIdx).localRef
        val envWithFields = freshFieldPrefix(allFieldBinders, envWithParams, fieldIdx + 1)
        envWithFields(fieldRef).tpe

      case None => throw NotFound(field)
    }
  }

  // Starting from an environment where constructor parameters are already bound, allocate fresh values for the first
  // fieldCount field binders so later field types can refer to earlier fields.
  private def freshFieldPrefix(
      fieldBinders: Vector[VBinder],
      envWithParams: RuntimeEnv,
      fieldCount: Int
  )(implicit eqStore: EqStore): RuntimeEnv = {
    val binders = fieldBinders.take(fieldCount)
    BinderOps.freshen(binders, envWithParams)
  }
}
