package com.raccoonlang

import com.raccoonlang.Util.NEL
import com.raccoonlang.Value.{ConstructorHead, VBinder, VCtor, VPi}

object ConstructorOps {
  final case class FreshCtor(value: VCtor, newVars: DepSet)

  final case class ConstructorShape(head: ConstructorHead, pi: VPi) {
    val paramCount: Int = head.numParams

    def paramBinders: Vector[VBinder] = pi.binders.toVector.take(paramCount)
    def fieldBinders: Vector[VBinder] = pi.binders.toVector.drop(paramCount)

    def paramArgs[A](args: Vector[A]): Vector[A] = args.take(paramCount)
    def isParamIndex(idx: Int): Boolean = idx < paramCount

    def instantiateParams(paramArgs: Vector[Value])(implicit eqStore: EqStore): Env = {
      if (paramArgs.length != paramCount) throw ArityMismatch(paramCount, paramArgs.length)
      if (paramCount == 0) pi.env
      else BinderOps.instantiate(NEL.mk(paramBinders), pi.env, NEL.mk(paramArgs))
    }

    def makeCtor(allArgs: Vector[Value], resultTy: Value): VCtor = VCtor(head, allArgs.drop(paramCount), resultTy)
  }

  object ConstructorShape {
    def from(head: ConstructorHead): Option[ConstructorShape] =
      head.tpe match {
        case pi: VPi => Some(ConstructorShape(head, pi))
        case _       => None
      }

    def require(head: ConstructorHead): ConstructorShape = from(head).getOrElse(throw CannotApplyNonFunction(head.tpe))
  }

  def freshFromParams(head: ConstructorHead, paramArgs: Vector[Value])(implicit eqStore: EqStore): FreshCtor =
    ConstructorShape.from(head) match {
      case Some(shape) =>
        val envWithParams = shape.instantiateParams(paramArgs)
        val fields = shape.fieldBinders
        val fresh = freshFieldPrefix(fields, envWithParams, fields.length)
        FreshCtor(VCtor(head, fresh.vars, shape.pi.codomain(fresh.env, eqStore)), fresh.newVars)

      case None => FreshCtor(VCtor(head, Vector.empty, head.tpe), DepSet.empty)
    }

  def freshAll(head: ConstructorHead)(implicit eqStore: EqStore): VCtor =
    ConstructorShape.from(head) match {
      case Some(shape) =>
        val fresh = BinderOps.freshen(shape.pi)
        shape.makeCtor(fresh.vars.map(v => v: Value), shape.pi.codomain(fresh.env, eqStore))

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

        val fieldRef = allFieldBinders(fieldIdx).localRef.getOrElse(throw NotFound(field))
        freshFieldPrefix(allFieldBinders, envWithParams, fieldIdx + 1).env(fieldRef).tpe

      case None => throw NotFound(field)
    }
  }

  // Starting from an environment where constructor parameters are already bound, allocate fresh values for the first
  // fieldCount field binders so later field types can refer to earlier fields.
  private def freshFieldPrefix(fieldBinders: Vector[VBinder], envWithParams: Env, fieldCount: Int)(implicit
      eqStore: EqStore
  ): BinderOps.Freshened = {
    val binders = fieldBinders.take(fieldCount)
    if (binders.isEmpty) BinderOps.Freshened(Vector.empty, envWithParams, DepSet.empty)
    else BinderOps.freshen(NEL.mk(binders), envWithParams)
  }
}
