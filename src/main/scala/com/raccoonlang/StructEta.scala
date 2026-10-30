package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.{ElabAst => EA}

/**
 * Structure eta (docs/kernel.md, "Structure eta and projections"), as a rule, not a representation. A family is
 * eligible when it has one constructor, no indices and no recursive field, and is not in `Prop`; its kind and level do
 * not matter, so linear families are eligible too. At an eligible type a value is definitionally its constructor applied
 * to its fields. The eta view of such a value is its stored fields when it is constructor-headed, and its field
 * projections otherwise; match evaluation, conversion, unification and structural descent all read that one view.
 *
 * A projection is the stuck evaluation of a canonical one-branch match, `match self returning motive with | mk x0 … xn
 * => xi`, with one match node per field of the family, so two projections of one field of convertible values convert by
 * identity. Its motive is the field's type at the projected value.
 */
object StructEta {

  /**
   * The name of the record a projector or a generated selector projects: no source identifier starts with `_`, so a
   * one-branch match on a local of this name is a projection, which `PrettyPrinter` prints as `base.field`.
   */
  val SelfName = "__self"

  /** The projector's locals: the projected value, the field's type, then the constructor's fields. */
  private val SelfRef = CoreAst.LocalRef(0, SelfName)
  private val MotiveRef = CoreAst.LocalRef(1, "motive")
  private val NoSpan = Span(0, 0)

  /** The canonical projector of each stored field of a constructor, whose fields are named `fieldNames`. */
  def projectors(ctorName: String, fieldNames: Vector[String]): Vector[EA.Term.Match] = {
    val fieldCount = fieldNames.length
    val fieldRefs = Vector.tabulate(fieldCount)(i => CoreAst.LocalRef(2 + i, fieldNames(i)))
    Vector.tabulate(fieldCount) { idx =>
      EA.Term.Match(
        EA.Term.LocalRef(SelfRef, NoSpan),
        Some(EA.Term.LocalRef(MotiveRef, NoSpan)),
        Vector(EA.Case(ctorName, fieldRefs.map(Some(_)), EA.Term.LocalRef(fieldRefs(idx), NoSpan), NoSpan)),
        NoSpan,
        NodeId.fresh()
      )
    }
  }

  /** The eligible family instance behind `tpe`, with its eta information. */
  def eligible(tpe: Value): Option[(InductiveFamilyInstance, EtaInfo)] =
    tpe match {
      case InductiveFamilyValue(instance) => instance.meta.eta.map(info => (instance, info))
      case _                              => None
    }

  /** The eta view of `value`, when its type is eligible. A proof has none: proofs are irrelevant instead. */
  def fields(value: Value): Option[Vector[Value]] =
    eligible(value.tpe).collect {
      case (instance, info) if !isProof(value) =>
        value match {
          case ConstructorValue(head, stored) if head.name == info.ctorName => stored
          case _ => Vector.tabulate(info.fieldCount)(projection(value, instance, info, _))
        }
    }

  /**
   * A constructor-headed value and a value that is not, at one eligible type: the pairs of the one's stored fields and
   * the other's projections, which eta compares. `None` otherwise, including for two neutral values, which eta would
   * only compare by projections of each, and so by the values themselves.
   */
  def fieldPairs(a: Value, b: Value): Option[Vector[(Value, Value)]] = {
    val aCtor = ConstructorValue.unapply(a).isDefined
    if (aCtor == ConstructorValue.unapply(b).isDefined) None
    else
      for {
        left <- fields(a)
        right <- fields(b)
        if left.length == right.length
      } yield left.zip(right)
  }

  private def projection(base: Value, instance: InductiveFamilyInstance, info: EtaInfo, idx: Int): Value = {
    val motive = fieldType(base, instance, info, idx)
    val env = Env.empty.putLocal(SelfRef, base).putLocal(MotiveRef, motive)
    Interpreter.stuckMatch(info.projectors(idx), base, env, motive)
  }

  /**
   * The type of field `idx` at `base`: the template field's type, with the constructor's result unified with the
   * instance, which solves the template's witnesses of the family parameters, and the earlier fields linked to their
   * projections. The family is uniform in its parameters and has no indices, so the unification only links witnesses.
   */
  private def fieldType(base: Value, instance: InductiveFamilyInstance, info: EtaInfo, idx: Int): Value = {
    val start = EqStore.empty.allow(info.templateIds)
    val solved = info.resultArgs.zip(instance.args).foldLeft(start) { case (store, (template, arg)) =>
      ValueEquivalence.tryUnify(template, arg, store) match {
        case Right(next) => next
        case Left(_)     => throw WTF(s"${info.ctorName}'s result does not unify with $instance")
      }
    }
    val store = (0 until idx).foldLeft(solved) { (store, field) =>
      info.fieldVars(field) match {
        case Var(_, id, _) if !store.subst.contains(id) => store.addLink(id, projection(base, instance, info, field))
        case _                                          => store
      }
    }
    ValueOps.materialize(info.fieldVars(idx).tpe, store)
  }

  private def isProof(value: Value): Boolean =
    value.tpe.tpe == PropTpe
}
