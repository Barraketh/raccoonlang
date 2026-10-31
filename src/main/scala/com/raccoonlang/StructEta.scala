package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{ElabAst => EA}

/**
 * Records, their projections and structure eta (docs/kernel.md, "Structure eta and projections"). A record is a family
 * with one constructor (`RecordInfo`). A projection of one of its fields is the stuck evaluation of a canonical
 * one-branch match, `match self returning motive with | mk x0 … xn => xi`, with one match node per field of the family,
 * so two projections of one field of convertible values convert by identity. Its motive is the field's type at the
 * projected value. On a constructor value a projection is the stored field.
 *
 * Eta is a rule, not a representation. A record is eligible when it also has no indices and no recursive field, is not
 * in `Prop`, and the family's arguments determine every field's type (`RecordInfo.eta`); its kind and level do not
 * matter, so linear records are eligible too. At an eligible type a value is definitionally its constructor applied to
 * its fields. The eta view of such a value is its stored fields when it is constructor-headed, and its field
 * projections otherwise; match evaluation, conversion, unification and structural descent all read that one view.
 */
object StructEta {

  /** The name of the local a projector projects, which no source identifier has, as none starts with `_`. */
  private val SelfName = "__self"

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

  /**
   * A constructor's telescope opened on fresh variables (`templateIds`, its binders' and its type-pattern captures'):
   * its result, a family instance, its stored fields (`fieldVars`), whose types state each field's type in terms of the
   * binders, the captures and the earlier fields, and its captures. A record keeps its constructor's, opened once, as
   * its template (`RecordInfo.template`).
   */
  final case class Template(result: Value, fieldVars: Vector[Value], captures: Vector[Value], templateIds: DepSet) {
    def resultArgs: Vector[Value] =
      result match {
        case ConstSpine(_, args) => args
        case other               => throw WTF(s"A constructor's result $other is not a family instance")
      }

    /**
     * The result unified with `args`, the leading arguments of a family instance, one argument at a time: one that does
     * not unify, such as an index whose equation is stuck, leaves the variables it would solve fresh.
     */
    def solve(args: Vector[Value]): EqStore =
      resultArgs.zip(args).foldLeft(EqStore.empty.allow(templateIds)) { case (store, (resultArg, arg)) =>
        ValueEquivalence.tryUnify(resultArg, arg, store).getOrElse(store)
      }

    /** The type of stored field `idx` in `store`, in terms of the variables `store` leaves fresh. */
    def fieldType(idx: Int, store: EqStore): Value = ValueOps.materialize(fieldVars(idx).tpe, store)
  }

  /** The telescope of the constructor `ctor`, opened on fresh variables. */
  private[raccoonlang] def template(ctor: ConstructorHead): Template =
    ctor.tpe match {
      case pi: VPi =>
        val fresh = BinderOps.freshen(pi)
        val opened = pi.binders.map(binder => fresh(binder.localRef))
        val captured = pi.binders.flatMap(_.captures).map(capture => fresh(capture.localRef))
        val ids = DepSet.from((opened ++ captured).collect { case Var(_, id, _) => id })
        Template(pi.codomain(fresh), opened.drop(ctor.numErased), captured, ids)
      // A constructor without binders belongs to a family without parameters.
      case result => Template(result, Vector.empty, Vector.empty, DepSet.empty)
    }

  /**
   * Whether the arguments of a family of type `familyType` determine every field's type in `template`: its result
   * unifies with fresh arguments, and no field's type then depends on a variable of the template other than the earlier
   * fields. A field whose type depends on a capture that no argument determines is a hidden dependency, such as `$n` in
   * `(v: Vec(A, $n))`; its eta projection would have no type.
   */
  private[raccoonlang] def determined(template: Template, familyType: Value): Boolean = {
    val args = familyType match {
      case pi: VPi =>
        val fresh = BinderOps.freshen(pi)
        pi.binders.map(binder => fresh(binder.localRef))
      case _ => Vector.empty
    }
    val solved =
      template.resultArgs.zip(args).foldLeft[Option[EqStore]](Some(EqStore.empty.allow(template.templateIds))) {
        case (store, (resultArg, arg)) => store.flatMap(s => ValueEquivalence.tryUnify(resultArg, arg, s).toOption)
      }
    // The arguments are fresh, so a variable of the template that remains in a field's type is one they leave unsolved.
    solved.exists { store =>
      template.fieldVars.indices.forall { idx =>
        val earlier = DepSet.from(template.fieldVars.take(idx).collect { case Var(_, id, _) => id })
        val deps = template.fieldType(idx, store).synDeps
        ((deps & template.templateIds) -- earlier).isEmpty
      }
    }
  }

  /** The eligible family instance behind `tpe`, with its record. */
  def eligible(tpe: Value): Option[(InductiveFamilyInstance, RecordInfo)] =
    tpe match {
      case InductiveFamilyValue(instance) => instance.meta.record.filter(_.eta).map(info => (instance, info))
      case _                              => None
    }

  /** The eta view of `value`, when its type is eligible. A proof has none: proofs are irrelevant instead. */
  def fields(value: Value): Option[Vector[Value]] =
    eligible(value.tpe).collect {
      case (instance, info) if !isProof(value) =>
        value match {
          case ConstructorValue(_, stored) => stored
          case _                           => projections(value, instance, info, info.fieldCount)
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

  /**
   * Field `idx` of `base`, a value of a record: its stored field when it is constructor-headed, and otherwise its
   * canonical projection, read off its type, the record's instance. A checked projection evaluates so.
   */
  def project(base: Value, idx: Int): Value =
    base match {
      case ConstructorValue(_, stored) => stored(idx)
      case _ =>
        base.tpe match {
          case InductiveFamilyValue(instance) if instance.meta.record.isDefined =>
            projections(base, instance, instance.meta.record.get, idx + 1)(idx)
          case other => throw WTF(s"Projected $base of type $other, which is no record")
        }
    }

  /**
   * The canonical projections of fields `0 until count` of `base`, a value of `instance` that is not
   * constructor-headed. Each is typed in one store, built along: the template's result solved at the instance
   * (`Template.solve`), with each earlier field's variable that leaves fresh linked to that field's projection. So a
   * projection's motive, its field's type, holds the projections of the earlier fields that type depends on.
   *
   * An argument that does unify states what every constructor value of the instance satisfies, so each type is the
   * field's at every value `base` can be. At an eligible type the result unifies with fresh arguments (`determined`),
   * so with every instance's, and every field's type is the template's at them. Otherwise a variable of the template
   * may remain, a capture no argument determines, and then the field has no projection at `instance` (`undetermined`),
   * which the checker asks of every projection it checks.
   */
  private def projections(
      base: Value,
      instance: InductiveFamilyInstance,
      info: RecordInfo,
      count: Int
  ): Vector[Value] = {
    val template = info.template
    val start = (Vector.empty[Value], template.solve(instance.args))
    (0 until count)
      .foldLeft(start) { case ((built, store), field) =>
        val projection = stuck(base, info, field, template.fieldType(field, store))
        val linked = template.fieldVars(field) match {
          case Var(_, id, _) if !store.subst.contains(id) => store.addLink(id, projection)
          case _                                          => store
        }
        (built :+ projection, linked)
      }
      ._1
  }

  private def stuck(base: Value, info: RecordInfo, idx: Int, motive: Value): Value = {
    val env = Env.empty.putLocal(SelfRef, base).putLocal(MotiveRef, motive)
    Interpreter.stuckMatch(info.projectors(idx), base, env, motive)
  }

  /**
   * The types of the fields a projection of field `idx` at `instance` reads: `idx` itself, and every earlier field
   * whose projection that type holds, transitively, which is one the type depends on and the instance's arguments do
   * not solve (`projections`). Each type is the template's at the instance, with its earlier fields left as the
   * template's variables, which is enough to tell a proof from data. A projection of a proof reads them all, as the
   * motive of the one-branch match it is would (`MatchChecker.checkProjectionElimination`).
   */
  def readFields(info: RecordInfo, instance: InductiveFamilyInstance, idx: Int): Vector[Value] = {
    val template = info.template
    val solved = template.solve(instance.args)
    val unsolved = template.fieldVars.map {
      case Var(_, id, _) if !solved.subst.contains(id) => Some(id)
      case _                                           => None
    }
    val read = Vector.newBuilder[Value]
    var pending = List(idx)
    var seen = Set.empty[Int]
    while (pending.nonEmpty) {
      val field = pending.head
      pending = pending.tail
      if (!seen(field)) {
        seen += field
        val tpe = template.fieldType(field, solved)
        read += tpe
        pending = (0 until field).filter(earlier => unsolved(earlier).exists(tpe.synDeps.contains)).toList ++ pending
      }
    }
    read.result()
  }

  /**
   * Whether `fieldType`, the type of a field `project` gives out of a value of the record `info`, still depends on a
   * variable of its template: a capture that the instance's arguments do not determine, directly or through an earlier
   * field's type. Never for a stored field, nor at an eligible type, whose arguments determine every field's type, so
   * that its types are not traversed.
   */
  def undetermined(info: RecordInfo, fieldType: Value): Boolean =
    !info.eta && fieldType.synDeps.intersects(info.template.templateIds)

  /**
   * A canonical projection (`project`): its projected value, the value's family instance, its record, and the field's
   * index. A stuck match is one when its match node is one of the projectors of the record its `__self` belongs to.
   */
  object Projection {
    def unapply(value: Value): Option[(Value, InductiveFamilyInstance, RecordInfo, Int)] =
      value match {
        case thunk: NeutralThunk =>
          thunk.term.scrut match {
            case EA.Term.LocalRef(SelfRef, _) if thunk.env.locals.length > SelfRef.id =>
              thunk.env.localBinding(SelfRef).valueOption.flatMap { base =>
                base.tpe match {
                  case InductiveFamilyValue(instance) =>
                    instance.meta.record.flatMap { info =>
                      val idx = info.projectors.indexWhere(_.nodeId == thunk.term.nodeId)
                      Option.when(idx >= 0)((base, instance, info, idx))
                    }
                  case _ => None
                }
              }
            case _ => None
          }
        case _ => None
      }
  }

  private def isProof(value: Value): Boolean =
    value.tpe.tpe == PropTpe
}
