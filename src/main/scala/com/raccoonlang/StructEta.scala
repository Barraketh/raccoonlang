package com.raccoonlang

import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * Structure eta as rules, not representation. A value of an eta-eligible structure type is NOT forced into constructor
 * form; instead `fields` supplies the eta *view* of any such value — its stored fields when it is already constructor-
 * headed, and its virtual field projections when it is neutral — and the four consumers of eta (match evaluation,
 * definitional equality, unification, structural subterm descent) all read that one view.
 *
 * Eligibility is a checked declaration property (one constructor, zero indices, nonrecursive) plus non-propness. Prop
 * instances remain proof-representation territory and never eta-expand. A field projection is an ordinary `match`, so
 * `match` stays the kernel's only eliminator.
 */
object StructEta {

  private def anyInstance(tpe: Value): Option[(InductiveFamilyInstance, ProjectionInfo)] =
    tpe match {
      case InductiveFamilyValue(inst) => inst.meta.projectionInfo.filter(_.etaEligible).map(info => (inst, info))
      case _                          => None
    }

  /** The eta-eligible family instance behind `tpe`, excluding proposition-valued instances. */
  def eligibleInstance(tpe: Value): Option[(InductiveFamilyInstance, ProjectionInfo)] =
    anyInstance(tpe).filter(_ => !Sorts.isProposition(tpe))

  /**
   * The eta view of a value at an eta-eligible structure type: the constructor's stored fields when it is already in
   * constructor form, and the virtual field projections otherwise. `None` for anything that is not at such a type.
   *
   * This is the single statement of structure eta. A `VProof` never has a view: proof values are governed by proof
   * irrelevance, and eligibility already excludes propositions.
   */
  def fields(value: Value): Option[Vector[Value]] =
    value match {
      case _: VProof => None
      case _ =>
        eligibleInstance(value.tpe).map { case (inst, info) =>
          value match {
            case ConstructorForm(ctorName, stored) if ctorName == info.ctorName =>
              if (stored.length != info.fieldCount)
                wtf(s"Constructor $ctorName supplied ${stored.length} fields, expected ${info.fieldCount}")
              stored
            case _ =>
              Vector.tabulate(info.fieldCount)(idx => fieldProjection(value, inst, info, idx))
          }
        }
    }

  /**
   * The canonical projection of field `idx` out of `base`. When `base` is constructor-headed this is the stored field;
   * otherwise it is the stuck evaluation of the canonical match term
   * `match self returning motive with | mk x0 … xn => x_idx`, with `motive` bound to the field's type at `base`.
   */
  def fieldProjection(base: Value, inst: InductiveFamilyInstance, info: ProjectionInfo, idx: Int): Value = {
    if (idx < 0 || idx >= info.fieldCount)
      fail(InvalidProjection(inst.head.name, idx, s"field index is out of range (${info.fieldCount} fields)"))
    base match {
      case ConstructorForm(ctorName, stored) if ctorName == info.ctorName =>
        if (stored.length != info.fieldCount)
          wtf(s"Constructor $ctorName supplied ${stored.length} fields, expected ${info.fieldCount}")
        stored(idx)
      case _ =>
        val program = info.projectors(idx)
        val motive = fieldType(base, inst, info, idx)
        // The projection term is self-contained: besides `self` and `motive` it names only its own
        // constructor, which is bound here so the term evaluates (and compares, via
        // tryUnifyNeutralMatches) without a surrounding global environment.
        val env = Env.empty
          .putGlobal(info.ctorHead.name, info.ctorHead)
          .putLocalUnchecked(program.self, base)
          .putLocal(program.motive, motive)
        val blockedOn = Blocker.unapply(base).getOrElse(DepSet.empty) ++ Interpreter.typeCollapseDeps(base.tpe)
        // The thunk a stuck evaluation of the same term would build, so re-sticking it keeps its identity.
        Value.canonicalizeProof(Interpreter.stuckMatchThunk(program.term, env, motive, blockedOn))
    }
  }

  /**
   * The type of field `idx` at this instance: the constructor's field telescope instantiated with the instance's family
   * arguments, extended with the projections of exactly the preceding fields that type depends on.
   */
  private def fieldType(base: Value, inst: InductiveFamilyInstance, info: ProjectionInfo, idx: Int): Value = {
    val head = info.ctorHead
    if (info.fieldCount > 0 && head.pi.isEmpty)
      wtf(s"Constructor ${head.name} has fields but non-Pi type ${head.tpe}")
    val binders = head.fieldBinders
    var env = head.fieldEnv(inst.args)
    val dependencies = info.fieldDependencies(idx)
    var fieldIdx = 0
    while (fieldIdx < idx) {
      if (dependencies.contains(fieldIdx))
        env = BinderOps.bindValue(env, binders(fieldIdx), fieldProjection(base, inst, info, fieldIdx))
      fieldIdx += 1
    }
    Interpreter.evalTerm(binders(idx).ty, env)
  }

  /**
   * The canonical projection program for one field of one family:
   * `match self returning motive with | mk x0 … xn => x_idx`. Each field index gets its own synthetic span, so its
   * `nodeId` is stable across every projection of that field and distinct from every other field's — which is exactly
   * what makes two projections of defEq bases compare equal by id.
   *
   * Every match writes its motive, and a field's type has no syntax in terms of `self` alone, so the motive is a local
   * that `fieldProjection` binds to the field's type at the base. Being a function of the base, it adds nothing to the
   * projection's identity that `self` does not already determine.
   *
   * The whole program is determined by the constructor's canonical name and the field count, so it is built once with
   * the family's `ProjectionInfo` (`ProjectionInfo.projectors`) rather than cached against it.
   */
  final case class Projector(self: CoreAst.LocalRef, motive: CoreAst.LocalRef, term: CTerm.Match)

  private[raccoonlang] def buildProjector(ctorName: String, fieldCount: Int, idx: Int): Projector = {
    val selfRef = SyntheticLocalRef.fresh("self")
    val motiveRef = SyntheticLocalRef.fresh("motive")
    val fieldRefs = Vector.tabulate(fieldCount)(i => SyntheticLocalRef.fresh(s"x$i"))
    val span = Span.synthetic()
    val body = CTerm.LocalRef(fieldRefs(idx), span)
    val branch = CoreAst.Case(ctorName, isFullyQualified = true, fieldRefs.map(Some(_)), body, span)
    val term = CTerm.Match(CTerm.LocalRef(selfRef, span), CTerm.LocalRef(motiveRef, span), Vector(branch), span)
    Projector(selfRef, motiveRef, term)
  }
}
