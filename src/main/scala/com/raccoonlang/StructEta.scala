package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * Structure eta as representation: every value of a derived structure-like type is constructor-headed from creation.
 * Eligibility is a checked declaration property (one constructor, zero indices, nonrecursive), independent of whether
 * the source used `struct` or `inductive`. Named selectors are frontend definitions and play no role here.
 *
 * Prop instances remain proof-representation territory and never eta-expand. Primitive positional projection is
 * implemented separately by InductiveProjection and remains available to indexed or recursive singleton families.
 */
object StructEta {

  private def anyInstance(tpe: Value): Option[(InductiveFamilyInstance, ProjectionInfo)] =
    tpe match {
      case InductiveFamilyValue(inst) => inst.meta.projectionInfo.filter(_.etaEligible).map(info => (inst, info))
      case _                          => None
    }

  /** The eta-eligible family instance behind `tpe`, excluding proposition-valued instances. */
  def eligibleInstance(tpe: Value): Option[(InductiveFamilyInstance, ProjectionInfo)] =
    anyInstance(tpe).filter(_ => !Value.isPropositionType(tpe))

  /** A fresh rigid witness at an eta-eligible type, recursively expanding nested structure-like fields. */
  def freshStructWitness(tpe: Value): Option[Value] =
    eligibleInstance(tpe).map { case (inst, info) =>
      val head = info.ctorHead
      head.tpe match {
        case pi: VPi =>
          val paramBinders = pi.binders.take(head.numErasedFamilyArgs)
          val fieldBinders = pi.binders.drop(head.numErasedFamilyArgs)
          val paramEnv = BinderOps.instantiateFull(paramBinders, pi.env, inst.args.take(paramBinders.length))
          val fieldEnv = BinderOps.freshen(fieldBinders, paramEnv)
          VCtor(head, fieldBinders.map(binder => fieldEnv(binder.localRef)), tpe)
        case _ => VCtor(head, Vector.empty, tpe)
      }
    }

  /**
   * Enforce the representation invariant on a just-created neutral value. Vars remain bare so refinable metas stay
   * linkable; constructors and proofs are already canonical.
   */
  def expandIfStruct(value: Value): Value =
    value match {
      case VCtor(_, _, _)     => value
      case _: Var | _: VProof => value
      case _: VConst | _: VApp | _: NeutralThunk =>
        eligibleInstance(value.tpe) match {
          case Some((inst, info)) =>
            VCtor(
              info.ctorHead,
              InductiveProjection.projections(value, inst, info),
              value.tpe
            )
          case None => value
        }
      case _ => value
    }
}
