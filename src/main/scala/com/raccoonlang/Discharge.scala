package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * Evidence discharge (PROOF_BY_EVALUATION §1.2, §1.9; docs/kernel.md, "Evidence arguments"): a proof of the proposition
 * `P′` an evidence binder's type evaluates to where an application stands, found without search.
 *
 *   - Rule 1: `P′` is an instance of a family with a constructor whose fields its result type determines, and whose
 *     result type, at the fields read off `P′`, is convertible with it (ProofReconstruction.determined, which invents
 *     no field). The constructors are tried in declaration order and the first that fits is taken; proof irrelevance
 *     makes the choice unobservable.
 *   - Rule 2: `P′` is an instance of an evidence-eligible family (InductiveMeta.evidenceEligible), and each of its
 *     constructor's evidence fields, in order, has a proposition that, evaluated with its arguments and the earlier
 *     fields' proofs, is discharged in turn. The proof is the constructor applied to those proofs.
 *
 * Either rule applies the constructor for the program at the application's site, as if it named it, so a sealed
 * family's constructors discharge only in its module (Sealing): elsewhere one would build a value its module never
 * built. A family of a block still being checked has no constructors to discharge with.
 *
 * Discharge terminates because it takes at most `DepthBound` rule-2 steps on any path: each step evaluates a field's
 * proposition, which is total, and has finitely many fields, so the tree of steps is finite.
 */
private[raccoonlang] object Discharge {

  /**
   * The most rule-2 steps on a path from an application's proposition, part of what a program means: a proposition a
   * step deeper would be discharged by is not discharged (`TooDeep`).
   */
  val DepthBound: Int = 1024

  /**
   * Where discharge failed: at `proposition`, reached from the one discharged through the evidence fields `path`, each
   * named `Family.field`, for `reason`.
   */
  final case class Failure(path: Vector[String], proposition: Value, reason: EvidenceNotDischarged.Reason)

  /** A proof of `proposition` for an application at `site` in `env`, or where and why there is none. */
  def discharge(proposition: Value, site: Span, env: Env): Either[Failure, Value] =
    dischargeAt(proposition, depth = 0, site, env)

  /** `depth` is how many rule-2 steps lead from the application's proposition to `proposition`. */
  private def dischargeAt(proposition: Value, depth: Int, site: Span, env: Env): Either[Failure, Value] = {
    def failed(reason: EvidenceNotDischarged.Reason): Either[Failure, Value] =
      Left(Failure(Vector.empty, proposition, reason))
    proposition match {
      case InductiveFamilyValue(instance) =>
        if (!Sealing.accessible(instance.meta.seal, site)) failed(EvidenceNotDischarged.Sealed)
        else
          instance.meta.block match {
            case _: ProvisionalInductiveBlockInfo => failed(EvidenceNotDischarged.Undeclared)
            case _: CheckedInductiveBlockSchema =>
              determined(proposition, instance, env) match {
                case Some(proof)                             => Right(proof)
                case None if !instance.meta.evidenceEligible => failed(EvidenceNotDischarged.NoConstructor)
                // This step would be at depth `depth + 1`.
                case None if depth == DepthBound => failed(EvidenceNotDischarged.TooDeep)
                case None                        => throughEvidenceFields(proposition, instance, depth, site, env)
              }
          }
      case _ => failed(EvidenceNotDischarged.NoConstructor)
    }
  }

  private def constructorHead(ctor: ConstructorMeta, env: Env): ConstructorHead =
    env(ctor.canonicalName) match {
      case head: ConstructorHead => head
      case other                 => wtf(s"Constructor ${ctor.canonicalName} is $other")
    }

  /** Rule 1: the first constructor, in declaration order, whose fields `proposition` determines. */
  private def determined(proposition: Value, instance: InductiveFamilyInstance, env: Env): Option[Value] =
    instance.meta.constructors.iterator
      .flatMap { ctor =>
        val sources = ctor.fieldSources.getOrElse(wtf(s"Constructor ${ctor.canonicalName} has no field sources"))
        ProofReconstruction.determined(proposition, instance, constructorHead(ctor, env), sources)
      }
      .nextOption()
      .map(proof => Value.canonicalizeProof(VCtor(proof.head, proof.fields, proposition)))

  /**
   * Rule 2: each evidence field's proposition, in order, evaluated in the constructor's telescope at the instance's
   * arguments and the earlier fields' proofs, discharged in turn. A failure is reported at the field, depth first.
   */
  private def throughEvidenceFields(
      proposition: Value,
      instance: InductiveFamilyInstance,
      depth: Int,
      site: Span,
      env: Env
  ): Either[Failure, Value] = {
    val head = constructorHead(instance.meta.constructors.head, env)
    @annotation.tailrec
    def fields(binders: List[CoreAst.Binder], telescope: Env, proofs: Vector[Value]): Either[Failure, Vector[Value]] =
      binders match {
        case Nil => Right(proofs)
        case binder :: rest =>
          val fieldProposition = Interpreter.evalTerm(binder.ty, telescope)
          dischargeAt(fieldProposition, depth + 1, site, env) match {
            case Left(failure) =>
              Left(failure.copy(path = s"${instance.head.name}.${binder.name}" +: failure.path))
            case Right(proof) => fields(rest, BinderOps.bindValue(telescope, binder, proof), proofs :+ proof)
          }
      }
    fields(head.fieldBinders.toList, head.fieldEnv(instance.args), Vector.empty).map { proofs =>
      Value.canonicalizeProof(VCtor(head, proofs, proposition))
    }
  }
}
