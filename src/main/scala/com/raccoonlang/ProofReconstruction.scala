package com.raccoonlang

import com.raccoonlang.Value._

/** Declaration-certified, type-directed canonical constructor reconstruction for proofs. */
object ProofReconstruction {

  final case class Result(head: ConstructorHead, fields: Vector[Value])

  /**
   * Whether `head` is the declaration-certified constructor for `tpe`. A well-typed application of that head already
   * carries every data field forced by its result type, so canonicalization can preserve it without re-executing the
   * reconstruction recipe.
   */
  def isCertifiedConstructor(tpe: Value, head: ConstructorHead): Boolean =
    tpe match {
      case InductiveFamilyValue(instance) =>
        instance.meta.proofStorage match {
          case ProofStorage.Reconstruct(info) => info.ctorHead.exists(_.name == head.name)
          case ProofStorage.Erase             => false
        }
      case _ => false
    }

  /**
   * Reconstruct one constructor layer at the exact proposition `tpe`. This performs no search or unification: the
   * declaration records the sole constructor and the source of every stored field. The final result-type comparison is
   * what distinguishes a diagonal instance such as `Eq Nat zero zero` from a non-diagonal one such as
   * `Eq Type Nat Bool`.
   */
  def reconstruct(tpe: Value): Option[Result] =
    tpe match {
      case InductiveFamilyValue(instance) =>
        instance.meta.proofStorage match {
          case ProofStorage.Reconstruct(info) => reconstruct(instance, info, tpe)
          case ProofStorage.Erase             => None
        }
      case _ => None
    }

  private def reconstruct(
      instance: InductiveFamilyInstance,
      info: ProofConstructorInfo,
      exactType: Value
  ): Option[Result] = {
    val head = info.ctorHead.getOrElse(return None)
    val numParams = head.numErasedFamilyArgs
    if (instance.args.length < numParams || info.fields.length != head.totalArity - numParams)
      return None

    head.tpe match {
      case pi: VPi =>
        if (pi.binders.length != head.totalArity) return None

        var env = pi.env
        val fullArgs = Vector.newBuilder[Value]
        var idx = 0

        while (idx < pi.binders.length) {
          val binder = pi.binders(idx)
          val expectedType = Interpreter.evalTerm(binder.ty, env)
          val fieldRecipe = if (idx < numParams) None else Some(info.fields(idx - numParams))
          val arg =
            fieldRecipe match {
              case None => instance.args(idx)
              case Some(ProofFieldRecipe.ResultArgument(resultIndex)) =>
                if (resultIndex < 0 || resultIndex >= instance.args.length) return None
                instance.args(resultIndex)
              case Some(ProofFieldRecipe.ErasedProof) =>
                if (!Value.isPropositionType(expectedType)) return None
                // Deliberately shallow: a recursive proof field canonicalizes when it is later
                // exposed as a binder, rather than constructing an infinite proof tree now.
                // Do not pass this through `ascribe`: that would immediately reconstruct the
                // same recursive constructor layer again.
                VProof(expectedType)
            }

          if (!ValueEquivalence.defEq(arg.tpe, expectedType)) return None
          val storedArg = fieldRecipe match {
            case Some(ProofFieldRecipe.ErasedProof) => arg
            case _ =>
              arg match {
                case _: UpdatableType => Value.ascribe(arg, expectedType)
                case _                => arg
              }
          }
          fullArgs += storedArg
          env = env.putLocalUnchecked(binder.localRef, storedArg)
          idx += 1
        }

        val resultType = pi.codomain(env)
        if (!ValueEquivalence.defEq(resultType, exactType)) None
        else Some(Result(head, fullArgs.result().drop(numParams)))

      case resultType if head.totalArity == 0 && ValueEquivalence.defEq(resultType, exactType) =>
        Some(Result(head, Vector.empty))

      case _ => None
    }
  }
}
