package com.raccoonlang

import com.raccoonlang.Value._

/** Type-directed field recovery and canonical constructor reconstruction for proofs. */
object ProofReconstruction {

  final case class Result(head: ConstructorHead, fields: Vector[Value])

  private final case class Recovered(
      head: ConstructorHead,
      fields: Vector[Option[Value]],
      resultType: Option[Value]
  )

  private def recoveryInfo(tpe: Value): Option[(InductiveFamilyInstance, ProofRecoveryInfo)] =
    if (!Value.isPropositionType(tpe)) None
    else
      tpe match {
        case InductiveFamilyValue(instance) => instance.meta.proofRecovery.map(info => instance -> info)
        case _                              => None
      }

  /** A declaration-certified constructor is already canonical at its exact result type. */
  def isDefinitelyCertifiedConstructor(tpe: Value, head: ConstructorHead): Boolean =
    recoveryInfo(tpe).exists { case (_, info) =>
      info.definitelyComplete && info.projectionInfo.ctorHeadOption.exists(_.name == head.name)
    }

  /** Whether all fields can be recovered from this exact family instance. */
  def canRecoverAll(tpe: Value): Boolean =
    recoveryInfo(tpe).exists { case (instance, info) => recover(instance, info, includeResultType = false).nonEmpty }

  /** Reconstruct one validated constructor layer at the exact proposition `tpe`. */
  def reconstruct(tpe: Value): Option[Result] =
    recoveryInfo(tpe).flatMap { case (instance, info) =>
      recover(instance, info, includeResultType = true).flatMap { recovered =>
        val fields = recovered.fields.flatten
        if (
          fields.length != info.fieldSources.length ||
          !recovered.resultType.exists { result =>
            ValueEquivalence.defEq(result, tpe)
          }
        ) None
        else Some(Result(recovered.head, fields))
      }
    }

  private def recover(
      instance: InductiveFamilyInstance,
      info: ProofRecoveryInfo,
      includeResultType: Boolean
  ): Option[Recovered] = {
    val head = info.projectionInfo.ctorHeadOption.getOrElse(return None)
    val numParams = head.numErasedFamilyArgs
    if (instance.args.length < numParams || info.fieldSources.length != head.totalArity - numParams) return None

    head.tpe match {
      case pi: VPi =>
        if (pi.binders.length != head.totalArity) return None

        var env = pi.env
        var parameterIndex = 0
        while (parameterIndex < numParams) {
          val binder = pi.binders(parameterIndex)
          val expectedType = Interpreter.evalTerm(binder.ty, env)
          val argument = instance.args(parameterIndex)
          if (!ValueEquivalence.defEq(argument.tpe, expectedType)) return None
          env = env.putLocalUnchecked(binder.localRef, argument)
          parameterIndex += 1
        }

        val fieldBinders = head.fieldBinders
        val recoveredFields = Array.fill[Option[Value]](fieldBinders.length)(None)
        var fieldIndex = 0
        while (fieldIndex < fieldBinders.length) {
          val binder = fieldBinders(fieldIndex)
          val expectedType = Interpreter.evalTerm(binder.ty, env)
          val recovered =
            if (Value.isPropositionType(expectedType)) Value.shallowProof(expectedType)
            else
              info.fieldSources(fieldIndex) match {
                case ProofFieldSource.ResultArgument(resultIndex) =>
                  if (resultIndex < 0 || resultIndex >= instance.args.length) return None
                  val argument = instance.args(resultIndex)
                  if (!ValueEquivalence.defEq(argument.tpe, expectedType)) return None
                  argument
                case ProofFieldSource.Unavailable => return None
              }
          recoveredFields(fieldIndex) = Some(recovered)
          env = env.putLocalUnchecked(binder.localRef, recovered)
          fieldIndex += 1
        }
        val resultType = Option.when(includeResultType)(pi.codomain(env))
        Some(Recovered(head, recoveredFields.toVector, resultType))

      case resultType if head.totalArity == 0 =>
        Some(Recovered(head, Vector.empty, Option.when(includeResultType)(resultType)))
      case _ => None
    }
  }
}
