package com.raccoonlang

import com.raccoonlang.Value._

import scala.collection.immutable.BitSet

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

  /**
   * A trusted constructor application is already canonical when its declaration guarantees recovery. Other
   * instance-sensitive families revalidate recovery at the exact proposition. The hint changes cost, never semantics.
   */
  def isDefinitelyCertifiedConstructor(tpe: Value, head: ConstructorHead): Boolean =
    recoveryInfo(tpe).exists { case (_, info) =>
      info.definitelyComplete && info.projectionInfo.ctorHeadOption.exists(_.name == head.name)
    }

  /** Recover one field and exactly the preceding fields needed to instantiate its type. */
  def recoverField(tpe: Value, fieldIndex: Int): Option[Value] =
    recoveryInfo(tpe).flatMap { case (instance, info) =>
      val projection = info.projectionInfo
      if (fieldIndex < 0 || fieldIndex >= projection.fieldCount) None
      else {
        val required = projection.fieldDependencies(fieldIndex) + fieldIndex
        recover(instance, info, required, includeResultType = false).flatMap(_.fields(fieldIndex)).map { field =>
          // Full reconstruction keeps recursive proof fields shallow. A projected field crosses an
          // observation boundary, so put that selected field into its own canonical representation.
          Value.canonicalizeProof(field)
        }
      }
    }

  /**
   * Whether every constructor field can be recovered from this exact family instance. No result equation is assumed.
   */
  def canRecoverAll(tpe: Value): Boolean =
    recoveryInfo(tpe).exists { case (instance, info) =>
      recover(instance, info, info.allFields, includeResultType = false).nonEmpty
    }

  /**
   * Reconstruct one validated constructor layer at the exact proposition `tpe`. Field recovery performs no search or
   * unification; this final result comparison is what prevents a constrained instance from manufacturing a branch-
   * firing constructor.
   */
  def reconstruct(tpe: Value): Option[Result] =
    recoveryInfo(tpe).flatMap { case (instance, info) =>
      recover(instance, info, info.allFields, includeResultType = true).flatMap { recovered =>
        val fields = recovered.fields.flatten
        if (fields.length != info.fieldSources.length || !recovered.resultType.exists(ValueEquivalence.defEq(_, tpe)))
          None
        else Some(Result(recovered.head, fields))
      }
    }

  private def recover(
      instance: InductiveFamilyInstance,
      info: ProofRecoveryInfo,
      required: BitSet,
      includeResultType: Boolean
  ): Option[Recovered] = {
    val head = info.projectionInfo.ctorHeadOption.getOrElse(return None)
    val numParams = head.numErasedFamilyArgs
    if (instance.args.length < numParams || info.fieldSources.length != head.totalArity - numParams)
      return None

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
          val storedArgument = argument match {
            case _: UpdatableType => Value.ascribe(argument, expectedType)
            case _                => argument
          }
          env = env.putLocalUnchecked(binder.localRef, storedArgument)
          parameterIndex += 1
        }
        val fieldBinders = pi.binders.drop(numParams)
        val recoveredFields = Array.fill[Option[Value]](fieldBinders.length)(None)
        var fieldIndex = 0

        while (fieldIndex < fieldBinders.length) {
          if (required.contains(fieldIndex)) {
            val binder = fieldBinders(fieldIndex)
            val expectedType = Interpreter.evalTerm(binder.ty, env)
            val recovered =
              if (Value.isPropositionType(expectedType)) VProof(expectedType)
              else
                info.fieldSources(fieldIndex) match {
                  case ProofFieldSource.ResultArgument(resultIndex) =>
                    if (resultIndex < 0 || resultIndex >= instance.args.length) return None
                    val argument = instance.args(resultIndex)
                    if (!ValueEquivalence.defEq(argument.tpe, expectedType)) return None
                    argument match {
                      case _: UpdatableType => Value.ascribe(argument, expectedType)
                      case _                => argument
                    }
                  case ProofFieldSource.Unavailable => return None
                }

            recoveredFields(fieldIndex) = Some(recovered)
            // Keep proof fields shallow here. Recursive proof reconstruction canonicalizes one
            // exposed layer at a time rather than building an infinite constructor tree.
            env = env.putLocalUnchecked(binder.localRef, recovered)
          }
          fieldIndex += 1
        }

        val resultType = Option.when(includeResultType)(pi.codomain(env))
        Some(Recovered(head, recoveredFields.toVector, resultType))

      case resultType if head.totalArity == 0 && required.isEmpty =>
        Some(Recovered(head, Vector.empty, Option.when(includeResultType)(resultType)))

      case _ => None
    }
  }
}
