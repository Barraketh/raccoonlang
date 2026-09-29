package com.raccoonlang

import com.raccoonlang.Value._

/** Type-directed field recovery and canonical constructor reconstruction for proofs. */
object ProofReconstruction {

  /** A reconstructed constructor layer, which only `reconstruct` hands out. */
  final class Result private[ProofReconstruction] (val head: ConstructorHead, val fields: Vector[Value])

  private final case class Recovered(
      head: ConstructorHead,
      fields: Vector[Option[Value]],
      resultType: Option[Value]
  )

  private def recoveryInfo(tpe: Value): Option[(InductiveFamilyInstance, ProofRecoveryInfo)] =
    if (!Sorts.isProposition(tpe)) None
    else
      tpe match {
        case InductiveFamilyValue(instance) => instance.meta.proofRecovery.map(info => instance -> info)
        case _                              => None
      }

  /**
   * Whether an application of `head` is a proof's canonical form at the exact proposition `tpe`: the one constructor
   * its recovery plan names, validated at this instance. A trusted application of a declaration-certified constructor
   * already carries the result-forced data fields, so it skips validation; the hint changes cost, never semantics.
   */
  def isCanonicalConstructor(tpe: Value, head: ConstructorHead): Boolean =
    recoveryInfo(tpe).exists { case (instance, info) =>
      info.projectionInfo.ctorHeadOption.exists(_.name == head.name) &&
      (info.definitelyComplete || validate(instance, info, tpe).nonEmpty)
    }

  /**
   * Whether every constructor field can be recovered from this exact family instance. No result equation is assumed.
   */
  def canRecoverAll(tpe: Value): Boolean =
    recoveryInfo(tpe).exists { case (instance, info) =>
      recover(instance, info, includeResultType = false).nonEmpty
    }

  /**
   * Reconstruct one validated constructor layer at the exact proposition `tpe`, a sealed one included (spec §7.1): only
   * the trusted prelude declares axioms and builtins, and none of them yields a proof of a sealed proposition except by
   * applying its constructors (obligation T2, docs/kernel.md), so every such proof was built from its constructors.
   */
  def reconstruct(tpe: Value): Option[Result] =
    recoveryInfo(tpe).flatMap { case (instance, info) => validate(instance, info, tpe) }

  /**
   * Field recovery performs no search or unification; this final result comparison is what prevents a constrained
   * instance from manufacturing a branch-firing constructor.
   */
  private def validate(instance: InductiveFamilyInstance, info: ProofRecoveryInfo, tpe: Value): Option[Result] =
    recover(instance, info, includeResultType = true).flatMap { recovered =>
      val fields = recovered.fields.flatten
      if (fields.length != info.fieldSources.length || !recovered.resultType.exists(ValueEquivalence.defEq(_, tpe)))
        None
      else Some(new Result(recovered.head, fields))
    }

  private def recover(
      instance: InductiveFamilyInstance,
      info: ProofRecoveryInfo,
      includeResultType: Boolean
  ): Option[Recovered] = {
    val head = info.projectionInfo.ctorHeadOption.getOrElse(return None)
    val numParams = head.numErasedFamilyArgs
    if (instance.args.length < numParams || info.fieldSources.length != head.totalArity - numParams)
      return None

    head.tpe match {
      case pi: VPi =>
        if (pi.binders.length != head.totalArity) return None

        // Not head.fieldEnv: recovery validates each parameter's type and reports a mismatch as a
        // recovery failure (None), where fieldEnv binds unconditionally and would throw.
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
            if (Sorts.isProposition(expectedType)) Value.shallowProof(expectedType)
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
          // Keep inductive proof fields shallow here. Recursive proof reconstruction canonicalizes one exposed
          // layer at a time rather than building an infinite constructor tree; Pi proofs remain eta-applicable.
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
