package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA}

/**
 * Admission checks for recursive definitions.
 *
 * Recursive calls are represented by a temporary native lambda while a body is checked. Calling that lambda proves the
 * call is decreasing; the temporary value is never allowed to escape in a result or a let binding.
 */
object TerminationChecker {
  private[raccoonlang] final case class CheckedLexicographic(
      components: Vector[(CA.LocalRef, Int, String)],
      span: Span
  )

  private def requireInductiveMetric(value: Value, span: Span): Unit = {
    // Equality on propositions is proof-irrelevant.  Consequently constructor
    // shape is not a sound well-founded order for proof values.
    if (value.tpe == PropTpe)
      throw InvalidDecreaseSpec(
        s"decrease metric $value is a proof; structural recursion on proofs is not supported",
        Some(span)
      )
    value.tpe match {
      case ConstSpine(VConst(_, Inductive(_), _), _) =>
      case _ => throw InvalidDecreaseSpec(s"decrease metric $value must have an inductive type", Some(span))
    }
  }

  private[raccoonlang] def checkLexicographic(vpi: VPi, spec: CA.DecreaseSpec, bodyEnv: Env): CheckedLexicographic =
    spec match {
      case CA.DecreaseSpec.Lexicographic(args, sp) =>
        if (args.isEmpty) throw InvalidDecreaseSpec("lexicographic decreases needs at least one argument", Some(sp))
        if (args.distinct.length != args.length)
          throw InvalidDecreaseSpec("lexicographic decreases arguments must be distinct", Some(sp))
        val components = args.map { ref =>
          val idx = vpi.binders.indexWhere(_.localRef == ref)
          if (idx < 0) throw InvalidDecreaseSpec(s"${ref.name} is not a function parameter", Some(sp))
          requireInductiveMetric(bodyEnv(ref), sp)
          (ref, idx, vpi.binders(idx).name)
        }
        CheckedLexicographic(components, sp)
      case CA.DecreaseSpec.Measure(_, sp) =>
        throw InvalidDecreaseSpec("measure decreases are not supported for recursive definition groups", Some(sp))
    }

  private[raccoonlang] def requireCompatible(caller: CheckedLexicographic, callee: CheckedLexicographic): Unit =
    if (caller.components.length != callee.components.length)
      throw InvalidDecreaseSpec(
        s"recursive peers have incompatible metric lengths ${caller.components.length} and ${callee.components.length}",
        Some(callee.span)
      )

  private def checkLexicographicCall(
      name: String,
      callArgs: Vector[Value],
      nativeEnv: Env,
      callee: CheckedLexicographic,
      caller: CheckedLexicographic
  ): Unit = {
    val decreasedAt =
      caller.components.zip(callee.components).find { case ((callerRef, _, _), (_, calleeIdx, calleeName)) =>
        val root = nativeEnv(callerRef)
        val candidate = callArgs(calleeIdx)
        if (isStrictSubterm(candidate, root)) true
        else if (ValueEquivalence.defEq(candidate, root)) false
        else
          throw NonDecreasingRecursiveCall(
            name,
            s"$calleeName is neither equal to nor smaller than the corresponding current argument",
            None
          )
      }
    if (decreasedAt.isEmpty)
      throw NonDecreasingRecursiveCall(name, "no lexicographic component decreases", None)
  }

  private[raccoonlang] def rawRecursivePeer(
      name: String,
      calleePi: VPi,
      callee: CheckedLexicographic,
      caller: CheckedLexicographic,
      callerBodyEnv: Env
  ): VLam = {
    requireCompatible(caller, callee)
    VLam(
      calleePi,
      ValueId.Const(name),
      LamBody.Native(
        (args, nativeEnv) => {
          checkLexicographicCall(name, args, nativeEnv, callee, caller)
          val envWithArgs = BinderOps.instantiateFull(calleePi.binders, calleePi.env, args)
          val resultTy = calleePi.codomain(envWithArgs)
          VApp(VConst(name, Symbol, calleePi), args, resultTy)
        },
        callerBodyEnv,
        isRawRecursive = true
      )
    )
  }

  def rawRecursiveSelf(name: String, vpi: VPi, spec: CA.DecreaseSpec, bodyEnv: Env): VLam = {
    val checkDecrease: (Vector[Value], Env) => Unit = spec match {
      case lexicographic: CA.DecreaseSpec.Lexicographic =>
        val checked = checkLexicographic(vpi, lexicographic, bodyEnv)
        (args, nativeEnv) => checkLexicographicCall(name, args, nativeEnv, checked, checked)
      case CA.DecreaseSpec.Measure(term, sp) =>
        val initialMeasure = TypeChecker.checkTerm(term, bodyEnv)
        requireInductiveMetric(initialMeasure.value, sp)
        val quoted = initialMeasure.residual
        (args, nativeEnv) => {
          val currentMeasure = Interpreter.evalTerm(quoted, nativeEnv)
          val callEnv = BinderOps.instantiateFull(vpi.binders, vpi.env, args)
          val candidate = Interpreter.evalTerm(quoted, callEnv)
          if (!isStrictSubterm(candidate, currentMeasure))
            throw NonDecreasingRecursiveCall(name, "measure does not structurally decrease", None)
        }
    }
    VLam(
      vpi,
      ValueId.Const(name),
      LamBody.Native(
        (args, nativeEnv) => {
          checkDecrease(args, nativeEnv)
          val envWithArgs = BinderOps.instantiateFull(vpi.binders, vpi.env, args)
          val resultTy = vpi.codomain(envWithArgs)
          VApp(VConst(name, Symbol, vpi), args, resultTy)
        },
        bodyEnv,
        isRawRecursive = true
      )
    )
  }

  private[raccoonlang] def isStrictSubterm(candidate: Value, root: Value): Boolean = root match {
    case packed: VPacked =>
      candidate match {
        case child: VPacked if child.codec == packed.codec => packed.codec.strictlyLess(child, packed)
        case _                                             => false
      }
    case VCtor(_, fields, _) =>
      fields.exists(field => applicationOfSubterm(candidate, field) || isStrictSubterm(candidate, field))
    case _ =>
      StructEta
        .fields(root)
        .exists(_.exists(field => applicationOfSubterm(candidate, field) || isStrictSubterm(candidate, field)))
  }

  private def applicationOfSubterm(candidate: Value, field: Value): Boolean =
    ValueEquivalence.defEq(candidate, field) || (candidate match {
      case VApp(head, _, _, _) => applicationOfSubterm(head, field)
      case _                   => false
    })

  /** Raw recursive values are admissible only as the head of a checked call. */
  def assertNonRawRecursive(value: Value, span: Span): Unit = value match {
    case VLam(_, ValueId.Const(name), LamBody.Native(_, _, true)) =>
      throw InvalidRecursiveOccurrence(name, Some(span))
    case _ =>
  }
}
