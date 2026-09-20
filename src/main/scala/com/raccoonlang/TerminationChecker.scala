package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA}

/** Termination checking uses a temporary raw-recursive value installed as a local while checking the body. */
object TerminationChecker {
  private[raccoonlang] final case class CheckedLexicographic(
      components: Vector[(CA.LocalRef, Int, String)],
      span: Span
  )

  private def requireInductiveMetric(value: Value, span: Span): Unit = {
    // Proof structure is not invariant under an equality that identifies wrap(x) with base;
    // erased proofs also have no subterms. Well-founded recursion on proofs needs a
    // dedicated Acc-style mechanism (docs/kernel.md#termination).
    if (Value.isPropositionType(value.tpe))
      at(span) { fail(NonInductiveDecreaseMetric(value, isProof = true)) }
    value.tpe match {
      case ConstSpine(VConst(_, Inductive(_), _), _) =>
      case _ => at(span) { fail(NonInductiveDecreaseMetric(value, isProof = false)) }
    }
  }

  private[raccoonlang] def checkLexicographic(
      vpi: VPi,
      spec: CA.DecreaseSpec,
      bodyEnv: Env
  ): CheckedLexicographic =
    spec match {
      case CA.DecreaseSpec.Lexicographic(args, sp) =>
        if (args.isEmpty) at(sp) { fail(InvalidDecreaseSpec("lexicographic decreases needs at least one argument")) }
        if (args.distinct.length != args.length)
          at(sp) { fail(InvalidDecreaseSpec("lexicographic decreases arguments must be distinct")) }

        val components = args.map { ref =>
          val idx = vpi.binders.indices.find(idx => vpi.binders(idx).localRef == ref).getOrElse {
            at(sp) { fail(InvalidDecreaseSpec(s"${ref.name} is not a function parameter")) }
          }
          requireInductiveMetric(bodyEnv(ref), sp)
          (ref, idx, vpi.binders(idx).name)
        }
        CheckedLexicographic(components, sp)

      case CA.DecreaseSpec.Measure(_, sp) =>
        at(sp) { fail(InvalidDecreaseSpec("measure decreases are not supported for recursive definition groups")) }
    }

  private[raccoonlang] def requireCompatible(
      caller: CheckedLexicographic,
      callee: CheckedLexicographic
  ): Unit =
    if (caller.components.length != callee.components.length)
      at(callee.span) {
        fail(
          InvalidDecreaseSpec(
            s"recursive peers have incompatible metric lengths ${caller.components.length} and ${callee.components.length}"
          )
        )
      }

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
          fail(
            NonDecreasingRecursiveCall(
              name,
              s"$calleeName is neither equal to nor smaller than the corresponding current argument"
            )
          )
      }
    if (decreasedAt.isEmpty)
      fail(NonDecreasingRecursiveCall(name, "no lexicographic component decreases"))
  }

  /**
   * The checker-only stub a recursive call runs: it validates the decrease against the caller's current arguments and
   * then residualizes the call. It never reduces, so the body cannot store it as an ordinary value
   * (`assertNonRawRecursive`).
   */
  private def rawRecursiveStub(
      name: String,
      calleePi: VPi,
      callerBodyEnv: Env,
      checkDecrease: (Vector[Value], Env) => Unit
  ): VLam =
    VLam(
      calleePi,
      ValueId.Const(name),
      LamBody.Native(
        (callArgs, nativeEnv) => {
          checkDecrease(callArgs, nativeEnv)

          val envWithArgs = BinderOps.instantiateFull(calleePi.binders, calleePi.env, callArgs)
          val resultTy = calleePi.codomain(envWithArgs)
          // A recursive call in a proof-by-recursion produces a proof of the instantiated goal.
          Value.canonicalizeProof(VApp(VConst(name, Symbol, calleePi), callArgs, resultTy))
        },
        callerBodyEnv,
        isRawRecursive = true
      )
    )

  private[raccoonlang] def rawRecursivePeer(
      name: String,
      calleePi: VPi,
      callee: CheckedLexicographic,
      caller: CheckedLexicographic,
      callerBodyEnv: Env
  ): VLam = {
    requireCompatible(caller, callee)
    rawRecursiveStub(
      name,
      calleePi,
      callerBodyEnv,
      (callArgs, nativeEnv) => checkLexicographicCall(name, callArgs, nativeEnv, callee, caller)
    )
  }

  def rawRecursiveSelf(
      name: String,
      vpi: VPi,
      spec: CA.DecreaseSpec,
      bodyEnv: Env
  ): VLam =
    spec match {
      // A singleton's self call is the degenerate peer call: it is its own caller and callee, so
      // the metric it must decrease is the one it declares.
      case lexicographic: CA.DecreaseSpec.Lexicographic =>
        val checked = checkLexicographic(vpi, lexicographic, bodyEnv)
        rawRecursivePeer(name, vpi, checked, checked, bodyEnv)

      case CA.DecreaseSpec.Measure(term, sp) =>
        val initialMeasure = TypeChecker.checkTerm(term, bodyEnv)
        requireInductiveMetric(initialMeasure.value, sp)
        val measureTerm = initialMeasure.residual
        rawRecursiveStub(
          name,
          vpi,
          bodyEnv,
          (args, nativeEnv) => {
            val currentMeasure = Interpreter.evalTerm(measureTerm, nativeEnv)
            val callEnv = BinderOps.instantiateFull(vpi.binders, vpi.env, args)
            val candidate = Interpreter.evalTerm(measureTerm, callEnv)
            if (!isStrictSubterm(candidate, currentMeasure))
              fail(NonDecreasingRecursiveCall(name, "measure does not structurally decrease"))
          }
        )
    }

  private[raccoonlang] def isStrictSubterm(candidate: Value, root: Value): Boolean =
    root match {
      // A packed root is ordered by its codec, never by field descent: the decoded layer is a
      // freshly built value, so descending it would compare against a different representation.
      // This arm must stay ahead of the constructor-form one.
      case root: VPacked =>
        candidate match {
          case packed: VPacked if packed.codec == root.codec => root.codec.strictlyLess(packed, root)
          case _                                             => false
        }
      case ConstructorForm(_, fields) =>
        descendsInto(candidate, fields)
      // Structure eta (rule 4): a neutral root at an eta-eligible struct type has the same fields a
      // constructor root would, reached virtually. Descending into them keeps a struct parameter's
      // projections strict subterms of the parameter, as they were when eta held by representation.
      case _ =>
        StructEta.fields(root) match {
          case Some(fields) => descendsInto(candidate, fields)
          case None         => false
        }
    }

  private def descendsInto(candidate: Value, fields: Vector[Value]): Boolean =
    fields.exists { field =>
      applicationOfSubterm(candidate, field) || isStrictSubterm(candidate, field)
    }

  /**
   * The candidate is the field itself, or an application spine whose head is the field. A function-typed field of a
   * strictly positive inductive is its node's child-selector in the value's tree semantics, so any application of it is
   * a child — one level down the well-founded tree (docs/kernel.md#termination, structural decrease). The order is
   * well-founded only while values are well-founded trees: strict positivity is enforced by InductiveChecks, and no
   * value can capture itself (recursion requires a decreasing parameter, so there is no value-level recursion). Only
   * `VApp` frames are stripped; any other candidate head must be defEq to the field itself, so descent never passes
   * through a blocked match, which could reduce to anything once unblocked. A field reached through structure eta is a
   * stuck projection match rather than a stored value, so this comparison is definitional (`defEq`) and not identity.
   */
  private def applicationOfSubterm(candidate: Value, field: Value): Boolean =
    ValueEquivalence.defEq(candidate, field) || (candidate match {
      case VApp(head, _, _, _) => applicationOfSubterm(head, field)
      case _                   => false
    })
}
