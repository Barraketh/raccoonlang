package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA}

/**
 * Termination checking uses a temporary raw-recursive value installed as a local while checking the body.
 *
 * A function whose result is a proposition may also decrease a proof. Its calls are compared by identity, never by
 * conversion: proof irrelevance makes every proof of a proposition convertible with every other, so conversion would
 * accept any call. The raw recursive self reads the root through the branch's refinement, in which `MatchChecker` links
 * a proof variable to the constructor value the branch matched, when that refinement succeeds.
 */
object TerminationChecker {
  def rawRecursiveSelf(name: String, vpi: VPi, spec: CA.DecreaseSpec, bodyEnv: Env): VLam = {
    val provesProposition = vpi.tpe == PropTpe

    /** A metric must have an inductive type; a proof is `InvalidDecreaseSpec` for `proofRejection`, if one is given. */
    def requireInductiveMetric(value: Value, span: Span, proofRejection: Option[String]): Unit = {
      if (isProof(value)) proofRejection.foreach(reason => throw InvalidDecreaseSpec(reason, Some(span)))
      value.tpe match {
        case ConstSpine(VConst(_, Inductive(_), _), _) =>
        case _ => throw InvalidDecreaseSpec(s"decrease metric ${value} must have an inductive type", Some(span))
      }
    }

    val checkDecrease: (Vector[Value], Env) => Unit = spec match {
      case CA.DecreaseSpec.Lexicographic(args, sp) =>
        if (args.isEmpty) throw InvalidDecreaseSpec("lexicographic decreases needs at least one argument", Some(sp))
        if (args.distinct.length != args.length)
          throw InvalidDecreaseSpec("lexicographic decreases arguments must be distinct", Some(sp))

        val indices = args.map { ref =>
          vpi.binders.indices.find(idx => vpi.binders(idx).localRef.id == ref.id).getOrElse {
            throw InvalidDecreaseSpec(s"${ref.name} is not a function parameter", Some(sp))
          }
        }
        val metrics = args.map(ref => bodyEnv(ref))
        val proofRejection =
          Option.unless(provesProposition)(
            "decrease metrics in Prop are allowed only for functions returning a proposition"
          )
        metrics.foreach(requireInductiveMetric(_, sp, proofRejection))
        // Each component's order: proofs by identity, data by conversion.
        val components = args.zip(indices).zip(metrics).map { case ((ref, idx), metric) =>
          val (smaller, same): ((Value, Value) => Boolean, (Value, Value) => Boolean) =
            if (isProof(metric)) (isStrictSubproof, (candidate, root) => candidate.key == root.key)
            else (isStrictSubterm, ValueEquivalence.defEq)
          (ref, idx, smaller, same)
        }

        (callArgs, nativeEnv) => {
          val decreasedAt = components.find { case (ref, idx, smaller, same) =>
            val root = nativeEnv.apply(ref)
            val candidate = callArgs(idx)
            if (smaller(candidate, root)) true
            else if (same(candidate, root)) false
            else
              throw NonDecreasingRecursiveCall(
                name,
                s"${vpi.binders(idx).name} is neither equal to nor smaller than the current argument",
                None
              )
          }
          if (decreasedAt.isEmpty) throw NonDecreasingRecursiveCall(name, "no lexicographic component decreases", None)
        }

      case CA.DecreaseSpec.Measure(term, sp) =>
        val initialMeasure = TypeChecker.checkTerm(term, bodyEnv)
        // Every call evaluates the measure again on its arguments without consuming them, so it is a read extent of
        // its own (L6), and its reads are no uses. A `structural` or `lexicographic` clause only names parameters.
        TypeChecker.readBoundary(initialMeasure.lin)
        val proofRejection = "decrease measures must live in Type; proofs in Prop cannot be used"
        requireInductiveMetric(initialMeasure.value, sp, Some(proofRejection))
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

  private def isStrictSubterm(candidate: Value, root: Value): Boolean =
    root match {
      case form: VNatPoly => NatNormalForm.isStrictlySmaller(candidate, form)
      case VCtor(_, fields, _) =>
        fields.exists(field => isFieldOrStrictSubterm(candidate, field))
      case word: VWord =>
        packed.Words.isProperSuffix(candidate, word) || {
          // Each layer's payload, then its tail, which is the rest at the next token, as the constructor view decodes
          // them, in one loop. The end is decomposed further.
          var found = false
          var first = true
          def tail(token: packed.Token): Boolean = !first && ValueEquivalence.defEq(candidate, token.rest)
          packed.Words.foreach(word)(
            layer = token => {
              found = tail(token) ||
                (0 until token.payloadWidth).exists(index => isFieldOrStrictSubterm(candidate, token.payload(index)))
              first = false
              !found
            },
            end = token => {
              found = tail(token) || isStrictSubterm(candidate, token.value)
              false
            }
          )
          found
        }
      // Structure eta: a field projection of a neutral value at an eligible type is one of its fields.
      case _ => StructEta.fields(root).exists(_.exists(field => isFieldOrStrictSubterm(candidate, field)))
    }

  private def isFieldOrStrictSubterm(candidate: Value, field: Value): Boolean =
    // Proof fields cannot expose data subterms, since proof irrelevance hides their structure.
    !isProof(field) && (ValueEquivalence.defEq(candidate, field) || isStrictSubterm(candidate, field))

  /**
   * Whether `candidate` is a proof field of `root`, or of one of its proof fields, by structural key. Keys distinguish
   * proofs that conversion identifies, so a rebuilt proof of a field's proposition is not mistaken for the field. As in
   * `ValueEquivalence.defEq`, equal keys are trusted to mean equal values. The search does not enter data fields, such
   * as the field of `Fact.mk(h)`.
   */
  private def isStrictSubproof(candidate: Value, root: Value): Boolean =
    root match {
      case VCtor(_, fields, _) =>
        fields.exists(field => isProof(field) && (field.key == candidate.key || isStrictSubproof(candidate, field)))
      case _ => false
    }

  private def isProof(value: Value): Boolean = TypeChecker.getUniverse(value.tpe) == PropTpe
}
