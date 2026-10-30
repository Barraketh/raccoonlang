package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA}

/**
 * Termination checking uses a temporary raw-recursive value installed as a local while checking the body: for a
 * recursive definition its own self, and for a member of a mutual block one per member of the block, itself included.
 * Each checks, at a call, that the callee's metric at the call's arguments is smaller than the caller's at its own.
 *
 * A function whose result is a proposition may also decrease a proof. Its calls are compared by identity, never by
 * conversion: proof irrelevance makes every proof of a proposition convertible with every other, so conversion would
 * accept any call. The raw recursive self reads the root through the branch's refinement, in which `MatchChecker` links
 * a proof variable to the constructor value the branch matched, when that refinement succeeds.
 */
object TerminationChecker {

  /**
   * A recursive function's metric: a tuple of components, ordered lexicographically, each by the structural subterm
   * order on data or the proof field order on proofs (docs/kernel.md, "Recursion on proofs"). `current` reads the
   * components at the function's own arguments in a caller's environment, refined in the branch the call is in, and
   * `atCall` computes them at a call's arguments. A `structural` or `lexicographic` clause names parameters, whose
   * values are its components; a `measure` is one component, its term evaluated again at each call, which reads its
   * arguments and consumes nothing (L6).
   */
  private[raccoonlang] final class Metric(
      val name: String,
      val vpi: VPi,
      val span: Span,
      val componentNames: Vector[String],
      val current: Env => Vector[Value],
      val atCall: Vector[Value] => Vector[Value]
  )

  /** `spec`, checked as the metric of the function `name` of type `vpi`, whose parameters `bodyEnv` binds. */
  private[raccoonlang] def metric(name: String, vpi: VPi, spec: CA.DecreaseSpec, bodyEnv: Env): Metric = {
    val provesProposition = vpi.tpe == PropTpe

    /** A metric must have an inductive type; a proof is `InvalidDecreaseSpec` for `proofRejection`, if one is given. */
    def requireInductiveMetric(value: Value, span: Span, proofRejection: Option[String]): Unit = {
      if (isProof(value)) proofRejection.foreach(reason => throw InvalidDecreaseSpec(reason, Some(span)))
      value.tpe match {
        case ConstSpine(VConst(_, Inductive(_), _), _) =>
        case _ => throw InvalidDecreaseSpec(s"decrease metric ${value} must have an inductive type", Some(span))
      }
    }

    spec match {
      case CA.DecreaseSpec.Lexicographic(args, sp) =>
        if (args.isEmpty) throw InvalidDecreaseSpec("lexicographic decreases needs at least one argument", Some(sp))
        if (args.distinct.length != args.length)
          throw InvalidDecreaseSpec("lexicographic decreases arguments must be distinct", Some(sp))

        val indices = args.map { ref =>
          vpi.binders.indices.find(idx => vpi.binders(idx).localRef.id == ref.id).getOrElse {
            throw InvalidDecreaseSpec(s"${ref.name} is not a function parameter", Some(sp))
          }
        }
        val proofRejection =
          Option.unless(provesProposition)(
            "decrease metrics in Prop are allowed only for functions returning a proposition"
          )
        args.foreach(ref => requireInductiveMetric(bodyEnv(ref), sp, proofRejection))
        new Metric(
          name,
          vpi,
          sp,
          indices.map(idx => vpi.binders(idx).name),
          env => args.map(ref => env(ref)),
          callArgs => indices.map(callArgs)
        )

      case CA.DecreaseSpec.Measure(term, sp) =>
        val initialMeasure = TypeChecker.checkTerm(term, bodyEnv)
        // Every call evaluates the measure again on its arguments without consuming them, so it is a read extent of
        // its own (L6), and its reads are no uses. A `structural` or `lexicographic` clause only names parameters.
        TypeChecker.readBoundary(initialMeasure.lin)
        val proofRejection = "decrease measures must live in Type; proofs in Prop cannot be used"
        requireInductiveMetric(initialMeasure.value, sp, Some(proofRejection))
        val quoted = initialMeasure.residual
        new Metric(
          name,
          vpi,
          sp,
          Vector("the measure"),
          env => Vector(Interpreter.evalTerm(quoted, env)),
          callArgs => Vector(Interpreter.evalTerm(quoted, BinderOps.instantiateFull(vpi.binders, vpi.env, callArgs)))
        )
    }
  }

  /**
   * The members of a mutual block compare their metrics component by component, so all have the same number of
   * components; that is all the block needs, since every component's order is one well-founded order on all values.
   */
  private[raccoonlang] def requireCompatible(metrics: Vector[Metric]): Unit =
    metrics.headOption.foreach { first =>
      metrics.find(_.componentNames.length != first.componentNames.length).foreach { other =>
        throw InvalidDecreaseSpec(
          s"the members of a mutual block decrease metrics of one length: ${first.name} has " +
            s"${first.componentNames.length} components and ${other.name} ${other.componentNames.length}",
          Some(other.span)
        )
      }
    }

  /**
   * The raw value a call from `caller` to `callee` runs while `caller` 's body is checked: it checks that the call
   * decreases and is otherwise a stuck application of `callee`, which only an application head may reference
   * (`LocalResidualPolicy.AppHeadOnly`). Each component's order is the one its current value takes: proofs by key, data
   * by conversion and structural descent. `callerBodyEnv` binds the caller's parameters; branch refinement materializes
   * it, so `current` reads the caller's arguments as the branch refined them.
   */
  private[raccoonlang] def rawRecursiveCall(callee: Metric, caller: Metric, callerBodyEnv: Env): VLam = {
    def checkDecrease(callArgs: Vector[Value], nativeEnv: Env): Unit = {
      val candidates = callee.atCall(callArgs)
      val roots = caller.current(nativeEnv)
      val decreasedAt = candidates.zip(roots).zip(callee.componentNames).find { case ((candidate, root), component) =>
        val (smaller, same) =
          if (isProof(root)) (isStrictSubproof(candidate, root), candidate.key == root.key)
          else (isStrictSubterm(candidate, root), ValueEquivalence.defEq(candidate, root))
        if (smaller) true
        else if (same) false
        else
          throw NonDecreasingRecursiveCall(
            callee.name,
            s"$component is neither equal to nor smaller than the current argument",
            None
          )
      }
      if (decreasedAt.isEmpty)
        throw NonDecreasingRecursiveCall(callee.name, "no lexicographic component decreases", None)
    }

    val vpi = callee.vpi
    VLam(
      vpi,
      ValueId.Const(callee.name),
      LamBody.Native(
        (args, nativeEnv) => {
          checkDecrease(args, nativeEnv)
          val envWithArgs = BinderOps.instantiateFull(vpi.binders, vpi.env, args)
          val resultTy = vpi.codomain(envWithArgs)
          VApp(VConst(callee.name, Symbol, vpi), args, resultTy)
        },
        callerBodyEnv,
        isRawRecursive = true
      )
    )
  }

  /** A recursive definition's raw self: the call from it to itself. */
  def rawRecursiveSelf(name: String, vpi: VPi, spec: CA.DecreaseSpec, bodyEnv: Env): VLam = {
    val own = metric(name, vpi, spec, bodyEnv)
    rawRecursiveCall(own, own, bodyEnv)
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
