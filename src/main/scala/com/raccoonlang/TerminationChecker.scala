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
   * A recursive function's metric: a tuple of components, ordered lexicographically, each by the order of the caller's
   * current value (`compare`): `<` on Nat, the structural subterm order on other data, and the proof field order on
   * proofs (docs/kernel.md, "Recursion on proofs"). `at` reads the components in an environment that binds the
   * function's parameters: a caller's body environment, refined in the branch the call is in, for its current values,
   * and the parameters instantiated at a call's arguments for the call's. A parameter component is the parameter's
   * value. A measure component is its term's value there, so it is evaluated again at each call; it reads its arguments
   * and consumes nothing (L6). A constant measure is a rank, which orders the members of a mutual block whose calls
   * keep the earlier components.
   */
  private[raccoonlang] final class Metric(
      val name: String,
      val vpi: VPi,
      val spec: CA.DecreaseSpec,
      val at: Env => Vector[Value]
  )

  /**
   * `spec`, checked as the metric of the function `name` of type `vpi`, whose parameters `bodyEnv` binds. Every
   * component has an inductive type. A parameter component may be a proof only in a function returning a proposition,
   * and a measure component is never one, as a `measure` clause never was (docs/kernel.md, "Recursion on proofs").
   */
  private[raccoonlang] def metric(name: String, vpi: VPi, spec: CA.DecreaseSpec, bodyEnv: Env): Metric = {
    val paramProofRejection =
      Option.unless(vpi.tpe == PropTpe)(
        "decrease metrics in Prop are allowed only for functions returning a proposition"
      )
    val measureProofRejection = Some("decrease measures must live in Type; proofs in Prop cannot be used")

    /** A metric must have an inductive type; a proof is `InvalidDecreaseSpec` for `proofRejection`, if one is given. */
    def requireInductiveMetric(value: Value, span: Span, proofRejection: Option[String]): Unit = {
      if (isProof(value)) proofRejection.foreach(reason => throw InvalidDecreaseSpec(reason, Some(span)))
      value.tpe match {
        case ConstSpine(VConst(_, Inductive(_), _), _) =>
        case _ => throw InvalidDecreaseSpec(s"decrease metric ${value} must have an inductive type", Some(span))
      }
    }

    val params = spec.components.collect { case CA.MetricComponent.Param(ref, _) => ref }
    if (params.distinct.length != params.length)
      throw InvalidDecreaseSpec("lexicographic decreases arguments must be distinct", Some(spec.span))

    // How to read each component in an environment that binds the parameters. The parser gives a clause at least one
    // component; a metric without any would refuse every call.
    val readers: Vector[Env => Value] = spec.components.map {
      case CA.MetricComponent.Param(ref, sp) =>
        if (!vpi.binders.exists(_.localRef.id == ref.id))
          throw InvalidDecreaseSpec(s"${ref.name} is not a function parameter", Some(sp))
        requireInductiveMetric(bodyEnv(ref), sp, paramProofRejection)
        env => env(ref)
      case CA.MetricComponent.Measure(term, sp) =>
        val initialMeasure = TypeChecker.checkTerm(term, bodyEnv)
        // Every call evaluates the measure again on its arguments without consuming them, so it is a read extent of
        // its own (L6), and its reads are no uses. A parameter component only names a parameter.
        TypeChecker.readBoundary(initialMeasure.lin)
        requireInductiveMetric(initialMeasure.value, sp, measureProofRejection)
        val quoted = initialMeasure.residual
        env => Interpreter.evalTerm(quoted, env)
    }
    new Metric(name, vpi, spec, env => readers.map(read => read(env)))
  }

  /**
   * The members of a mutual block compare their metrics component by component, so all have the same number of
   * components; that is all the block needs, since every component compares by one well-founded order on all values
   * (`compare`).
   */
  private[raccoonlang] def requireCompatible(metrics: Vector[Metric]): Unit =
    metrics.headOption.foreach { first =>
      def length(metric: Metric): Int = metric.spec.components.length
      metrics.find(length(_) != length(first)).foreach { other =>
        throw InvalidDecreaseSpec(
          s"the members of a mutual block decrease metrics of one length: ${first.name} has " +
            s"${length(first)} components and ${other.name} ${length(other)}",
          Some(other.spec.span)
        )
      }
    }

  /**
   * The raw value a call from `caller` to `callee` runs while `caller` 's body is checked: it checks that the call
   * decreases and is otherwise a stuck application of `callee`, which only an application head may reference
   * (`LocalResidualPolicy.AppHeadOnly`). Each component's order is the one its current value takes (`compare`).
   * `callerBodyEnv` binds the caller's parameters; branch refinement materializes it, so the caller's metric is read at
   * its arguments as the branch refined them. The callee's is read at the call's arguments, in the environment its
   * result type is computed in.
   */
  private[raccoonlang] def rawRecursiveCall(callee: Metric, caller: Metric, callerBodyEnv: Env): VLam = {
    def checkDecrease(calleeEnv: Env, nativeEnv: Env): Unit = {
      val candidates = callee.at(calleeEnv)
      val roots = caller.at(nativeEnv)
      val decreasedAt = candidates.zip(roots).zip(callee.spec.components).find { case ((candidate, root), component) =>
        compare(candidate, root) match {
          case Comparison.Smaller  => true
          case Comparison.NoLarger => false
          case Comparison.Neither =>
            throw NonDecreasingRecursiveCall(
              callee.name,
              s"${PrettyPrinter.printMetricComponent(component)} at the call is neither equal to nor smaller than the " +
                "caller's",
              None
            )
        }
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
          val envWithArgs = BinderOps.instantiateFull(vpi.binders, vpi.env, args)
          checkDecrease(envWithArgs, nativeEnv)
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

  /** How a call's metric component compares with the caller's current one, its root. */
  private sealed trait Comparison
  private object Comparison {

    /** Below the root: the call decreases at this component. */
    case object Smaller extends Comparison

    /** Equal to the root, or a Nat at most it: the comparison goes on to the next component. */
    case object NoLarger extends Comparison

    /** Neither: the call does not decrease. */
    case object Neither extends Comparison
  }

  /**
   * The order of a component is the one its root takes. A proof is below a proof it is a proof field of
   * (`isStrictSubproof`) and equal to one with its key. Other data is below a value it is a structural subterm of and
   * equal to one it converts with. A Nat is also below a Nat by `<`, and at most it by `<=`, decided on the normal
   * forms' signed difference as `Nat.ble` decides (`NatNormalForm.differenceBound`). The structural test comes first
   * and conversion second, so a call that the structural order alone accepts does no arithmetic.
   *
   * Every chain of calls descends, because every component compares by one relation on all values, the union of the
   * proof field order, the structural subterm order and `<` on Nat, and it is well-founded:
   *   - `<` on Nat is well-founded and contains the structural order on Nat, which removes known successors
   *     (`NatNormalForm.isStrictlySmaller`).
   *   - No value of another type is below a Nat: a Nat's structural subterms are Nats, since its only constructor with
   *     a field, `succ`, holds a Nat (its root is zero, a form, or an atom of a family without structure eta), a Nat is
   *     no proof, and `<` relates only Nats, since `differenceBound` checks both sides. So a descending chain that
   *     reaches a Nat descends by `<` from there on, and one that never does descends by the structural and proof field
   *     orders, which are well-founded.
   *   - Lexicographically, a prefix of components that are equal or at most the root's descends too: along a chain of
   *     calls the first component never increases, so it decreases only finitely often and is then constant, and the
   *     rest descend in turn.
   *   - What the forms decide holds at run time. A bound on the difference holds for every natural value of the forms'
   *     atoms, which are variables or opaque Nat-valued terms, so under every substitution of the variables, and so for
   *     the values the call runs with; and the root is read through the branch's refinement, which holds whenever the
   *     call runs.
   *   - A call's component is the root the callee reads when the call runs, so the chain the checks order is the chain
   *     of calls that runs. A parameter component is the call's argument. A measure is a checked term over the
   *     parameters alone, which names no member of the block, so evaluating it terminates and gives the same value at
   *     the call's arguments as when the callee runs on them. Where a component comes from does not enter the order, so
   *     a measure component, a constant rank among them, is ordered like any other value of its type.
   */
  private def compare(candidate: Value, root: Value): Comparison =
    if (isProof(root))
      if (isStrictSubproof(candidate, root)) Comparison.Smaller
      else if (candidate.key == root.key) Comparison.NoLarger
      else Comparison.Neither
    else if (isStrictSubterm(candidate, root)) Comparison.Smaller
    else if (ValueEquivalence.defEq(candidate, root)) Comparison.NoLarger
    else
      NatNormalForm.differenceBound(root, candidate) match {
        case Some(bound) if bound > 0 => Comparison.Smaller
        case Some(_)                  => Comparison.NoLarger
        case None                     => Comparison.Neither
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
