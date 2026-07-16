package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA}

/** Termination checking uses a temporary raw-recursive value installed as a local while checking the body. */
object TerminationChecker {
  def rawRecursiveSelf(
      name: String,
      vpi: VPi,
      spec: CA.DecreaseSpec,
      bodyEnv: Env
  ): VLam = {
    def requireInductiveMetric(value: Value, span: Span): Unit = {
      // Proof structure is not invariant under an equality that identifies wrap(x) with base;
      // erased proofs also have no subterms. Well-founded recursion on proofs needs a
      // dedicated Acc-style mechanism (proof-collapse.md §6).
      if (Value.isPropositionType(value.tpe))
        throw InvalidDecreaseSpec(
          s"decrease metric ${value} is a proof; structural recursion on proofs is not supported",
          Some(span)
        )
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
          vpi.binders.indices.find(idx => vpi.binders(idx).localRef == ref).getOrElse {
            throw InvalidDecreaseSpec(s"${ref.name} is not a function parameter", Some(sp))
          }
        }
        args.map(ref => bodyEnv(ref)).foreach(requireInductiveMetric(_, sp))
        val refsWithIndices = args.zip(indices)

        (callArgs, nativeEnv) => {
          val decreasedAt = refsWithIndices.find { case (ref, idx) =>
            val root = nativeEnv.apply(ref)
            val candidate = callArgs(idx)
            if (isStrictSubterm(candidate, root)) true
            else if (ValueEquivalence.defEq(candidate, root)) false
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
          // A recursive call in a proof-by-recursion produces a proof of the instantiated goal;
          // a struct-returning one produces its residual in canonical constructor form.
          StructEta.expandIfStruct(Value.canonicalizeProof(VApp(VConst(name, Symbol, vpi), args, resultTy)))
        },
        bodyEnv,
        isRawRecursive = true
      )
    )
  }

  private def isStrictSubterm(candidate: Value, root: Value): Boolean =
    root match {
      case VCtor(_, fields, _) =>
        fields.exists { field =>
          applicationOfSubterm(candidate, field) ||
          isStrictSubterm(candidate, field)
        }
      case root: VPacked =>
        candidate match {
          case packed: VPacked if packed.codec == root.codec => root.codec.strictlyLess(packed, root)
          case _                                             => false
        }
      case _ => false
    }

  /**
   * The candidate is the field itself, or an application spine whose head is the field. A function-typed field of a
   * strictly positive inductive is its node's child-selector in the value's tree semantics, so any application of it is
   * a child — one level down the well-founded tree (kernel-theory §5, structural decrease). The order is well-founded
   * only while values are well-founded trees: strict positivity is enforced by InductiveChecks, and no value can
   * capture itself (recursion requires a decreasing parameter, so there is no value-level recursion). Only `VApp`
   * frames are stripped; any other candidate head must be defEq to the field itself, so descent never passes through a
   * blocked match, which could reduce to anything once unblocked.
   */
  private def applicationOfSubterm(candidate: Value, field: Value): Boolean =
    ValueEquivalence.defEq(candidate, field) || (candidate match {
      case VApp(head, _, _, _) => applicationOfSubterm(head, field)
      case _                   => false
    })
}
