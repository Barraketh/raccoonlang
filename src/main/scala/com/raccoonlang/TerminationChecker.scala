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
      bodyContext: TypingContext
  ): VLam = {
    val bodyEnv = bodyContext.env

    def requireInductiveMetric(value: Value, span: Span): Unit =
      value.tpe match {
        case ConstSpine(VConst(_, Inductive(_), _), _) =>
        case _ => throw InvalidDecreaseSpec(s"decrease metric ${value} must have an inductive type", Some(span))
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
            else if (ValueEquivalence.defEq(candidate, root, propIrrelevant = false)) false
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
        val initialMeasure = TypeChecker.checkTerm(term, bodyContext)
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

  private def isStrictSubterm(candidate: Value, root: Value): Boolean =
    root match {
      case VCtor(_, fields, _) =>
        fields.exists { field =>
          ValueEquivalence.defEq(candidate, field, propIrrelevant = false) ||
          isStrictSubterm(candidate, field)
        }
      case _ => false
    }
}
