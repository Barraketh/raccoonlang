package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA}

/**
 * Termination checking is done in the following way:
 *
 * Every recursive function must have a DecreaseSpec - otherwise a reference to it will not get installed in the Env,
 * and recursive calls will fail with a 'NotFound' error.
 *
 * If a function does have a DecreaseSpec, we will install a VLam() that when called verifies that the passed in
 * arguments are smaller than closed-over arguments. The important nuance here is that the existing closed-over args are
 * just fresh variables, so proving smallness is reliant on EqStore equations.
 *
 * Once we've verified that all calls to our VLam in the function body go through the 'smaller-than' verification check,
 * the only thing we have to ensure is that we don't accidentally smuggle our termination checker out of the function.
 * That is, we need to verify that
 *   - The function return doesn't contain our synthetic VLam
 *   - That any 'let' definitions in the body do not contain our VLam. This second condition is only required because we
 *     could have lets that call VLam() but then discard the value, which would not be caught by checking the function
 *     return
 *
 * Verifying that a value does not contain our VLam has two parts:
 *   - forbidEscapeRawRecursive scans a Value for raw-recursive VLams and throws if it finds one. Note that we can only
 *     have one raw-recursive VLam in the system at a time, so a simple Boolean on VLam is fine
 *   - [[ValueQuote]].quoteLam throws if the VLam is rawRecursive, which prevents neutrals from smuggling the recursive
 *     calls out.
 */
object TerminationChecker {
  def rawRecursiveSelf(name: String, vpi: VPi, spec: CA.DecreaseSpec, bodyEnv: TypecheckEnv, isStable: Boolean)(implicit
      eqStore: EqStore
  ): VLam = {
    def requireInductiveMetric(value: Value, span: Span): Unit = value.tpe.caseOf {
      case VConst(_, Inductive(_), _)             => true
      case VApp(VConst(_, Inductive(_), _), _, _) => true
      case _ => throw InvalidDecreaseSpec(s"decrease metric ${value} must have an inductive type", Some(span))
    }

    val checkDecrease: (Vector[Value], EqStore) => Unit = spec match {
      case CA.DecreaseSpec.Lexicographic(args, sp) =>
        if (args.isEmpty) throw InvalidDecreaseSpec("lexicographic decreases needs at least one argument", Some(sp))
        if (args.distinct.length != args.length)
          throw InvalidDecreaseSpec("lexicographic decreases arguments must be distinct", Some(sp))

        val indices = args.map { ref =>
          vpi.binders.indices.find(idx => vpi.binders(idx).localRef.id == ref.id).getOrElse {
            throw InvalidDecreaseSpec(s"${ref.name} is not a function parameter", Some(sp))
          }
        }
        val current = args.map(ref => bodyEnv(ref))
        current.foreach(requireInductiveMetric(_, sp))
        val indicesWithCur = current.zip(indices)

        (callArgs, store) => {
          val decreasedAt = indicesWithCur.find { case (root, idx) =>
            val candidate = callArgs(idx)
            if (isStrictSubterm(candidate, root, bodyEnv.normalizers)(store)) true
            else if (ValueEquivalence.defEq(candidate, root, bodyEnv.normalizers, propIrrelevant = false)(store)) false
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
        val measure = TypeChecker.check(term, bodyEnv)
        requireInductiveMetric(measure, sp)
        val quoted = ValueQuote.quoteTerm(measure, ValueQuote.quoteContext(bodyEnv), term.span)
        (args, store) => {
          val callEnv = BinderOps.instantiateFull(vpi.binders, vpi.env, args)(store)
          val candidate = Interpreter.evalTerm(quoted, callEnv)(store)
          if (!isStrictSubterm(candidate, measure, bodyEnv.normalizers)(store))
            throw NonDecreasingRecursiveCall(name, "measure does not structurally decrease", None)
        }
    }

    VLam(
      vpi,
      ValueId.Const(name),
      isStable,
      LamBody.Native(
        (args, store) => {
          checkDecrease(args, store)
          val envWithArgs = BinderOps.instantiateFull(vpi.binders, vpi.env, args)(store)
          val resultTy = vpi.codomain(envWithArgs, store)
          VApp(VConst(name, Symbol, vpi), args, resultTy)
        },
        isRawRecursive = true
      )
    )
  }

  private def isStrictSubterm(candidate: Value, root: Value, normalizers: Normalizers.NormalizerMap)(implicit
      eqStore: EqStore
  ): Boolean = root.caseOf {
    case ctor: VCtor =>
      ctor.fields.exists { field =>
        ValueEquivalence.defEq(candidate, field, normalizers, propIrrelevant = false) ||
        isStrictSubterm(candidate, field, normalizers)
      }
    case _ => false
  }

  def forbidEscapedRawRecursive(value: Value, span: Span)(implicit eqStore: EqStore): Unit =
    findRawRecursive(value).foreach { name =>
      throw InvalidRecursiveOccurrence(name, "raw recursive self escapes the recursive body", Some(span))
    }

  private def findRawRecursive(value: Value)(implicit eqStore: EqStore): Option[String] = {
    def first(values: IterableOnce[Value]): Option[String] = values.iterator
      .map(loop)
      .collectFirst { case Some(name) => name }

    def inRuntimeEnv(env: RuntimeEnv): Option[String] = first(env.locals.iterator.flatMap(_.valueOption))

    def inId(id: ValueId): Option[String] = id match {
      case ValueId.LocalId(_, captures) => first(captures)
      case ValueId.Const(_)             => None
    }

    def loop(value: Value): Option[String] = {
      val resolved = Interpreter.resolveInEqStore(value).value
      resolved match {
        case VLam(_, ValueId.Const(name), _, LamBody.Native(_, true)) => return Some(name)
        case _                                                        =>
      }

      resolved match {
        case VConst(_, _, tpe) => loop(tpe)
        case app: AppliedValue =>
          loop(app.head)
            .orElse(first(app.args))
            .orElse(loop(app.tpe))
        case ctor: VCtor => first(ctor.args).orElse(loop(ctor.tpe))
        case neutral: NeutralThunk =>
          (neutral.body match {
            case ThunkBody.Match(_, env) => inRuntimeEnv(env)
          })
            .orElse(inId(neutral.id))
            .orElse(loop(neutral.tpe))
        case Var(_, _, tpe) => loop(tpe)
        case lam: VLam =>
          loop(lam.tpe)
            .orElse(inId(lam.id))
            .orElse {
              lam.body match {
                case LamBody.Core(_, env) => inRuntimeEnv(env)
                case LamBody.Native(_, _) => None
              }
            }
        case pi: VPi =>
          inRuntimeEnv(pi.env)
            .orElse(inId(pi.id))
            .orElse(loop(pi.tpe))
        case ConstructorHead(_, _, _, tpe)                                     => loop(tpe)
        case n: Normalizer                                                     => first(n.dependencies)
        case _: Universe | _: Level | LevelTpe | NormalizerType | KernelObject => None
      }
    }

    loop(value)
  }
}
