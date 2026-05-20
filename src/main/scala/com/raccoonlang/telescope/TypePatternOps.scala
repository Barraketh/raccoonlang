package com.raccoonlang.telescope

import com.raccoonlang.CoreAst.{Term, BinderType => CBinderType, TypePattern => CPattern}
import com.raccoonlang.ElabAst.{BinderType => EBinderType, Term => ETerm, TypePattern => EPattern}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang._

object TypePatternOps {
  private final case class OpenedApp[E <: EnvLike[E]](fn: Value, args: Vector[Value], env: E)

  private def requirePi(fn: Value)(implicit eqStore: EqStore): VPi =
    fn.tpe.caseOf {
      case pi: VPi => pi
      case other   => throw CannotApplyNonFunction(other)
    }

  private def compileType(pattern: ElabAst.TypePattern): ElabAst.TypeTerm = pattern match {
    case EPattern.Type(term)          => term
    case EPattern.Capture(ref, span)  => ETerm.LocalRef(ref, span)
    case EPattern.App(fn, args, span) => ETerm.App(fn, args.map(compileType), span)
  }

  private def compileBinderType(binderType: ElabAst.BinderType): ElabAst.TypeTerm =
    binderType match {
      case EBinderType.TypePattern(tp, _)               => compileType(tp)
      case EBinderType.ConstrainedCapture(ref, _, span) => ETerm.LocalRef(ref, span)
    }

  private def collectCaptures(pattern: ElabAst.TypePattern, root: CaptureRoot = ActualType): Vector[VCapture] = {
    def compileLevelCapture(pattern: ElabAst.TypePattern): Option[VCapture] =
      pattern match {
        case EPattern.Capture(ref, _) => Some(VCapture(ref, 0 :: Nil, LevelCapture(0), root))
        case EPattern.App(ETerm.GlobalRef("Level.succ", _), args, _) =>
          compileLevelCapture(args.head).map {
            case c @ VCapture(_, _, LevelCapture(subtract), _) => c.copy(captureType = LevelCapture(subtract + 1))
            case _ => throw WTF("Expected a level capture while compiling a level pattern")
          }
        case _ => None
      }

    pattern match {
      case EPattern.App(ETerm.GlobalRef("Sort", _), args, _) => compileLevelCapture(args.head).toVector

      case app: EPattern.App =>
        app.args.zipWithIndex.flatMap { case (next, idx) =>
          next match {
            case EPattern.Type(_) => Vector.empty
            case nested: EPattern.App =>
              collectCaptures(nested, root).map(capture => capture.copy(path = idx :: capture.path))
            case EPattern.Capture(localRef, _) => Vector(VCapture(localRef, idx :: Nil, StructuralCapture, root))
          }
        }

      case _ => Vector.empty
    }
  }

  private def collectBinderCaptures(binderType: ElabAst.BinderType): Vector[VCapture] =
    binderType match {
      case EBinderType.TypePattern(tp, _) => collectCaptures(tp)
      case EBinderType.ConstrainedCapture(ref, constraint, _) =>
        collectCaptures(constraint, ActualTypeClassifier) :+ VCapture(ref, Nil, StructuralCapture, ActualType)
    }

  private def toElabRef(caRef: CoreAst.Term.Ref): ElabAst.Term.Ref = caRef match {
    case Term.GlobalRef(name, span) => ElabAst.Term.GlobalRef(name, span)
    case Term.LocalRef(ref, span)   => ElabAst.Term.LocalRef(ref, span)
  }

  private[telescope] def toVBinder(binder: CoreAst.Binder, env: TypecheckEnv)(implicit
      eqStore: EqStore
  ): (VBinder, ElabAst.Binder) = {
    def checkPattern(pattern: CoreAst.TypePattern, env: TypecheckEnv): (ElabAst.TypePattern, TypecheckEnv) = {
      pattern match {
        case CPattern.Type(term) =>
          val checked = TypeChecker.checkTypeTerm(term, env)
          val quoteCtx = ValueQuote.quoteContext(env)
          (EPattern.Type(ValueQuote.quoteType(checked, quoteCtx, term.span)), env)
        case CPattern.Capture(ref, span) => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
        case CPattern.App(fn, args, span) =>
          val fnV = TypeChecker.checkRef(fn, env)
          val pi = requirePi(fnV)
          val binders = pi.binders

          if (binders.length != args.length) throw ArityMismatch(binders.length, args.length, Some(span))

          var patternEnv = env
          var telescopeEnv = pi.env
          val argPatterns = Vector.newBuilder[ElabAst.TypePattern]

          binders.zip(args).foreach { case (paramBinder, arg) =>
            val argPattern =
              arg match {
                case CPattern.Capture(ref, captureSpan) =>
                  val (expected, _) = openBinderType(telescopeEnv, paramBinder.ty)

                  val value = FreshVar.freshVar(ref.name, expected)
                  patternEnv = patternEnv.putLocal(ref, value)
                  EPattern.Capture(ref, captureSpan)

                case other =>
                  val (checkedPattern, checkedEnv) = checkPattern(other, patternEnv)
                  patternEnv = checkedEnv
                  checkedPattern
              }

            val argValue = Interpreter.evalTypeTerm(compileType(argPattern), patternEnv)
            telescopeEnv = bindValueAndCheck(telescopeEnv, paramBinder, argValue, patternEnv.normalizers)
            argPatterns += argPattern
          }

          val checkedArgs = argPatterns.result()
          val pattern = EPattern.App(toElabRef(fn), checkedArgs, span)
          (pattern, patternEnv)
      }
    }

    def checkTopLevel(pattern: CoreAst.TopLevelTP, env: TypecheckEnv): (ElabAst.TopLevelTP, TypecheckEnv) = {
      val (checked, checkedEnv) = checkPattern(pattern, env)
      checked match {
        case topLevel: ElabAst.TopLevelTP => (topLevel, checkedEnv)
        case EPattern.Capture(ref, span)  => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
      }
    }

    def checkBinderType(binderType: CoreAst.BinderType, env: TypecheckEnv): (ElabAst.BinderType, TypecheckEnv) =
      binderType match {
        case CBinderType.TypePattern(tp, span) =>
          val (checked, checkedEnv) = checkTopLevel(tp, env)
          (EBinderType.TypePattern(checked, span), checkedEnv)

        case CBinderType.ConstrainedCapture(ref, constraint, span) =>
          val (checkedConstraint, constraintEnv) = checkTopLevel(constraint, env)
          val constraintTy = compileType(checkedConstraint)
          val constraintValue = Interpreter.evalTypeTerm(constraintTy, constraintEnv)
          TypeChecker.assertType(constraintValue)
          val captureValue = FreshVar.freshVar(ref.name, constraintValue)
          val checkedEnv = constraintEnv.putLocal(ref, captureValue)
          (EBinderType.ConstrainedCapture(ref, checkedConstraint, span), checkedEnv)
      }

    val (binderType, checkedEnv) = checkBinderType(binder.ty, env)
    val captures = collectBinderCaptures(binderType)
    val resType = compileBinderType(binderType)
    TypeChecker.assertType(Interpreter.evalTypeTerm(resType, checkedEnv))
    val checkedBinder = ElabAst.Binder(binder.localRef, binderType, binder.span, binder.isInstance)

    (
      VBinder(binder.localRef, binderType, resType, captures, binder.isInstance),
      checkedBinder
    )
  }

  def toVBinder(binder: ElabAst.Binder): VBinder = {
    val expectedTy = compileBinderType(binder.ty)
    VBinder(binder.localRef, binder.ty, expectedTy, collectBinderCaptures(binder.ty), binder.isInstance)
  }

  private def project(value: Value, path: List[Int])(implicit eqStore: EqStore): Value = {
    def projectStep(value: Value, idx: Int): Value =
      value.caseOf {
        case VSort(level) if idx == 0 => level
        case VApp(_, args, _)         => args.lift(idx).getOrElse(throw FailedToOpenCapture(value, idx))
        case VBlockedApp(_, args, _, _) =>
          args.lift(idx).getOrElse(throw FailedToOpenCapture(value, idx))
        case v: VCtor => v.fields.lift(idx).getOrElse(throw FailedToOpenCapture(value, idx))
        case _        => throw FailedToOpenCapture(value, idx)
      }

    path.foldLeft(value) { case (cur, nextIdx) => projectStep(cur, nextIdx) }
  }

  private def openCaptures[E <: EnvLike[E]](env: E, captures: Vector[VCapture], actualTy: Value)(implicit
      eqStore: EqStore
  ): E = {
    captures.foldLeft(env) { (curEnv, capture) =>
      val root = capture.root match {
        case ActualType           => actualTy
        case ActualTypeClassifier => actualTy.tpe
      }
      val captureValue = capture.captureType match {
        case StructuralCapture => project(root, capture.path)
        case LevelCapture(subtract) =>
          val projected = Interpreter.getLevel(project(root, capture.path))
          if (!Level.geq(projected, subtract)) throw InvalidLevelSubtraction(projected, subtract)
          Level.addOffset(projected, -subtract)
      }
      curEnv.putLocal(capture.localRef, captureValue)
    }
  }

  private def openPatternPrefix[E <: EnvLike[E]](env: E, app: EPattern.App, argCount: Int)(implicit
      eqStore: EqStore
  ): OpenedApp[E] = {
    val fnV = evalTypeTerm(app.fn, env)
    val pi = requirePi(fnV)
    val binders = pi.binders
    val args = app.args

    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length, Some(app.span))

    var callerEnv: E = env
    var calleeEnv: RuntimeEnv = pi.env
    val argValues = Vector.newBuilder[Value]

    binders.zip(args).take(argCount).foreach { case (binder, arg) =>
      val argValue = arg match {
        case EPattern.Capture(ref, _) =>
          val (expected, _) = openBinderType(calleeEnv, binder.ty)

          val value = FreshVar.freshVar(ref.name, expected)
          callerEnv = callerEnv.putLocal(ref, value)
          value

        case other =>
          val (openedArg, openedEnv) = openPattern(callerEnv, other)
          callerEnv = openedEnv
          openedArg
      }
      calleeEnv = bindValue(calleeEnv, binder, argValue)
      argValues += argValue
    }

    OpenedApp(fnV, argValues.result(), callerEnv)
  }

  private def openPattern[E <: EnvLike[E]](env: E, pattern: ElabAst.TypePattern)(implicit
      eqStore: EqStore
  ): (Value, E) =
    pattern match {
      case app: EPattern.App =>
        val opened = openPatternPrefix(env, app, app.args.length)
        (Interpreter.evalApply(opened.fn, opened.args), opened.env)
      case EPattern.Capture(ref, span) => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
      case EPattern.Type(term)         => (evalTypeTerm(term, env), env)
    }

  private def openBinderType[E <: EnvLike[E]](env: E, binderType: ElabAst.BinderType)(implicit
      eqStore: EqStore
  ): (Value, E) =
    binderType match {
      case EBinderType.TypePattern(tp, _) => openPattern(env, tp)
      case EBinderType.ConstrainedCapture(ref, constraint, _) =>
        val (constraintValue, constraintEnv) = openPattern(env, constraint)
        val captureValue = FreshVar.freshVar(ref.name, constraintValue)
        (captureValue, constraintEnv.putLocal(ref, captureValue))
    }

  private[telescope] def freshenBinder[E <: EnvLike[E]](env: E, binder: VBinder)(implicit
      eqStore: EqStore
  ): E = {
    val (opened, openedEnv) = openBinderType(env, binder.ty)
    val value = FreshVar.freshVar(binder.name, opened)
    val instanceKey =
      if (binder.isInstance) Some(InstanceSearch.instanceKey(binder.name, value, eqStore))
      else None
    openedEnv.putLocal(binder.localRef, value, instanceKey)
  }

  def bindValue(env: RuntimeEnv, binder: VBinder, actual: Value)(implicit eqStore: EqStore): RuntimeEnv = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    openedEnv.putLocal(binder.localRef, actual)
  }

  private[telescope] def bindValueAndCheck(
      env: RuntimeEnv,
      binder: VBinder,
      actual: Value,
      normalizerMap: Normalizers.NormalizerMap
  )(implicit
      eqStore: EqStore
  ): RuntimeEnv = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    val expectedTy = Interpreter.evalTypeTerm(binder.expectedTy, openedEnv)
    binder.ty match {
      case EBinderType.ConstrainedCapture(_, constraint, _) =>
        val constraintTy = Interpreter.evalTypeTerm(compileType(constraint), openedEnv)
        TypeChecker.checkType(expectedTy, constraintTy, normalizerMap)
      case _ =>
    }
    TypeChecker.checkType(actual, expectedTy, normalizerMap)
    openedEnv.putLocal(binder.localRef, Value.ascribe(actual, expectedTy))
  }

}
