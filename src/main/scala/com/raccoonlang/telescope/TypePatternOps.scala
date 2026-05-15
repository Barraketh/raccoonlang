package com.raccoonlang.telescope

import com.raccoonlang.CoreAst.{TypePattern => CPattern}
import com.raccoonlang.ElabAst.{Term => ETerm, TypePattern => EPattern}
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

  private def collectCaptures(pattern: ElabAst.TypePattern): Vector[VCapture] = {
    def compileLevelCapture(pattern: ElabAst.TypePattern): Option[VCapture] =
      pattern match {
        case EPattern.Capture(ref, _) => Some(VCapture(ref, 0 :: Nil, LevelCapture(0)))
        case EPattern.App(ETerm.GlobalRef("Level::succ", _), args, _) =>
          compileLevelCapture(args.head).map {
            case c @ VCapture(_, _, LevelCapture(subtract)) => c.copy(captureType = LevelCapture(subtract + 1))
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
              collectCaptures(nested).map(capture => capture.copy(path = idx :: capture.path))
            case EPattern.Capture(localRef, _) => Vector(VCapture(localRef, idx :: Nil, StructuralCapture))
          }
        }

      case _ => Vector.empty
    }
  }

  private[telescope] def toVBinder(binder: CoreAst.Binder, env: TypecheckEnv)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): (VBinder, ElabAst.Binder) = {
    def checkPattern(pattern: CoreAst.TypePattern, env: TypecheckEnv): (ElabAst.TypePattern, TypecheckEnv) =
      pattern match {
        case CPattern.Type(term) =>
          val checked = TypeChecker.checkTypeTerm(term, env)
          (EPattern.Type(checked.term), env)
        case CPattern.Capture(ref, span) => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
        case CPattern.App(fn, args, span) =>
          val (fnV, fnTerm) = TypeChecker.checkRef(fn, env)
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
                  val (expected, _) = openPattern(telescopeEnv, paramBinder.ty)

                  val value = FreshVar.freshVar(ref.name, expected)
                  patternEnv = patternEnv.putLocal(ref, value)
                  EPattern.Capture(ref, captureSpan)

                case other =>
                  val (checkedPattern, checkedEnv) = checkPattern(other, patternEnv)
                  patternEnv = checkedEnv
                  checkedPattern
              }

            val argValue = Interpreter.evalTypeTerm(compileType(argPattern), patternEnv)
            telescopeEnv = bindValueAndCheck(telescopeEnv, paramBinder, argValue)
            argPatterns += argPattern
          }

          val checkedArgs = argPatterns.result()
          val pattern = EPattern.App(fnTerm, checkedArgs, span)
          (pattern, patternEnv)
      }

    val (pattern, checkedEnv) = checkPattern(binder.ty, env)
    val captures = collectCaptures(pattern)
    val resType = compileType(pattern)
    TypeChecker.assertType(Interpreter.evalTypeTerm(resType, checkedEnv))
    val checkedBinder = ElabAst.Binder(binder.localRef, pattern, binder.span, binder.isInstance)

    (
      VBinder(binder.localRef, pattern, resType, captures, binder.isInstance),
      checkedBinder
    )
  }

  def toVBinder(binder: ElabAst.Binder): VBinder = {
    val expectedTy = compileType(binder.ty)
    VBinder(binder.localRef, binder.ty, expectedTy, collectCaptures(binder.ty), binder.isInstance)
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
      val captureValue = capture.captureType match {
        case StructuralCapture => project(actualTy, capture.path)
        case LevelCapture(subtract) =>
          val projected = Interpreter.getLevel(project(actualTy, capture.path))
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
          val (expected, _) = openPattern(calleeEnv, binder.ty)

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

  private[telescope] def freshenBinder[E <: EnvLike[E]](env: E, binder: VBinder)(implicit
      eqStore: EqStore
  ): E = {
    def putBinderLocal(env: E, value: Value): E = {
      val instanceKey =
        if (binder.isInstance) Some(InstanceSearch.instanceKey(binder.name, value, eqStore))
        else None
      env.putLocal(binder.localRef, value, instanceKey)
    }

    val structShape = binder.expectedTy match {
      case ETerm.App(fn, args, _) => Some(Interpreter.evalTerm(fn, env) -> args)
      case ref: ETerm.Ref         => Some(Interpreter.evalTypeTerm(ref, env) -> Vector.empty[ElabAst.Term])
      case _                      => None
    }

    structShape.flatMap { case (headValue, argTerms) =>
      headValue.caseOf {
        case VConst(_, Inductive(meta), _) if meta.isStruct =>
          env(meta.constructorNames.head) match {
            case head: ConstructorHead => ConstructorOps.ConstructorShape.from(head).map(_ -> argTerms)
            case other                 => throw WTF(s"Expected constructor head, got $other")
          }
        case _ => None
      }
    } match {
      case Some((shape, argTerms)) =>
        val args = binder.ty match {
          case app: EPattern.App =>
            val opened = openPatternPrefix(env, app, shape.paramCount)
            opened.args
          case _ => shape.paramArgs(argTerms).map(arg => Interpreter.evalTerm(arg, env))
        }
        val fresh = ConstructorOps.freshFromParams(shape.head, args)
        val refinedEnv = openCaptures(env, binder.captures, fresh.tpe)
        putBinderLocal(refinedEnv, fresh)

      case None =>
        val (opened, openedEnv) = openPattern(env, binder.ty)
        val value = FreshVar.freshVar(binder.name, opened)
        putBinderLocal(openedEnv, value)
    }
  }

  def bindValue(env: RuntimeEnv, binder: VBinder, actual: Value)(implicit eqStore: EqStore): RuntimeEnv = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    openedEnv.putLocal(binder.localRef, actual)
  }

  private[telescope] def bindValueAndCheck(env: RuntimeEnv, binder: VBinder, actual: Value)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): RuntimeEnv = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    val expectedTy = Interpreter.evalTypeTerm(binder.expectedTy, openedEnv)
    TypeChecker.checkType(actual, expectedTy)
    openedEnv.putLocal(binder.localRef, Value.ascribe(actual, expectedTy))
  }

}
