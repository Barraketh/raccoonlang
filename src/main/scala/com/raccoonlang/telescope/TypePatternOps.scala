package com.raccoonlang.telescope

import com.raccoonlang.CoreAst.{Term => CTerm, TypePattern => CPattern}
import com.raccoonlang.ElabAst.{Term => ETerm, TypePattern => EPattern}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang._

object TypePatternOps {
  private final case class OpenedApp[E <: EnvLike[E]](fn: Value, args: Vector[Value], env: E)

  private def requirePi(fn: Value)(implicit eqStore: EqStore): VPi =
    resolveInEqStore(fn.tpe) match {
      case pi: VPi => pi
      case other   => throw CannotApplyNonFunction(other)
    }

  private def compileType(pattern: ElabAst.TypePattern): ElabAst.TypeTerm = pattern match {
    case EPattern.Type(term)         => term
    case EPattern.Capture(ref, span) => ETerm.LocalRef(ref, span)
    case EPattern.App(fn, args, span) =>
      ETerm.App(fn, args.map(compileType), span)
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
    def checkPattern(pattern: CoreAst.TypePattern, env: TypecheckEnv): (ElabAst.TypePattern, Value, TypecheckEnv) =
      pattern match {
        case CPattern.Type(term) =>
          val checked = TypeChecker.checkTypeTerm(term, env)
          (EPattern.Type(checked.term), checked.value, env)
        case CPattern.Capture(ref, span) =>
          throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
        case CPattern.App(fn, args, span) =>
          val fnTerm = fn match {
            case CTerm.GlobalRef(name, span) => ETerm.GlobalRef(name, span)
            case CTerm.LocalRef(ref, span)   => ETerm.LocalRef(ref, span)
          }
          val fnV = evalTypeTerm(fnTerm, env)
          val pi = requirePi(fnV)
          val binders = pi.binders
          val explicitArgCount = binders.count(!_.isDerived)

          var argIdx = 0
          var callerEnv = env
          var calleeEnv = pi.env
          val argPatterns = Vector.newBuilder[ElabAst.TypePattern]
          val argValues = Vector.newBuilder[Value]

          binders.foreach { binder =>
            val (argPattern, argValue) =
              if (binder.isDerived) {
                val solved = BinderOps.solveBinder(calleeEnv, binder, env)
                val term = solved.term match {
                  case term: ElabAst.TypeTerm => EPattern.Type(term)
                  case other => throw WTF(s"Expected checked instance term to be usable in a type pattern, got $other")
                }
                (term, solved.value)
              } else {
                if (argIdx >= args.length) throw ArityMismatch(explicitArgCount, args.length, Some(span))
                val arg = args(argIdx)
                argIdx += 1

                arg match {
                  case CPattern.Capture(ref, captureSpan) =>
                    val (expected, _) = openPattern(calleeEnv, binder.ty)

                    val value = FreshVar.freshVar(ref.name, expected)
                    val pattern = EPattern.Capture(ref, captureSpan)
                    callerEnv = callerEnv.putLocal(ref, value)
                    (pattern, value)

                  case other =>
                    val (checkedPattern, checkedValue, checkedEnv) = checkPattern(other, callerEnv)
                    callerEnv = checkedEnv
                    (checkedPattern, checkedValue)
                }
              }

            calleeEnv = bindValueAndCheck(calleeEnv, binder, argValue)
            argPatterns += argPattern
            argValues += argValue
          }

          if (argIdx != args.length) throw ArityMismatch(explicitArgCount, args.length, Some(span))

          val checkedArgs = argPatterns.result()
          val pattern = EPattern.App(fnTerm, checkedArgs, span)
          (pattern, Interpreter.evalApply(fnV, argValues.result()), callerEnv)
      }

    val (pattern, _, checkedEnv) = checkPattern(binder.ty, env)
    val captures = collectCaptures(pattern)
    val resType = compileType(pattern)
    TypeChecker.assertType(Interpreter.evalTypeTerm(resType, checkedEnv))
    val checkedBinder = ElabAst.Binder(
      binder.localRef,
      pattern,
      binder.span,
      binder.isDerived,
      binder.isInstance
    )

    (
      VBinder(binder.localRef, pattern, resType, captures, binder.isDerived, binder.isInstance),
      checkedBinder
    )
  }

  def toVBinder(binder: ElabAst.Binder): VBinder = {
    val expectedTy = compileType(binder.ty)
    VBinder(
      binder.localRef,
      binder.ty,
      expectedTy,
      collectCaptures(binder.ty),
      binder.isDerived,
      binder.isInstance
    )
  }

  private def project(value: Value, path: List[Int])(implicit eqStore: EqStore): Value = {
    def projectStep(value: Value, idx: Int): Value =
      resolveInEqStore(value) match {
        case VSort(level) if idx == 0 => level
        case VApp(_, args, _)         => args.lift(idx).getOrElse(throw FailedToOpenCapture(value, idx))
        case VBlockedApp(_, args, _, _) =>
          args.lift(idx).getOrElse(throw FailedToOpenCapture(value, idx))
        case v: VCtor => v.fields.lift(idx).getOrElse(throw FailedToOpenCapture(value, idx))
        case _        => throw FailedToOpenCapture(value, idx)
      }

    path.foldLeft(resolveInEqStore(value)) { case (cur, nextIdx) => projectStep(cur, nextIdx) }
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
    val structShape = binder.expectedTy match {
      case ETerm.App(fn, args, _) => Some(Interpreter.evalTerm(fn, env) -> args)
      case ref: ETerm.Ref         => Some(Interpreter.evalTypeTerm(ref, env) -> Vector.empty[ElabAst.Term])
      case _                      => None
    }

    structShape.flatMap { case (headValue, argTerms) =>
      Interpreter.resolveInEqStore(headValue) match {
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
        BinderOps.putBinderLocal(refinedEnv, binder, fresh)

      case None =>
        val (opened, openedEnv) = openPattern(env, binder.ty)
        val value = FreshVar.freshVar(binder.name, opened)
        BinderOps.putBinderLocal(openedEnv, binder, value)
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
