package com.raccoonlang.telescope

import com.raccoonlang.CoreAst.{Term => CTerm, TypePattern => CPattern}
import com.raccoonlang.ElabAst.{Term => ETerm, TypePattern => EPattern}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang._

object TypePatternOps {
  private[telescope] final case class FreshenedBinder[E <: EnvLike[E]](value: Value, env: E, newVars: DepSet)
  private[telescope] final case class FreshenedRawBinder(
      value: Value,
      env: TypecheckEnv,
      newVars: DepSet,
      binder: VBinder,
      checkedBinder: ElabAst.Binder
  )
  private final case class OpenedPattern[E <: EnvLike[E]](value: Value, env: E, newVars: DepSet)
  private final case class OpenedApp[E <: EnvLike[E]](fn: Value, args: Vector[Value], env: E, newVars: DepSet)
  private final case class CheckedPattern(
      pattern: ElabAst.TypePattern,
      value: Value,
      env: TypecheckEnv,
      newVars: DepSet
  ) {
    def expectedTy: ElabAst.TypeTerm = compileType(pattern)
  }
  private final case class CheckedBinder(binder: VBinder, checkedBinder: ElabAst.Binder)

  private def toCheckedRef(ref: CoreAst.Term.Ref): ElabAst.Term.Ref = ref match {
    case CTerm.GlobalRef(name, span) => ETerm.GlobalRef(name, span)
    case CTerm.LocalRef(ref, span)   => ETerm.LocalRef(ref, span)
  }

  private def globalName(ref: ElabAst.Term.Ref): Option[String] = ref match {
    case ETerm.GlobalRef(name, _) => Some(name)
    case ETerm.LocalRef(_, _)     => None
  }

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

  private def checkedTermAsTypeTerm(term: ElabAst.Term): ElabAst.TypeTerm =
    term match {
      case term: ElabAst.TypeTerm => term
      case other => throw WTF(s"Expected checked instance term to be usable in a type pattern, got $other")
    }

  private def checkedTermAsTypePattern(term: ElabAst.Term): ElabAst.TypePattern =
    EPattern.Type(checkedTermAsTypeTerm(term))

  private def compileLevelCapture(pattern: ElabAst.TypePattern): Option[VCapture] =
    pattern match {
      case EPattern.Capture(ref, _) => Some(VCapture(ref, 0 :: Nil, LevelCapture(0)))
      case EPattern.App(fn, args, _) if globalName(fn).contains("Level::succ") =>
        compileLevelCapture(args.head).map {
          case c @ VCapture(_, _, LevelCapture(subtract)) => c.copy(captureType = LevelCapture(subtract + 1))
          case _ => throw WTF("Expected a level capture while compiling a level pattern")
        }
      case _ => None
    }

  private def collectCaptures(pattern: ElabAst.TypePattern): Vector[VCapture] =
    pattern match {
      case EPattern.App(fn, args, _) if globalName(fn).contains("Sort") => compileLevelCapture(args.head).toVector

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

  private def checkPattern(pattern: CoreAst.TypePattern, env: TypecheckEnv)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): CheckedPattern =
    pattern match {
      case CPattern.Type(term) =>
        val checked = TypeChecker.checkTypeTerm(term, env)
        CheckedPattern(EPattern.Type(checked.term), checked.value, env, DepSet.empty)
      case CPattern.Capture(ref, span) =>
        throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
      case CPattern.App(fn, args, span) =>
        checkPatternApp(fn, args, span, env)
    }

  private def checkPatternApp(
      fn: CoreAst.Term.Ref,
      args: Vector[CoreAst.TypePattern],
      span: Span,
      env: TypecheckEnv
  )(implicit eqStore: EqStore, normalizers: NormalizerMap): CheckedPattern = {
    val fnTerm = toCheckedRef(fn)
    val fnV = evalTypeTerm(fnTerm, env)
    val pi = requirePi(fnV)
    val binders = pi.binders
    val explicitArgCount = binders.count(!_.isDerived)

    var argIdx = 0
    var callerEnv = env
    var calleeEnv = pi.env
    val argPatterns = Vector.newBuilder[ElabAst.TypePattern]
    val argValues = Vector.newBuilder[Value]
    val newVars = DepSet.newBuilder

    binders.foreach { binder =>
      val (argPattern, argValue) =
        if (binder.isDerived) {
          val solved = BinderOps.solveBinder(calleeEnv, binder, env)
          val term = checkedTermAsTypePattern(solved.term)
          (term, solved.value)
        } else {
          if (argIdx >= args.length) throw ArityMismatch(explicitArgCount, args.length, Some(span))
          val arg = args(argIdx)
          argIdx += 1

          arg match {
            case CPattern.Capture(ref, captureSpan) =>
              val expected = openPattern(calleeEnv, binder.ty)
              newVars.unionInPlace(expected.newVars)

              val value = FreshVar.freshVar(ref.name, expected.value)
              val pattern = EPattern.Capture(ref, captureSpan)
              callerEnv = callerEnv.putLocal(ref, value)
              newVars.add(value.id)
              (pattern, value)

            case other =>
              val checked = checkPattern(other, callerEnv)
              callerEnv = checked.env
              newVars.unionInPlace(checked.newVars)
              (checked.pattern, checked.value)
          }
        }

      calleeEnv = bindValueAndCheck(calleeEnv, binder, argValue)
      argPatterns += argPattern
      argValues += argValue
    }

    if (argIdx != args.length) throw ArityMismatch(explicitArgCount, args.length, Some(span))

    val checkedArgs = argPatterns.result()
    val pattern = EPattern.App(fnTerm, checkedArgs, span)
    CheckedPattern(pattern, Interpreter.evalApply(fnV, argValues.result()), callerEnv, newVars.result())
  }

  private def checkBinder(binder: CoreAst.Binder, env: TypecheckEnv)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): CheckedBinder = {
    val checked = checkPattern(binder.ty, env)
    val pattern = checked.pattern
    val captures = collectCaptures(pattern)
    val resType = checked.expectedTy
    TypeChecker.assertType(Interpreter.evalTypeTerm(resType, checked.env))
    val checkedBinder = ElabAst.Binder(
      binder.localRef,
      pattern,
      binder.span,
      binder.isDerived,
      binder.isInstance
    )

    CheckedBinder(
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

  private def projectStep(value: Value, idx: Int)(implicit eqStore: EqStore): Value =
    resolveInEqStore(value) match {
      case VSort(level) if idx == 0 => level
      case VApp(_, args, _)         => args.lift(idx).getOrElse(throw FailedToOpenCapture(value, idx))
      case VBlockedApp(_, args, _, _) =>
        args.lift(idx).getOrElse(throw FailedToOpenCapture(value, idx))
      case v: VCtor => v.fields.lift(idx).getOrElse(throw FailedToOpenCapture(value, idx))
      case _        => throw FailedToOpenCapture(value, idx)
    }

  private def project(value: Value, path: List[Int])(implicit eqStore: EqStore): Value =
    path.foldLeft(resolveInEqStore(value)) { case (cur, nextIdx) => projectStep(cur, nextIdx) }

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

  private def structConstructorForBinderType[E <: EnvLike[E]](env: E, binderTy: ElabAst.TypeTerm)(implicit
      eqStore: EqStore
  ): Option[(ConstructorOps.ConstructorShape, Vector[ElabAst.Term])] = {
    val (headValue, argTerms) = binderTy match {
      case ETerm.App(fn, args, _) => (Interpreter.evalTerm(fn, env), args)
      case ref: ETerm.Ref         => (Interpreter.evalTypeTerm(ref, env), Vector.empty)
      case _                      => return None
    }

    Interpreter.resolveInEqStore(headValue) match {
      case VConst(_, Inductive(meta), _) if meta.isStruct =>
        env(meta.constructorNames.head) match {
          case head: ConstructorHead => ConstructorOps.ConstructorShape.from(head).map(_ -> argTerms)
          case other                 => throw WTF(s"Expected constructor head, got $other")
        }
      case _ => None
    }
  }

  private def freshenStructBinder[E <: EnvLike[E]](
      env: E,
      binder: VBinder,
      shape: ConstructorOps.ConstructorShape,
      argTerms: Vector[ElabAst.Term]
  )(implicit eqStore: EqStore): FreshenedBinder[E] = {
    val (args, newVars) = binder.ty match {
      case app: EPattern.App =>
        val opened = openPatternPrefix(env, app, shape.paramCount)
        (opened.args, opened.newVars)
      case _ =>
        (shape.paramArgs(argTerms).map(arg => Interpreter.evalTerm(arg, env)), DepSet.empty)
    }
    val fresh = ConstructorOps.freshFromParams(shape.head, args)
    val refinedEnv = openCaptures(env, binder.captures, fresh.value.tpe)
    FreshenedBinder(fresh.value, refinedEnv, newVars ++ fresh.newVars)
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
    val newVars = DepSet.newBuilder

    binders.zip(args).take(argCount).foreach { case (binder, arg) =>
      val argValue = arg match {
        case EPattern.Capture(ref, _) =>
          val expected = openPattern(calleeEnv, binder.ty)
          newVars.unionInPlace(expected.newVars)

          val value = FreshVar.freshVar(ref.name, expected.value)
          callerEnv = callerEnv.putLocal(ref, value)
          newVars.add(value.id)
          value

        case other =>
          val openedArg = openPattern(callerEnv, other)
          callerEnv = openedArg.env
          newVars.unionInPlace(openedArg.newVars)
          openedArg.value
      }
      calleeEnv = bindValue(calleeEnv, binder, argValue)
      argValues += argValue
    }

    OpenedApp(fnV, argValues.result(), callerEnv, newVars.result())
  }

  private def openPattern[E <: EnvLike[E]](env: E, pattern: ElabAst.TypePattern)(implicit
      eqStore: EqStore
  ): OpenedPattern[E] =
    pattern match {
      case app: EPattern.App =>
        val opened = openPatternPrefix(env, app, app.args.length)
        OpenedPattern(Interpreter.evalApply(opened.fn, opened.args), opened.env, opened.newVars)
      case EPattern.Capture(ref, span) => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
      case EPattern.Type(term)         => OpenedPattern(evalTypeTerm(term, env), env, DepSet.empty)
    }

  private[telescope] def freshenBinder[E <: EnvLike[E]](env: E, binder: VBinder)(implicit
      eqStore: EqStore
  ): FreshenedBinder[E] = {
    structConstructorForBinderType(env, binder.expectedTy) match {
      case Some((shape, argTerms)) => freshenStructBinder(env, binder, shape, argTerms)
      case None =>
        val opened = openPattern(env, binder.ty)
        val value = FreshVar.freshVar(binder.name, opened.value)
        FreshenedBinder(value, opened.env, opened.newVars + value.id)
    }
  }

  private[telescope] def freshenRawBinder(env: TypecheckEnv, binder: CoreAst.Binder)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): FreshenedRawBinder = {
    val checked = checkBinder(binder, env)
    val fresh = freshenBinder(env, checked.binder)
    FreshenedRawBinder(fresh.value, fresh.env, fresh.newVars, checked.binder, checked.checkedBinder)
  }

  def bindValue(
      env: RuntimeEnv,
      binder: VBinder,
      actual: Value
  )(implicit eqStore: EqStore): RuntimeEnv = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    openedEnv.putLocal(binder.localRef, actual)
  }

  private[telescope] def bindValueAndCheck(
      env: RuntimeEnv,
      binder: VBinder,
      actual: Value
  )(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): RuntimeEnv = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    val expectedTy = Interpreter.evalTypeTerm(binder.expectedTy, openedEnv)
    TypeChecker.checkType(actual, expectedTy)
    openedEnv.putLocal(binder.localRef, Value.ascribe(actual, expectedTy))
  }

}
