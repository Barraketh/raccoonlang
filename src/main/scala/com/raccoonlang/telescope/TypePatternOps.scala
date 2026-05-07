package com.raccoonlang.telescope

import com.raccoonlang.CoreAst.{Term => CTerm, TypePattern => CPattern}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang._

object TypePatternOps {
  private[telescope] final case class FreshenedBinder(value: Value, env: Env, newVars: DepSet)
  private[telescope] final case class FreshenedRawBinder(
      value: Value,
      env: Env,
      newVars: DepSet,
      binder: VBinder,
      checkedBinder: CoreAst.CheckedBinder
  )
  private final case class OpenedPattern(value: Value, env: Env, newVars: DepSet)
  private final case class OpenedApp(fn: Value, args: Vector[Value], env: Env, newVars: DepSet)
  private final case class CheckedPattern(
      pattern: CoreAst.CheckedTypePattern,
      value: Value,
      env: Env,
      newVars: DepSet
  ) {
    def expectedTy: CoreAst.CheckedTypeTerm = compileType(pattern)
  }
  private final case class CheckedBinder(binder: VBinder, checkedBinder: CoreAst.CheckedBinder)

  private def putBinderLocal(
      env: Env,
      binder: VBinder,
      value: Value,
      instanceTerm: Option[CoreAst.CheckedTerm] = None
  )(implicit eqStore: EqStore): Env = {
    val instanceKey =
      if (binder.isInstance) Some(InstanceSearch.instanceKey(binder.name, value, eqStore))
      else None
    env.putLocal(binder.localRef, value, instanceKey, instanceTerm)
  }

  private def toCheckedRef(ref: CoreAst.RawRef): CoreAst.CheckedRef = ref match {
    case CTerm.GlobalRef(name, span) => CTerm.GlobalRef[CoreAst.Checked](name, span)
    case CTerm.LocalRef(ref, span)   => CTerm.LocalRef[CoreAst.Checked](ref, span)
  }

  private def globalName(ref: CoreAst.CheckedRef): Option[String] = ref match {
    case CTerm.GlobalRef(name, _) => Some(name)
    case CTerm.LocalRef(_, _)     => None
  }

  private def requirePi(fn: Value)(implicit eqStore: EqStore): VPi =
    resolveInEqStore(fn.tpe) match {
      case pi: VPi => pi
      case other   => throw CannotApplyNonFunction(other)
    }

  private def compileType(pattern: CoreAst.CheckedTypePattern): CoreAst.CheckedTypeTerm = pattern match {
    case CPattern.Type(term)         => term
    case CPattern.Capture(ref, span) => CTerm.LocalRef[CoreAst.Checked](ref, span)
    case CPattern.App(fn, args, span) =>
      CTerm.App[CoreAst.Checked](fn, args.map(compileType), span)
  }

  private def checkedTermAsTypeTerm(term: CoreAst.CheckedTerm): CoreAst.CheckedTypeTerm =
    term match {
      case term: CoreAst.TypeTerm[_] => term.asInstanceOf[CoreAst.CheckedTypeTerm]
      case other => throw WTF(s"Expected checked instance term to be usable in a type pattern, got $other")
    }

  private def checkedTermAsTypePattern(term: CoreAst.CheckedTerm): CoreAst.CheckedTypePattern =
    CPattern.Type(checkedTermAsTypeTerm(term))

  private def compileLevelCapture(pattern: CoreAst.CheckedTypePattern): Option[VCapture] =
    pattern match {
      case CPattern.Capture(ref, _) => Some(VCapture(ref, 0 :: Nil, LevelCapture(0)))
      case CPattern.App(fn, args, _) if globalName(fn).contains("Level::succ") =>
        compileLevelCapture(args.head).map {
          case c @ VCapture(_, _, LevelCapture(subtract)) => c.copy(captureType = LevelCapture(subtract + 1))
          case _ => throw WTF("Expected a level capture while compiling a level pattern")
        }
      case _ => None
    }

  private def collectCaptures(pattern: CoreAst.CheckedTypePattern): Vector[VCapture] =
    pattern match {
      case CPattern.App(fn, args, _) if globalName(fn).contains("Sort") => compileLevelCapture(args.head).toVector

      case app: CPattern.App[CoreAst.Checked] =>
        app.args.zipWithIndex.flatMap { case (next, idx) =>
          next match {
            case CPattern.Type(_) => Vector.empty
            case nested: CPattern.App[CoreAst.Checked] =>
              collectCaptures(nested).map(capture => capture.copy(path = idx :: capture.path))
            case CPattern.Capture(localRef, _) => Vector(VCapture(localRef, idx :: Nil, StructuralCapture))
          }
        }

      case _ => Vector.empty
    }

  private def checkPattern(pattern: CoreAst.RawTypePattern, env: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): CheckedPattern =
    pattern match {
      case CPattern.Type(term) =>
        val checked = TypeChecker.checkTypeTerm(term, env)
        CheckedPattern(CPattern.Type(checked.term), checked.value, env, DepSet.empty)
      case CPattern.Capture(ref, span) =>
        throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
      case CPattern.App(fn, args, span) =>
        checkPatternApp(fn, args, span, env)
    }

  private def checkPatternApp(
      fn: CoreAst.RawRef,
      args: Vector[CoreAst.RawTypePattern],
      span: Span,
      env: Env
  )(implicit eqStore: EqStore, normalizers: NormalizerMap): CheckedPattern = {
    val fnTerm = toCheckedRef(fn)
    val fnV = evalTypeTerm(fnTerm, env)
    val pi = requirePi(fnV)
    val binders = pi.binders
    val explicitArgCount = binders.count(!_.isDerived)

    var argIdx = 0
    var callerEnv = env
    var calleeEnv = pi.env
    val argPatterns = Vector.newBuilder[CoreAst.CheckedTypePattern]
    val argValues = Vector.newBuilder[Value]
    val newVars = DepSet.newBuilder

    binders.foreach { binder =>
      val (argPattern, argValue, argTerm) =
        if (binder.isDerived) {
          val solved = BinderOps.solveBinder(calleeEnv, binder, env)
          val term = checkedTermAsTypePattern(solved.term)
          (term, solved.value, solved.term)
        } else {
          if (argIdx >= args.length) throw ArityMismatch(explicitArgCount, args.length, Some(span))
          val arg = args(argIdx)
          argIdx += 1

          arg match {
            case CPattern.Capture(ref, captureSpan) =>
              val expected = openPattern(calleeEnv, binder.ty)
              newVars.unionInPlace(expected.newVars)

              val value = FreshVar.freshVar(ref.name, expected.value)
              val pattern = CPattern.Capture[CoreAst.Checked](ref, captureSpan)
              val term = CTerm.LocalRef[CoreAst.Checked](ref, captureSpan)
              callerEnv = callerEnv.putLocal(ref, value)
              newVars.add(value.id)
              (pattern, value, term)

            case other =>
              val checked = checkPattern(other, callerEnv)
              callerEnv = checked.env
              newVars.unionInPlace(checked.newVars)
              (checked.pattern, checked.value, checked.expectedTy)
          }
        }

      calleeEnv = bindValueAndCheck(calleeEnv, binder, argValue, Some(argTerm))
      argPatterns += argPattern
      argValues += argValue
    }

    if (argIdx != args.length) throw ArityMismatch(explicitArgCount, args.length, Some(span))

    val checkedArgs = argPatterns.result()
    val pattern = CPattern.App[CoreAst.Checked](fnTerm, checkedArgs, span)
    CheckedPattern(pattern, Interpreter.evalApply(fnV, argValues.result()), callerEnv, newVars.result())
  }

  private def checkBinder(binder: CoreAst.RawBinder, env: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): CheckedBinder = {
    val checked = checkPattern(binder.ty, env)
    val pattern = checked.pattern
    val captures = collectCaptures(pattern)
    val resType = checked.expectedTy
    TypeChecker.assertType(Interpreter.evalTypeTerm(resType, checked.env))
    val checkedBinder = CoreAst.Binder[CoreAst.Checked](
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

  def toVBinder(binder: CoreAst.CheckedBinder): VBinder = {
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

  private def openCaptures(env: Env, captures: Vector[VCapture], actualTy: Value)(implicit
      eqStore: EqStore
  ): Env = {
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

  private def structConstructorForBinderType(env: Env, binderTy: CoreAst.CheckedTypeTerm)(implicit
      eqStore: EqStore
  ): Option[(ConstructorOps.ConstructorShape, Vector[CoreAst.CheckedTerm])] = {
    val (headValue, argTerms) = binderTy match {
      case CTerm.App(fn, args, _)          => (Interpreter.evalTerm(fn, env), args)
      case ref: CTerm.Ref[CoreAst.Checked] => (Interpreter.evalTypeTerm(ref, env), Vector.empty)
      case _                               => return None
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

  private def freshenStructBinder(
      env: Env,
      binder: VBinder,
      shape: ConstructorOps.ConstructorShape,
      argTerms: Vector[CoreAst.CheckedTerm]
  )(implicit eqStore: EqStore): FreshenedBinder = {
    val (args, newVars) = binder.ty match {
      case app: CPattern.App[CoreAst.Checked] =>
        val opened = openPatternPrefix(env, app, shape.paramCount)
        (opened.args, opened.newVars)
      case _ =>
        (shape.paramArgs(argTerms).map(arg => Interpreter.evalTerm(arg, env)), DepSet.empty)
    }
    val fresh = ConstructorOps.freshFromParams(shape.head, args)
    val refinedEnv = openCaptures(env, binder.captures, fresh.value.tpe)
    FreshenedBinder(fresh.value, refinedEnv, newVars ++ fresh.newVars)
  }

  private def openPatternPrefix(env: Env, app: CPattern.App[CoreAst.Checked], argCount: Int)(implicit
      eqStore: EqStore
  ): OpenedApp = {
    val fnV = evalTypeTerm(app.fn, env)
    val pi = requirePi(fnV)
    val binders = pi.binders
    val args = app.args

    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length, Some(app.span))

    var callerEnv = env
    var calleeEnv = pi.env
    val argValues = Vector.newBuilder[Value]
    val newVars = DepSet.newBuilder

    binders.zip(args).take(argCount).foreach { case (binder, arg) =>
      val argValue = arg match {
        case CPattern.Capture(ref, _) =>
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

  private def openPattern(env: Env, pattern: CoreAst.CheckedTypePattern)(implicit eqStore: EqStore): OpenedPattern =
    pattern match {
      case app: CPattern.App[CoreAst.Checked] =>
        val opened = openPatternPrefix(env, app, app.args.length)
        OpenedPattern(Interpreter.evalApply(opened.fn, opened.args), opened.env, opened.newVars)
      case CPattern.Capture(ref, span) => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
      case CPattern.Type(term)         => OpenedPattern(evalTypeTerm(term, env), env, DepSet.empty)
    }

  private[telescope] def freshenBinder(env: Env, binder: VBinder)(implicit eqStore: EqStore): FreshenedBinder = {
    structConstructorForBinderType(env, binder.expectedTy) match {
      case Some((shape, argTerms)) => freshenStructBinder(env, binder, shape, argTerms)
      case None =>
        val opened = openPattern(env, binder.ty)
        val value = FreshVar.freshVar(binder.name, opened.value)
        FreshenedBinder(value, opened.env, opened.newVars + value.id)
    }
  }

  private[telescope] def freshenRawBinder(env: Env, binder: CoreAst.RawBinder)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): FreshenedRawBinder = {
    val checked = checkBinder(binder, env)
    val fresh = freshenBinder(env, checked.binder)
    FreshenedRawBinder(fresh.value, fresh.env, fresh.newVars, checked.binder, checked.checkedBinder)
  }

  def bindValue(
      env: Env,
      binder: VBinder,
      actual: Value,
      instanceTerm: Option[CoreAst.CheckedTerm] = None
  )(implicit eqStore: EqStore): Env = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    putBinderLocal(openedEnv, binder, actual, instanceTerm)
  }

  private[telescope] def bindValueAndCheck(
      env: Env,
      binder: VBinder,
      actual: Value,
      instanceTerm: Option[CoreAst.CheckedTerm] = None
  )(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Env = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    val expectedTy = Interpreter.evalTypeTerm(binder.expectedTy, openedEnv)
    TypeChecker.checkType(actual, expectedTy)
    putBinderLocal(openedEnv, binder, Value.ascribe(actual, expectedTy), instanceTerm)
  }

}
