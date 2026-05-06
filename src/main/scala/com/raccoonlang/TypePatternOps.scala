package com.raccoonlang

import com.raccoonlang.CoreAst.{Binder, Term => CTerm, TypePattern => CTypePattern, TypeTerm => CTypeTerm}
import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

object TypePatternOps {
  final case class FreshenedBinder(value: Value, env: Env, newVars: DepSet)
  final case class FreshenedRawBinder(value: Value, env: Env, newVars: DepSet, binder: VBinder)
  private final case class OpenedPattern(value: Value, env: Env, newVars: DepSet)
  private final case class OpenedApp(fn: Value, args: Vector[Value], env: Env, newVars: DepSet)
  private final case class CheckedPattern(pattern: ElabAst.TypePattern, value: Value, env: Env, newVars: DepSet) {
    def expectedTy: ElabAst.TypeTerm = compileType(pattern)
  }

  private def putBinderLocal(
      env: Env,
      binder: VBinder,
      value: Value,
      instanceTerm: Option[ElabAst.Term] = None
  )(implicit eqStore: EqStore): Env = {
    val instanceKey =
      if (binder.isInstance || binder.isDerived) Some(InstanceSearch.instanceKey(binder.name, value, eqStore))
      else None
    env.putLocal(binder.localRef, value, instanceKey, instanceTerm)
  }

  private def toElabRef(ref: CTerm.Ref): ETerm.Ref = ref match {
    case CTerm.GlobalRef(name, span) => ETerm.GlobalRef(name, span)
    case CTerm.LocalRef(ref, span)   => ETerm.LocalRef(ref, span)
  }

  private def globalName(ref: ETerm.Ref): Option[String] = ref match {
    case ETerm.GlobalRef(name, _) => Some(name)
    case ETerm.LocalRef(_, _)     => None
  }

  private def requirePi(fn: Value)(implicit eqStore: EqStore): VPi =
    resolveInEqStore(fn.tpe) match {
      case pi: VPi => pi
      case other   => throw CannotApplyNonFunction(other)
    }

  private def compileType(pattern: ElabAst.TypePattern): ElabAst.TypeTerm = pattern match {
    case term: ElabAst.TypeTerm      => term
    case ETerm.Capture(_, ref, span) => ETerm.LocalRef(ref, span)
    case ETerm.PatternApp(fn, args, span) =>
      ETerm.App(fn, args.toVector.map(compileType), span)
  }

  private def checkedTermAsTypePattern(term: ElabAst.Term): ElabAst.TypePattern =
    term match {
      case pattern: ElabAst.TypePattern => pattern
      case other => throw WTF(s"Expected checked instance term to be usable in a type pattern, got $other")
    }

  private def compileLevelCapture(pattern: ElabAst.TypePattern): Option[VCapture] =
    pattern match {
      case ETerm.Capture(name, ref, _) => Some(VCapture(name, ref, 0 :: Nil, LevelCapture(0)))
      case ETerm.PatternApp(fn, args, _) if globalName(fn).contains("Level::succ") =>
        compileLevelCapture(args.head).map {
          case c @ VCapture(_, _, _, LevelCapture(subtract)) => c.copy(captureType = LevelCapture(subtract + 1))
          case _ => throw WTF("Expected a level capture while compiling a level pattern")
        }
      case _ => None
    }

  private def collectCaptures(pattern: ElabAst.TypePattern): Vector[VCapture] =
    pattern match {
      case ETerm.PatternApp(fn, args, _) if globalName(fn).contains("Sort") => compileLevelCapture(args.head).toVector

      case app: ETerm.PatternApp =>
        app.args.toVector.zipWithIndex.flatMap { case (next, idx) =>
          next match {
            case _: ElabAst.TypeTerm => Vector.empty
            case nested: ETerm.PatternApp =>
              collectCaptures(nested).map(capture => capture.copy(path = idx :: capture.path))
            case ETerm.Capture(name, localRef, _) => Vector(VCapture(name, localRef, idx :: Nil, StructuralCapture))
          }
        }

      case _ => Vector.empty
    }

  private def checkPattern(pattern: CTypePattern, env: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): CheckedPattern =
    pattern match {
      case term: CTypeTerm =>
        val checked = TypeChecker.checkTypeTerm(term, env)
        CheckedPattern(checked.term, checked.value, env, DepSet.empty)
      case CTerm.Capture(name, _, span) =>
        throw PatternCaptureNeedsExpectedType(name, Some(span))
      case CTerm.PatternApp(fn, args, span) =>
        checkPatternApp(fn, args.toVector, span, env)
    }

  private def checkPatternApp(
      fn: CTerm.Ref,
      args: Vector[CTypePattern],
      span: Span,
      env: Env
  )(implicit eqStore: EqStore, normalizers: NormalizerMap): CheckedPattern = {
    val fnTerm = toElabRef(fn)
    val fnV = evalTypeTerm(fnTerm, env)
    val pi = requirePi(fnV)
    val binders = pi.binders.toVector
    val explicitArgCount = binders.count(!_.isDerived)

    var argIdx = 0
    var callerEnv = env
    var calleeEnv = pi.env
    val argPatterns = Vector.newBuilder[ElabAst.TypePattern]
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
            case CTerm.Capture(name, ref, captureSpan) =>
              val expected = openPattern(calleeEnv, binder.ty)
              newVars.unionInPlace(expected.newVars)

              val value = FreshVar.freshVar(name, expected.value)
              val pattern = ETerm.Capture(name, ref, captureSpan)
              val term = ETerm.LocalRef(ref, captureSpan)
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
    val pattern = ETerm.PatternApp(fnTerm, NEL.mk(checkedArgs), span)
    CheckedPattern(pattern, Interpreter.evalApply(fnV, NEL.mk(argValues.result())), callerEnv, newVars.result())
  }

  def toVBinder(binder: CoreAst.Binder, env: Env)(implicit eqStore: EqStore, normalizers: NormalizerMap): VBinder = {
    val checked = checkPattern(binder.ty, env)
    val pattern = checked.pattern
    val captures = collectCaptures(pattern)
    val resType = checked.expectedTy
    TypeChecker.assertType(Interpreter.evalTypeTerm(resType, checked.env))

    val plan = TypePatternPlan(pattern, resType, captures)
    VBinder(binder.name, binder.localRef, plan, binder.isDerived, binder.isInstance)
  }

  def toElabBinder(binder: VBinder, span: Span): ElabAst.Binder =
    ElabAst.Binder(
      binder.name,
      binder.localRef,
      binder.ty,
      binder.expectedTy,
      binder.captures,
      span,
      binder.isDerived,
      binder.isInstance
    )

  def toVBinder(binder: ElabAst.Binder): VBinder =
    VBinder(
      binder.name,
      binder.localRef,
      TypePatternPlan(binder.ty, binder.expectedTy, binder.captures),
      binder.isDerived,
      binder.isInstance
    )

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

  private def structConstructorForBinderType(env: Env, binderTy: ElabAst.TypeTerm)(implicit
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

  private def freshenStructBinder(
      env: Env,
      binder: VBinder,
      shape: ConstructorOps.ConstructorShape,
      argTerms: Vector[ElabAst.Term]
  )(implicit eqStore: EqStore): FreshenedBinder = {
    val (args, newVars) = binder.ty match {
      case app: ETerm.PatternApp =>
        val opened = openPatternPrefix(env, app, shape.paramCount)
        (opened.args, opened.newVars)
      case _ =>
        (shape.paramArgs(argTerms).map(arg => Interpreter.evalTerm(arg, env)), DepSet.empty)
    }
    val fresh = ConstructorOps.freshFromParams(shape.head, args)
    val refinedEnv = openCaptures(env, binder.captures, fresh.value.tpe)
    FreshenedBinder(fresh.value, refinedEnv, newVars ++ fresh.newVars)
  }

  private def openPatternPrefix(env: Env, app: ETerm.PatternApp, argCount: Int)(implicit
      eqStore: EqStore
  ): OpenedApp = {
    val fnV = evalTypeTerm(app.fn, env)
    val pi = requirePi(fnV)
    val binders = pi.binders.toVector
    val args = app.args.toVector

    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length, Some(app.span))

    var callerEnv = env
    var calleeEnv = pi.env
    val argValues = Vector.newBuilder[Value]
    val newVars = DepSet.newBuilder

    binders.zip(args).take(argCount).foreach { case (binder, arg) =>
      val argValue = arg match {
        case ETerm.Capture(name, ref, _) =>
          val expected = openPattern(calleeEnv, binder.ty)
          newVars.unionInPlace(expected.newVars)

          val value = FreshVar.freshVar(name, expected.value)
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

  private def openPattern(env: Env, pattern: ElabAst.TypePattern)(implicit eqStore: EqStore): OpenedPattern =
    pattern match {
      case app: ETerm.PatternApp =>
        val opened = openPatternPrefix(env, app, app.args.length)
        OpenedPattern(Interpreter.evalApply(opened.fn, NEL.mk(opened.args)), opened.env, opened.newVars)
      case ETerm.Capture(name, _, span) => throw PatternCaptureNeedsExpectedType(name, Some(span))
      case term: ElabAst.TypeTerm       => OpenedPattern(evalTypeTerm(term, env), env, DepSet.empty)
    }

  def freshenBinder(env: Env, binder: VBinder)(implicit eqStore: EqStore): FreshenedBinder = {
    structConstructorForBinderType(env, binder.expectedTy) match {
      case Some((shape, argTerms)) => freshenStructBinder(env, binder, shape, argTerms)
      case None =>
        val opened = openPattern(env, binder.ty)
        val value = FreshVar.freshVar(binder.name, opened.value)
        FreshenedBinder(value, opened.env, opened.newVars + value.id)
    }
  }

  def freshenRawBinder(env: Env, binder: Binder)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): FreshenedRawBinder = {
    val vBinder = toVBinder(binder, env)
    val fresh = freshenBinder(env, vBinder)
    FreshenedRawBinder(fresh.value, fresh.env, fresh.newVars, vBinder)
  }

  def bindValue(
      env: Env,
      binder: VBinder,
      actual: Value,
      instanceTerm: Option[ElabAst.Term] = None
  )(implicit eqStore: EqStore): Env = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    putBinderLocal(openedEnv, binder, actual, instanceTerm)
  }

  def bindValueAndCheck(
      env: Env,
      binder: VBinder,
      actual: Value,
      instanceTerm: Option[ElabAst.Term] = None
  )(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Env = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    val expectedTy = Interpreter.evalTypeTerm(binder.expectedTy, openedEnv)
    TypeChecker.checkType(actual, expectedTy)
    putBinderLocal(openedEnv, binder, Value.ascribe(actual, expectedTy), instanceTerm)
  }

  def expectedType(env: Env, binder: VBinder)(implicit eqStore: EqStore): Value =
    Interpreter.evalTypeTerm(binder.expectedTy, env)
}
