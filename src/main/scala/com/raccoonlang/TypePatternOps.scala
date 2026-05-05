package com.raccoonlang

import com.raccoonlang.CoreAst.{Binder, Term, TypePattern, TypeTerm}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

object TypePatternOps {
  final case class FreshenedBinder(value: Value, env: Env, newVars: DepSet)
  final case class FreshenedRawBinder(value: Value, env: Env, newVars: DepSet, binder: VBinder)
  private final case class OpenedPattern(value: Value, env: Env, newVars: DepSet)
  private final case class OpenedApp(fn: Value, args: Vector[Value], env: Env, newVars: DepSet)

  private def putBinderLocal(env: Env, binder: VBinder, value: Value): Env =
    binder.localRef match {
      case Some(ref) => env.putLocal(ref, value)
      case None      => env
    }

  private def globalName(ref: Term.Ref): Option[String] = ref match {
    case Term.GlobalRef(name, _) => Some(name)
    case Term.LocalRef(_, _)     => None
  }

  private def requirePi(fn: Value)(implicit eqStore: EqStore): VPi =
    resolveInEqStore(fn.tpe) match {
      case pi: VPi => pi
      case other   => throw CannotApplyNonFunction(other)
    }

  private def compileType(pattern: TypePattern): TypeTerm = pattern match {
    case term: TypeTerm             => term
    case Term.Capture(_, ref, span) => Term.LocalRef(ref, span)
    case Term.PatternApp(fn, args, span) =>
      Term.TApp(fn, args.map(compileType), span)
  }

  private def compileLevelCapture(pattern: TypePattern): Option[VCapture] =
    pattern match {
      case Term.Capture(name, ref, _) => Some(VCapture(name, ref, 0 :: Nil, LevelCapture(0)))
      case Term.PatternApp(fn, args, _) if globalName(fn).contains("Level::succ") =>
        compileLevelCapture(args.head).map {
          case c @ VCapture(_, _, _, LevelCapture(subtract)) => c.copy(captureType = LevelCapture(subtract + 1))
          case _ => throw WTF("Expected a level capture while compiling a level pattern")
        }
      case _ => None
    }

  private def collectCaptures(pattern: TypePattern): Vector[VCapture] =
    pattern match {
      case Term.PatternApp(fn, args, _) if globalName(fn).contains("Sort") => compileLevelCapture(args.head).toVector

      case app: Term.PatternApp =>
        app.args.toVector.zipWithIndex.flatMap { case (next, idx) =>
          next match {
            case _: TypeTerm => Vector.empty
            case nested: Term.PatternApp =>
              collectCaptures(nested).map(capture => capture.copy(path = idx :: capture.path))
            case Term.Capture(name, localRef, _) => Vector(VCapture(name, localRef, idx :: Nil, StructuralCapture))
          }
        }

      case _ => Vector.empty
    }

  def toVBinder(env: Env, binder: CoreAst.Binder, evalTypeTerm: (CoreAst.TypeTerm, Env) => Value)(implicit
      eqStore: EqStore
  ): VBinder = {
    val captures = collectCaptures(binder.ty)
    val resType = compileType(binder.ty)

    val opened = openPattern(env, binder.ty)
    evalTypeTerm(resType, opened.env)

    VBinder(binder.name, binder.localRef, binder.ty, resType, captures)
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

  private def structConstructorForBinderType(env: Env, binderTy: TypeTerm)(implicit
      eqStore: EqStore
  ): Option[(ConstructorOps.ConstructorShape, Vector[TypeTerm])] = {
    val (headValue, argTerms) = binderTy match {
      case Term.TApp(fn, args, _) => (Interpreter.evalTypeTerm(fn, env), args.toVector)
      case ref: Term.Ref          => (Interpreter.evalTypeTerm(ref, env), Vector.empty)
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
      argTerms: Vector[TypeTerm]
  )(implicit eqStore: EqStore): FreshenedBinder = {
    val (args, newVars) = binder.ty match {
      case app: Term.PatternApp =>
        val opened = openPatternPrefix(env, app, shape.paramCount)
        (opened.args, opened.newVars)
      case _ =>
        (shape.paramArgs(argTerms).map(arg => Interpreter.evalTypeTerm(arg, env)), DepSet.empty)
    }
    val fresh = ConstructorOps.freshFromParams(shape.head, args)
    // Constructor params are only used to build the fresh struct. Captures are projected from the fresh result type
    // under the original caller env so index refinements from the constructed value are preserved.
    val refinedEnv = openCaptures(env, binder.captures, fresh.value.tpe)
    FreshenedBinder(fresh.value, refinedEnv, newVars ++ fresh.newVars)
  }

  private def openPatternPrefix(env: Env, app: Term.PatternApp, argCount: Int)(implicit eqStore: EqStore): OpenedApp = {
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
        case Term.Capture(name, ref, _) =>
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

  private def openPattern(env: Env, pattern: TypePattern)(implicit eqStore: EqStore): OpenedPattern =
    pattern match {
      case app: Term.PatternApp =>
        val opened = openPatternPrefix(env, app, app.args.length)
        OpenedPattern(Interpreter.evalApply(opened.fn, NEL.mk(opened.args)), opened.env, opened.newVars)
      case Term.Capture(name, _, span) => throw PatternCaptureNeedsExpectedType(name, Some(span))
      case term: TypeTerm              => OpenedPattern(evalTypeTerm(term, env), env, DepSet.empty)
    }

  // =========================
  // Public API
  // =========================

  /** Create a fresh value for a binder and return:
    *   - The fresh value (either a Var or a VCtor for struct types)
    *   - The environment extended with any captures introduced by the binder's type pattern
    *   - The set of newly created variable IDs
    */
  def freshenBinder(env: Env, binder: VBinder)(implicit eqStore: EqStore): FreshenedBinder = {
    structConstructorForBinderType(env, binder.expectedTy) match {
      case Some((shape, argTerms)) => freshenStructBinder(env, binder, shape, argTerms)
      case None =>
        val opened = openPattern(env, binder.ty)
        val openedEnv = opened.env
        val value = FreshVar.freshVar(binder.name, opened.value)
        FreshenedBinder(value, openedEnv, opened.newVars + value.id)
    }
  }

  def freshenRawBinder(env: Env, binder: Binder, evalTypeTerm: (CoreAst.TypeTerm, Env) => Value)(implicit
      eqStore: EqStore
  ): FreshenedRawBinder = {
    val vBinder = toVBinder(env, binder, evalTypeTerm)
    val fresh = freshenBinder(env, vBinder)
    FreshenedRawBinder(fresh.value, fresh.env, fresh.newVars, vBinder)
  }

  // Used by Interpreter.getEnvWithArgs
  def bindValue(env: Env, binder: VBinder, actual: Value)(implicit eqStore: EqStore): Env = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    putBinderLocal(openedEnv, binder, actual)
  }

  // Used by TypeChecker.typecheckApply
  def bindValueAndCheck(env: Env, binder: VBinder, actual: Value)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Env = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    val expectedTy = Interpreter.evalTypeTerm(binder.expectedTy, openedEnv)
    TypeChecker.checkType(actual, expectedTy)
    putBinderLocal(openedEnv, binder, actual)
  }

}
