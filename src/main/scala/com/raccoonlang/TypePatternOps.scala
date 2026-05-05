package com.raccoonlang

import com.raccoonlang.CoreAst.{Binder, Term, TypePattern, TypeTerm}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._

object TypePatternOps {
  final case class FreshenedBinder(value: Value, env: Env, newVars: DepSet)
  final case class FreshenedRawBinder(value: Value, env: Env, newVars: DepSet, binder: VBinder)

  private def requirePi(fn: Value)(implicit eqStore: EqStore): VPi =
    resolveInEqStore(fn.tpe) match {
      case pi: VPi => pi
      case other   => throw CannotApplyNonFunction(other)
    }

  private def compileType(pattern: TypePattern): TypeTerm = pattern match {
    case term: TypeTerm           => term
    case Term.Capture(name, span) => Term.Ident(name, span)
    case Term.PatternApp(fn, args, span) =>
      Term.TApp(fn, args.map(compileType), span)
  }

  private def compileLevelCapture(pattern: TypePattern): Option[VCapture] =
    pattern match {
      case Term.Capture(name, _) => Some(VCapture(name, 0 :: Nil, LevelCapture(0)))
      case Term.PatternApp(fn, args, _) if fn.name == "Level::succ" =>
        compileLevelCapture(args.head).map {
          case c @ VCapture(_, _, LevelCapture(subtract)) => c.copy(captureType = LevelCapture(subtract + 1))
          case _ => throw WTF("Expected a level capture while compiling a level pattern")
        }
      case _ => None
    }

  private def collectCaptures(env: Env, pattern: TypePattern, evalTypeTerm: (CoreAst.TypeTerm, Env) => Value)(implicit
      eqStore: EqStore
  ): Vector[VCapture] =
    pattern match {
      case Term.PatternApp(fn, args, _) if fn.name == "Sort" => compileLevelCapture(args.head).toVector

      case app: Term.PatternApp =>
        val fnV = evalTypeTerm(app.fn, env)
        val pi = requirePi(fnV)

        pi.binders.zip(app.args).toVector.zipWithIndex.flatMap {
          case ((binder, next), idx) =>
            next match {
              case _: TypeTerm => Vector.empty
              case nested: Term.PatternApp =>
                collectCaptures(env, nested, evalTypeTerm).map(capture => capture.copy(path = idx :: capture.path))
              case Term.Capture(name, _) =>
                Vector(VCapture(name, idx :: Nil, StructuralCapture(binder)))
            }
          case _ => Vector.empty
        }

      case _ => Vector.empty
    }

  def toVBinder(env: Env, binder: CoreAst.Binder, evalTypeTerm: (CoreAst.TypeTerm, Env) => Value)(implicit
      eqStore: EqStore
  ): VBinder = {
    binder.ty match {
      case Term.Capture(name, span) => throw PatternCaptureNeedsExpectedType(name, Some(span))
      case _                        =>
    }

    val captures = collectCaptures(env, binder.ty, evalTypeTerm)
    val resType = compileType(binder.ty)

    val (withCaptures, _) = freshenCaptures(env, captures)
    evalTypeTerm(resType, withCaptures)

    VBinder(binder.name, resType, captures)
  }

  private def actualHeadView(v: Value)(implicit eqStore: EqStore): Option[(Value, Vector[Value])] =
    resolveInEqStore(v) match {
      case VSort(level)       => Some((envSortValue, Vector(level)))
      case av: AppliedValue   => Some((av.head, av.args.toVector))
      case v: VCtor           => Some((v.head, v.fields))
      case h: VConst          => Some((h, Vector.empty))
      case h: ConstructorHead => Some((h, Vector.empty))
      case _                  => None
    }

  private def envSortValue: Value = VConst("Sort", Symbol, KernelObject)

  private def project(value: Value, path: List[Int])(implicit eqStore: EqStore): Value =
    path.foldLeft(resolveInEqStore(value)) { case (cur, nextIdx) =>
      val pieces = resolveInEqStore(cur) match {
        case VSort(level)     => Vector(level)
        case av: AppliedValue => av.args.toVector
        case v: VCtor         => v.fields
        case _                => throw FailedToOpenCapture(cur, nextIdx)
      }
      pieces.lift(nextIdx).getOrElse(throw FailedToOpenCapture(cur, nextIdx))
    }

  private def openCaptures(env: Env, captures: Vector[VCapture], actualTy: Value)(implicit
      eqStore: EqStore
  ): Env = {
    captures.foldLeft(env) { (curEnv, capture) =>
      val captureValue = capture.captureType match {
        case StructuralCapture(_) => project(actualTy, capture.path)
        case LevelCapture(subtract) =>
          val projected = Interpreter.getLevel(project(actualTy, capture.path))
          if (!Level.geq(projected, subtract)) throw InvalidLevelSubtraction(projected, subtract)
          Level.addOffset(projected, -subtract)
      }
      curEnv.putLocal(capture.name, captureValue)
    }
  }

  private def freshenCaptures(env: Env, captures: Vector[VCapture])(implicit eqStore: EqStore): (Env, DepSet) = {
    captures.foldLeft((env, DepSet.empty)) { case ((curEnv, curNewVars), capture) =>
      capture.captureType match {
        case StructuralCapture(captureBinder) =>
          val fresh = freshenBinder(curEnv, captureBinder)
          (curEnv.putLocal(capture.name, fresh.value), curNewVars ++ fresh.newVars)
        case LevelCapture(_) =>
          val fresh = FreshVar.freshVar(capture.name, LevelTpe)
          (curEnv.putLocal(capture.name, fresh), curNewVars + fresh.id)
      }
    }
  }

  private def structConstructorForBinderType(env: Env, binderTy: TypeTerm)(implicit
      eqStore: EqStore
  ): Option[(ConstructorOps.ConstructorShape, Vector[TypeTerm])] = {
    val (headValue, argTerms) = binderTy match {
      case Term.TApp(fn, args, _) => (Interpreter.evalTypeTerm(fn, env), args.toVector)
      case ident: Term.Ident      => (Interpreter.evalTypeTerm(ident, env), Vector.empty)
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
    // Freshen param captures because they are required to evaluate constructor parameter args.
    val paramCaptures = binder.captures.filter(capture => shape.isParamIndex(capture.path.head))
    val (paramEnv, paramCaptureVars) = freshenCaptures(env, paramCaptures)

    val paramArgs = shape.paramArgs(argTerms).map(arg => Interpreter.evalTypeTerm(arg, paramEnv))
    val fresh = ConstructorOps.freshFromParams(shape.head, paramArgs)
    val refinedEnv = openCaptures(env, binder.captures, fresh.value.tpe)
    FreshenedBinder(fresh.value, refinedEnv, paramCaptureVars ++ fresh.newVars)
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
    structConstructorForBinderType(env, binder.ty) match {
      case Some((shape, argTerms)) => freshenStructBinder(env, binder, shape, argTerms)
      case None =>
        val (openedEnv, captureVars) = freshenCaptures(env, binder.captures)
        val tpe = Interpreter.resolveInEqStore(Interpreter.evalTypeTerm(binder.ty, openedEnv))
        val value = FreshVar.freshVar(binder.name, tpe)
        FreshenedBinder(value, openedEnv, captureVars + value.id)
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
    val withCaptures = openCaptures(env, binder.captures, actual.tpe)
    withCaptures.putLocal(binder.name, actual)
  }

  // Used by TypeChecker.typecheckApply
  def bindValueAndCheck(env: Env, binder: VBinder, actual: Value)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Env = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    val expectedTy = Interpreter.evalTypeTerm(binder.ty, openedEnv)
    TypeChecker.checkType(actual, expectedTy)
    openedEnv.putLocal(binder.name, actual)
  }

}
