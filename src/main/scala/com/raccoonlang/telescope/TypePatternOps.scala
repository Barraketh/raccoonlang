package com.raccoonlang.telescope

import com.raccoonlang.CoreAst.{Term, BinderType => CBinderType, TypePattern => CPattern}
import com.raccoonlang.ElabAst.{BinderType => EBinderType, Term => ETerm, TypePattern => EPattern}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang._
import com.raccoonlang.Ledger.LinearInfo

object TypePatternOps {
  private final case class OpenedApp(fn: Value, args: Vector[Value], env: Env)

  private def requirePi(fn: Value): VPi =
    fn.tpe match {
      case pi: VPi => pi
      case other   => throw CannotApplyNonFunction(other)
    }

  private def compileType(pattern: ElabAst.TypePattern): ElabAst.TypeTerm = pattern match {
    case EPattern.Type(term)            => term
    case EPattern.Capture(ref, span, _) => ETerm.LocalRef(ref, span)
    case EPattern.App(fn, args, span)   => ETerm.App(fn, args.map(compileType), span)
  }

  private def compileBinderType(binderType: ElabAst.BinderType): ElabAst.TypeTerm =
    binderType match {
      case EBinderType.TypePattern(tp, _)               => compileType(tp)
      case EBinderType.ConstrainedCapture(ref, _, span) => ETerm.LocalRef(ref, span)
    }

  private def collectCaptures(pattern: ElabAst.TypePattern, root: CaptureRoot = ActualType): Vector[VCapture] = {
    // The level argument of a universe former is its argument `index`: `Sort(l)` and `Lin(l)` at 0, `Univ(k, l)` at 1.
    def compileLevelCapture(pattern: ElabAst.TypePattern, index: Int): Option[VCapture] =
      pattern match {
        case EPattern.Capture(ref, _, _) => Some(VCapture(ref, index :: Nil, LevelCapture(0), root))
        case EPattern.App(ETerm.GlobalRef("Level.succ", _), args, _) =>
          compileLevelCapture(args.head, index).map {
            case c @ VCapture(_, _, LevelCapture(subtract), _) =>
              c.copy(captureType = LevelCapture(subtract + 1))
            case _ => throw WTF("Expected a level capture while compiling a level pattern")
          }
        case _ => None
      }

    pattern match {
      case EPattern.App(ETerm.GlobalRef("Sort" | "Lin", _), args, _) =>
        compileLevelCapture(args.head, 0).toVector
      case EPattern.App(ETerm.GlobalRef("Univ", _), Vector(kind, level), _) =>
        val kindCapture = kind match {
          case EPattern.Capture(ref, _, _) => Vector(VCapture(ref, 0 :: Nil, KindCapture, root))
          case _                           => Vector.empty
        }
        kindCapture ++ compileLevelCapture(level, 1)

      case app: EPattern.App =>
        app.args.zipWithIndex.flatMap { case (next, idx) =>
          next match {
            case EPattern.Type(_) => Vector.empty
            case nested: EPattern.App =>
              collectCaptures(nested, root).map(capture => capture.copy(path = idx :: capture.path))
            // A constraint matches the type of the captured argument, and its captures come first, as they are bound.
            case EPattern.Capture(localRef, _, constraint) =>
              constraint.toVector.flatMap { c =>
                collectCaptures(c, root).map(capture => capture.copy(path = idx :: TypeOfStep :: capture.path))
              } :+ VCapture(localRef, idx :: Nil, StructuralCapture, root)
          }
        }

      case _ => Vector.empty
    }
  }

  /** The captures a binder type binds, in source order, with their spans: those of its pattern and its constraints. */
  private def boundCaptures(binderType: ElabAst.BinderType): Vector[(CoreAst.LocalRef, Span)] = {
    def walk(pattern: ElabAst.TypePattern): Vector[(CoreAst.LocalRef, Span)] =
      pattern match {
        case EPattern.Type(_)                        => Vector.empty
        case EPattern.App(_, args, _)                => args.flatMap(walk)
        case EPattern.Capture(ref, span, constraint) => (ref -> span) +: constraint.toVector.flatMap(walk)
      }
    binderType match {
      case EBinderType.TypePattern(tp, _)                        => walk(tp)
      case EBinderType.ConstrainedCapture(ref, constraint, span) => (ref -> span) +: walk(constraint)
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

  private[telescope] def toVBinder(binder: CoreAst.Binder, env: Env): (VBinder, ElabAst.Binder) = {

    /**
     * The checked pattern, its environment, its value, and what it does with tracked locals. A pattern is part of the
     * binder's type, a read extent: each application node is a call of the read rules (`Ledger.call`), and the root, a
     * type, reports their first violation. A `Type` argument is a checked term with its own info. A capture of linear
     * type is refused (L7): it would bind an untracked linear local that a term could consume.
     */
    def checkPattern(pattern: CoreAst.TypePattern, env: Env): (ElabAst.TypePattern, Env, Value, LinearInfo) = {
      pattern match {
        case CPattern.Type(term) =>
          val checked = TypeChecker.checkTypeTerm(term, env)
          (EPattern.Type(checked.residual), env, checked.value, checked.lin)
        case CPattern.Capture(ref, span, _) => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
        case CPattern.App(fn, args, span) =>
          val checkedFn = TypeChecker.checkTypeTerm(fn, env)
          val pi = requirePi(checkedFn.value)
          val binders = pi.binders

          if (binders.length != args.length) throw ArityMismatch(binders.length, args.length, Some(span))

          var patternEnv = env
          var telescopeEnv = pi.env
          val argPatterns = Vector.newBuilder[ElabAst.TypePattern]
          val argValues = Vector.newBuilder[Value]
          val inputs = Vector.newBuilder[Ledger.Input]
          inputs += Ledger.Input(checkedFn.lin, fn.span)

          // An argument that does not fit its parameter is reported where it is written.
          binders.zip(args).foreach { case (paramBinder, arg) =>
            TypeChecker.at(arg.span) {
              val (argPattern, argValue, argInfo) =
                arg match {
                  // A constrained capture has its constraint as its type, which the parameter's type must then fit, such
                  // as `$A in Sort($u)` at a `Univ($k, $u)` parameter, which fixes the kind.
                  case CPattern.Capture(ref, captureSpan, constraint) =>
                    val (checkedConstraint, captureType) = constraint match {
                      case Some(c) =>
                        val (checkedC, constraintEnv) = checkTopLevel(c, patternEnv)
                        patternEnv = constraintEnv
                        val constraintValue = Interpreter.evalTypeTerm(compileType(checkedC), constraintEnv)
                        TypeChecker.assertType(constraintValue)
                        (Some(checkedC), constraintValue)
                      case None => (None, openBinderType(telescopeEnv, paramBinder.ty)._1)
                    }
                    if (Linearity.isLinear(captureType)) throw LinearInType(Some(captureSpan))
                    val value = FreshVar.freshVar(ref.name, captureType)
                    patternEnv = patternEnv.putLocal(ref, value)
                    (EPattern.Capture(ref, captureSpan, checkedConstraint), value, LinearInfo.empty)

                  case other =>
                    val (checkedPattern, checkedEnv, value, info) = checkPattern(other, patternEnv)
                    patternEnv = checkedEnv
                    (checkedPattern, value, info)
                }

              telescopeEnv = bindValueAndCheck(telescopeEnv, paramBinder, argValue)
              argPatterns += argPattern
              argValues += argValue
              inputs += Ledger.Input(argInfo, arg.span)
            }
          }

          val value = Interpreter.evalApply(checkedFn.value, argValues.result())
          val pattern = EPattern.App(toElabRef(fn), argPatterns.result(), span)
          (pattern, patternEnv, value, Ledger.call(value, inputs.result(), span, patternEnv))
      }
    }

    def checkTopLevel(pattern: CoreAst.TopLevelTP, env: Env): (ElabAst.TopLevelTP, Env) = {
      // A binder's type pattern is a type, so the root's info has reported every violation inside it.
      val (checked, checkedEnv, _, _) = checkPattern(pattern, env)
      checked match {
        case topLevel: ElabAst.TopLevelTP   => (topLevel, checkedEnv)
        case EPattern.Capture(ref, span, _) => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
      }
    }

    def checkBinderType(binderType: CoreAst.BinderType, env: Env): (ElabAst.BinderType, Env) =
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

    // A binder type's error is located in it, wherever the binder stands: a declaration, a lambda, a function type or
    // a constructor field.
    val (binderType, checkedEnv) = TypeChecker.at(binder.ty.span)(checkBinderType(binder.ty, env))
    val captures = collectBinderCaptures(binderType)
    // The declaration binds every capture of the pattern, but a binding opens only the collected ones; another, such as
    // `$u` in `Sort(Level.max($u, $v))`, would be unbound at every call.
    val opened = captures.map(_.localRef).toSet
    boundCaptures(binderType).find { case (ref, _) => !opened(ref) }.foreach { case (ref, span) =>
      throw CaptureWithoutOpening(ref.name, Some(span))
    }
    val resType = compileBinderType(binderType)
    val resTypeValue = Interpreter.evalTypeTerm(resType, checkedEnv)
    TypeChecker.at(binder.ty.span)(TypeChecker.assertType(resTypeValue))
    // L7: instance search would copy a linear instance.
    if (binder.isInstance && Linearity.isLinear(resTypeValue)) throw LinearInstance(binder.name, Some(binder.span))
    val checkedBinder = ElabAst.Binder(binder.localRef, binderType, binder.span, binder.isInstance)

    (
      VBinder(binder.localRef, binderType, captures, binder.isInstance),
      checkedBinder
    )
  }

  def toVBinder(binder: ElabAst.Binder): VBinder =
    VBinder(binder.localRef, binder.ty, collectBinderCaptures(binder.ty), binder.isInstance)

  /** A capture path step that takes the type of the value reached so far, for the captures of a constraint. */
  private val TypeOfStep = -1

  /**
   * The value at `path` in `value`, read by position for `capture`. A position that `value` does not have is
   * `FailedToOpenCapture`: the argument's type does not have the pattern's shape there. A universe of constant kind
   * reads as `Sort(l)` or `Lin(l)`, with its level at position 0, and one of a variable kind has no position.
   */
  private def project(value: Value, path: List[Int], capture: CoreAst.LocalRef): Value = {
    def projectStep(value: Value, idx: Int): Value =
      value match {
        case _ if idx == TypeOfStep => value.tpe
        // A universe is read by position only under a head that computes, such as `L($u)` with an alias
        // `L(u) := Lin(u)`; under a universe head, a capture is a level or kind capture (`openCaptures`). The read is
        // the same at either constant kind, and only a guess. Argument checking, instance search (`tryCandidate`) and
        // function-type equality (`defEqPi`) bind by `bindValueAndCheck`, which re-checks it (`checkOpenedPattern`):
        // the level must be the alias's argument, and the type rebuilt from it, `L(l)`, must convert with the universe
        // read. So `L($u)` opens on `Lin(l)` and is refused at `Sort(l)`, and an alias for `Sort` the other way round.
        // `bindValue` reads without the check, on the fresh values of a pattern's own telescope, which fit by
        // construction, and on an application's arguments when it is evaluated, which were checked first.
        case VSort(level) if idx == 0 => level
        case VLin(level) if idx == 0  => level
        case ConstructorValue(_, fields) =>
          fields.lift(idx).getOrElse(throw FailedToOpenCapture(capture.name, value, idx))
        case VApp(_, args, _, _) => args.lift(idx).getOrElse(throw FailedToOpenCapture(capture.name, value, idx))
        case _                   => throw FailedToOpenCapture(capture.name, value, idx)
      }

    path.foldLeft(value) { case (cur, nextIdx) => projectStep(cur, nextIdx) }
  }

  private def openCaptures(env: Env, captures: Vector[VCapture], actualTy: Value): Env = {
    captures.foldLeft(env) { (curEnv, capture) =>
      val root = capture.root match {
        case ActualType           => actualTy
        case ActualTypeClassifier => actualTy.tpe
      }
      val captureValue = capture.captureType match {
        case StructuralCapture => project(root, capture.path, capture.localRef)
        case KindCapture =>
          project(root, capture.path.init, capture.localRef) match {
            case VUniv(kind, _) => kind
            case PropTpe        => throw PropositionAsTypeCarrier()
            case other          => throw FailedToOpenCapture(capture.localRef.name, other, capture.path.last)
          }
        case LevelCapture(subtract) =>
          val projected = project(root, capture.path.init, capture.localRef) match {
            case VUniv(_, level) => level
            case PropTpe         => throw PropositionAsTypeCarrier()
            case other           => throw FailedToOpenCapture(capture.localRef.name, other, capture.path.last)
          }
          if (!Level.geq(projected, subtract)) throw InvalidLevelSubtraction(projected, subtract)
          Level.addOffset(projected, -subtract)
      }
      curEnv.putLocal(capture.localRef, captureValue)
    }
  }

  private def openPatternPrefix(env: Env, app: EPattern.App, argCount: Int): OpenedApp = {
    val fnV = evalTypeTerm(app.fn, env)
    val pi = requirePi(fnV)
    val binders = pi.binders
    val args = app.args

    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length, Some(app.span))

    var callerEnv = env
    var calleeEnv = pi.env
    val argValues = Vector.newBuilder[Value]

    binders.zip(args).take(argCount).foreach { case (binder, arg) =>
      val argValue = arg match {
        case EPattern.Capture(ref, _, constraint) =>
          val captureType = constraint match {
            case Some(c) =>
              val (constraintValue, constraintEnv) = openPattern(callerEnv, c)
              callerEnv = constraintEnv
              constraintValue
            case None => openBinderType(calleeEnv, binder.ty)._1
          }
          val value = FreshVar.freshVar(ref.name, captureType)
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

  private def openPattern(env: Env, pattern: ElabAst.TypePattern): (Value, Env) =
    pattern match {
      case app: EPattern.App =>
        val opened = openPatternPrefix(env, app, app.args.length)
        (Interpreter.evalApply(opened.fn, opened.args), opened.env)
      case EPattern.Capture(ref, span, _) => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
      case EPattern.Type(term)            => (evalTypeTerm(term, env), env)
    }

  private[telescope] def openBinderType(env: Env, binderType: ElabAst.BinderType): (Value, Env) =
    binderType match {
      case EBinderType.TypePattern(tp, _) => openPattern(env, tp)
      case EBinderType.ConstrainedCapture(ref, constraint, _) =>
        val (constraintValue, constraintEnv) = openPattern(env, constraint)
        val captureValue = FreshVar.freshVar(ref.name, constraintValue)
        (captureValue, constraintEnv.putLocal(ref, captureValue))
    }

  /** A binder of linear type gives a tracked local (`Binding.linear`), decided once from its type here. */
  private[telescope] def freshenBinder(env: Env, binder: VBinder): Env = {
    val (opened, openedEnv) = openBinderType(env, binder.ty)
    val value = FreshVar.freshVar(binder.name, opened)
    val instanceKey =
      if (binder.isInstance) Some(InstanceSearch.instanceKey(binder.name, value))
      else None
    openedEnv.putLocal(binder.localRef, value, instanceKey, linear = Linearity.isLinear(opened))
  }

  def bindValue(env: Env, binder: VBinder, actual: Value): Env = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    openedEnv.putLocal(binder.localRef, actual)
  }

  /**
   * The value of `pattern` with its captures open in `env`, and whether it has a capture, re-checking each application
   * above a capture on the values it opened, as `checkPattern` checked it on fresh ones: its arguments must instantiate
   * the head's parameter telescope, and a constrained capture must have its constraint as its type. A capture is read
   * off the actual type by position, which inverts the application only at a family or opaque head. At a head that
   * computes, such as `SList(A) := List(A)`, the value at a position need not be the head's argument, or even fit its
   * parameter, so the opened values are checked as the head's arguments, and the type rebuilt from them must then
   * convert with the actual type (`bindValueAndCheck`). An application with no capture below it is well typed already,
   * by substitution of the telescope's checked arguments.
   */
  private def checkOpenedPattern(env: Env, pattern: ElabAst.TypePattern): (Value, Boolean) =
    pattern match {
      case EPattern.Type(term) => (evalTypeTerm(term, env), false)
      case EPattern.Capture(ref, _, constraint) =>
        val value = env(ref)
        constraint.foreach(c => TypeChecker.checkType(value, checkOpenedPattern(env, c)._1))
        (value, true)
      case EPattern.App(fn, args, _) =>
        val fnV = evalTypeTerm(fn, env)
        val (argValues, argsOpened) = args.map(checkOpenedPattern(env, _)).unzip
        val opened = argsOpened.contains(true)
        if (opened) {
          val pi = requirePi(fnV)
          BinderOps.checkAndInstantiate(pi.binders, pi.env, argValues)
        }
        (Interpreter.evalApply(fnV, argValues), opened)
    }

  /**
   * Binds `actual` to `binder`, after opening its captures on the type of `actual`. The opened values must be the
   * arguments of the pattern's applications (`checkOpenedPattern`), and the type they rebuild must convert with the
   * type of `actual`. With no cumulativity, argument checking and function-type equality instantiate a telescope alike.
   */
  private[telescope] def bindValueAndCheck(env: Env, binder: VBinder, actual: Value): Env = {
    val openedEnv = openCaptures(env, binder.captures, actual.tpe)
    val expectedTy = binder.ty match {
      case EBinderType.TypePattern(tp, _) => checkOpenedPattern(openedEnv, tp)._1
      case EBinderType.ConstrainedCapture(ref, constraint, span) =>
        checkOpenedPattern(openedEnv, EPattern.Capture(ref, span, Some(constraint)))._1
    }
    TypeChecker.checkType(actual, expectedTy)
    openedEnv.putLocal(binder.localRef, actual)
  }

}
