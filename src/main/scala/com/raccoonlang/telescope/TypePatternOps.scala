package com.raccoonlang.telescope

import com.raccoonlang.CoreAst.{Term, TypePattern => CPattern}
import com.raccoonlang.ElabAst.{Term => ETerm, TypePattern => EPattern}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang._

/**
 * Type patterns are binder annotations that expose pieces of an actual argument type as ordinary locals. A binder such
 * as `b: Box($A)` means: when an argument whose type is definitionally `Box(T)` is supplied, bind `A` to `T` and make
 * it available to later binders, the codomain, and the body. Pattern heads are general type-valued functions, so
 * `Pred($A)` is handled the same way as an inductive family application.
 *
 * Implementation overview:
 *
 *   - A checked type pattern is also an ordinary type term. `compileType` turns captures into local references, so
 *     evaluation can use the same interpreter path as normal types once the captures have been put into the
 *     environment.
 *   - To open a pattern is to evaluate it into a `Value`, extending the environment with any capture locals introduced
 *     while walking nested pattern applications.
 *   - To bind a telescope binder is to instantiate that binder with an actual argument. For binders with captures,
 *     binding opens the expected type, unifies that opened type with `actual.tpe`, and materializes the opened
 *     environment with the resulting capture solutions.
 *
 * `OpenedBinderPattern` is the shared representation for this operation. Its `value` is the opened expected type; its
 * `env` contains the capture locals created while opening; its `captureDeps` are the fresh dependencies reachable from
 * those captures and not already present in the input env. Only those deps are refinable while solving a type pattern.
 *
 * Invariants:
 *
 *   - A bare `$A` cannot be opened without an expected type. Captures are introduced only from binder patterns or from
 *     arguments to a pattern head whose Pi binder supplies the expected type.
 *   - Each binder pattern is opened once at a binding site. The same opened value/env is used to create capture
 *     arguments and to bind the binder, avoiding accidentally comparing against fresh copies of the same conceptual
 *     capture.
 *   - Solving starts from an empty `EqStore` and only allows `captureDeps`. Type-pattern inference must not mutate
 *     unrelated caller equality variables.
 *   - Constrained captures solve like ordinary captures, then check their solved type against the constraint. This
 *     happens after unifying the opened binder pattern with the actual argument type so aliases such as
 *     `$A of Sort($u)` can solve both `A` and `u`.
 *   - After solving, every collected capture for a concrete argument must have changed from its fresh variable. If any
 *     remain unsolved, the pattern did not provide enough information and is rejected.
 *
 * Subtlety: capture arguments inside a pattern head bind as already-expected values rather than by immediately solving
 * their own hidden dependencies. For `Head($v)`, for example, `$v` may have a type containing hidden captures
 * introduced by `Head` 's binder telescope. Those captures are intentionally carried by `$v` and are solved later when
 * the outer binder is checked against the real argument.
 */
object TypePatternOps {
  private final case class OpenedPatternApp(fn: Value, args: Vector[Value], env: Env)
  private[raccoonlang] final case class OpenedBinderPattern(value: Value, env: Env, captureDeps: DepSet)

  private def requirePi(fn: Value): VPi =
    fn.tpe match {
      case pi: VPi => pi
      case other   => throw CannotApplyNonFunction(other)
    }

  private def hasLocal(env: Env, ref: CoreAst.LocalRef): Boolean =
    ref.id < env.locals.length && env.locals(ref.id).ref == ref

  private def compileType(pattern: ElabAst.TypePattern): ElabAst.TypeTerm = pattern match {
    case EPattern.Type(term)                       => term
    case EPattern.Capture(ref, span)               => ETerm.LocalRef(ref, span)
    case EPattern.ConstrainedCapture(ref, _, span) => ETerm.LocalRef(ref, span)
    case EPattern.App(fn, args, span)              => ETerm.App(fn, args.map(compileType), span)
    case EPattern.Pi(binders, out, classifier, span) =>
      val compiledBinders = binders.map(b => b.copy(ty = EPattern.Type(compileType(b.ty))))
      ETerm.Pi(compiledBinders, compileType(out), classifier, span)
  }

  private def collectCaptures(pattern: ElabAst.TypePattern): Vector[VCapture] =
    pattern match {
      case EPattern.Type(_)                                => Vector.empty
      case EPattern.Capture(ref, _)                        => Vector(VCapture(ref))
      case EPattern.ConstrainedCapture(ref, constraint, _) => collectCaptures(constraint) :+ VCapture(ref)
      case EPattern.App(_, args, _)                        => args.flatMap(collectCaptures)
      case EPattern.Pi(binders, out, _, _) =>
        binders.flatMap(binder => collectCaptures(binder.ty)) ++ collectCaptures(out)
    }

  private def toElabRef(caRef: CoreAst.Term.Ref): ElabAst.Term.Ref = caRef match {
    case Term.GlobalRef(name, span) => ElabAst.Term.GlobalRef(name, span)
    case Term.LocalRef(ref, span)   => ElabAst.Term.LocalRef(ref, span)
  }

  private[telescope] def toVBinder(binder: CoreAst.Binder, env: Env): (VBinder, ElabAst.Binder) = {
    def initializePiCaptures(pattern: CoreAst.TypePattern, env: Env): Env = {
      var curEnv = env

      def loop(pattern: CoreAst.TypePattern): Unit =
        pattern match {
          case CPattern.Type(_) =>

          case CPattern.Capture(ref, span) =>
            if (!hasLocal(curEnv, ref)) throw PatternCaptureNeedsExpectedType(ref.name, Some(span))

          case CPattern.ConstrainedCapture(ref, constraint, _) =>
            val (checkedConstraint, constraintEnv) = checkTopLevel(constraint, curEnv)
            val constraintValue = Interpreter.evalTypeTerm(compileType(checkedConstraint), constraintEnv)
            TypeChecker.assertType(constraintValue)
            curEnv =
              if (hasLocal(constraintEnv, ref)) constraintEnv
              else constraintEnv.putLocal(ref, FreshVar.freshVar(ref.name, constraintValue))

          case CPattern.App(_, args, _) =>
            args.foreach(loop)

          case CPattern.Pi(binders, out, _) =>
            binders.foreach(binder => loop(binder.ty))
            loop(out)
        }

      loop(pattern)
      curEnv
    }

    def checkPattern(pattern: CoreAst.TypePattern, env: Env): (ElabAst.TypePattern, Env) = {
      pattern match {
        case CPattern.Type(term) =>
          val checked = TypeChecker.checkTypeTerm(term, env)
          (EPattern.Type(checked.residual), env)
        case CPattern.Capture(ref, span) => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
        case CPattern.ConstrainedCapture(ref, constraint, span) =>
          val (checkedConstraint, constraintEnv) = checkTopLevel(constraint, env)
          val constraintTy = compileType(checkedConstraint)
          val constraintValue = Interpreter.evalTypeTerm(constraintTy, constraintEnv)
          TypeChecker.assertType(constraintValue)
          val checkedEnv =
            if (hasLocal(constraintEnv, ref)) {
              TypeChecker.checkType(constraintEnv(ref), constraintValue, constraintEnv.normalizers)
              constraintEnv
            } else {
              val captureValue = FreshVar.freshVar(ref.name, constraintValue)
              constraintEnv.putLocal(ref, captureValue)
            }
          (EPattern.ConstrainedCapture(ref, checkedConstraint, span), checkedEnv)
        case CPattern.App(fn, args, span) =>
          val fnV = TypeChecker.checkTypeTerm(fn, env).value
          val pi = requirePi(fnV)
          val binders = pi.binders

          if (binders.length != args.length) throw ArityMismatch(binders.length, args.length, Some(span))

          var patternEnv = env
          var telescopeEnv = pi.env
          val argPatterns = Vector.newBuilder[ElabAst.TypePattern]

          binders.zip(args).foreach { case (paramBinder, arg) =>
            val opened = openBinderPattern(telescopeEnv, paramBinder)
            val (argPattern, bindAsOpened) =
              arg match {
                case CPattern.Capture(ref, captureSpan) =>
                  val value =
                    if (hasLocal(patternEnv, ref)) {
                      val existing = patternEnv(ref)
                      TypeChecker.checkType(existing, opened.value, patternEnv.normalizers)
                      existing
                    } else {
                      val fresh = FreshVar.freshVar(ref.name, opened.value)
                      patternEnv = patternEnv.putLocal(ref, fresh)
                      fresh
                    }
                  (EPattern.Capture(ref, captureSpan), true)

                case other =>
                  val (checkedPattern, checkedEnv) = checkPattern(other, patternEnv)
                  patternEnv = checkedEnv
                  (checkedPattern, false)
              }

            val argValue = Interpreter.evalTypeTerm(compileType(argPattern), patternEnv)
            telescopeEnv =
              if (bindAsOpened) bindOpenedAsExpected(opened, paramBinder, argValue)
              else bindOpenedValueAndCheck(opened, paramBinder, argValue, patternEnv.normalizers)
            argPatterns += argPattern
          }

          val checkedArgs = argPatterns.result()
          val pattern = EPattern.App(toElabRef(fn), checkedArgs, span)
          (pattern, patternEnv)
        case CPattern.Pi(binders, out, span) =>
          val captureEnv = initializePiCaptures(pattern, env)
          val vBinders = Vector.newBuilder[VBinder]
          val checkedBinders = Vector.newBuilder[ElabAst.Binder]
          var binderEnv = captureEnv

          binders.foreach { binder =>
            val (vBinder, checkedBinder) = TypePatternOps.toVBinder(binder, binderEnv)
            vBinders += vBinder
            checkedBinders += checkedBinder
            binderEnv = freshenBinder(binderEnv, vBinder)
          }

          val (checkedOut, outEnv) = checkTopLevel(out, binderEnv)
          val outValue = Interpreter.evalTypeTerm(compileType(checkedOut), outEnv)
          val freshArgs = vBinders.result().map(b => binderEnv(b.localRef))
          val classifier =
            if (TypeChecker.isPropValuedType(outValue)) PropTpe
            else {
              val outLevel = TypeChecker.getUniverse(outValue).level
              val domLevels = freshArgs
                .map(v => TypeChecker.getUniverse(v.tpe))
                .collect { case VSort(level) => level }

              VSort(Level.max(domLevels :+ outLevel))
            }

          (EPattern.Pi(checkedBinders.result(), checkedOut, classifier, span), captureEnv)
      }
    }

    def checkTopLevel(pattern: CoreAst.TopLevelTP, env: Env): (ElabAst.TopLevelTP, Env) = {
      val (checked, checkedEnv) = checkPattern(pattern, env)
      checked match {
        case topLevel: ElabAst.TopLevelTP => (topLevel, checkedEnv)
        case EPattern.Capture(ref, span)  => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
      }
    }

    val (checkedPattern, checkedEnv) = checkTopLevel(binder.ty, env)
    val captures = collectCaptures(checkedPattern)
    val resType = compileType(checkedPattern)
    TypeChecker.assertType(Interpreter.evalTypeTerm(resType, checkedEnv))
    val checkedBinder = ElabAst.Binder(binder.localRef, checkedPattern, binder.span, binder.isInstance)
    val vBinder = VBinder(binder.localRef, checkedPattern, resType, captures, binder.isInstance, binder.familyParamIdx)
    if (captures.nonEmpty) validateMatchable(vBinder, env, binder.span)

    (vBinder, checkedBinder)
  }

  /**
   * Declaration-time matchability: a pattern must be able to match an actual type presented exactly as the
   * pattern's own opening. Matching the pattern against an independent fresh opening of itself (an α-renamed
   * copy) exercises every rule of `TypePatternMatcher` on the pattern's shape; failure means some capture
   * sits in a position the matcher cannot traverse (under a stuck match, a non-trivial level expression, a
   * non-pattern application spine), so no argument type could ever determine it.
   */
  private def validateMatchable(binder: VBinder, env: Env, span: Span): Unit = {
    val opened = openBinderPattern(env, binder)
    val probe = openBinderPattern(env, binder)
    try {
      TypePatternMatcher.matchBinderPattern(opened, probe.value, env.normalizers)
      ()
    } catch {
      case err: TypeError =>
        throw UnmatchablePattern(PrettyPrinter.printElabTypePattern(binder.ty), err.msg, Some(span))
    }
  }

  def toVBinder(binder: ElabAst.Binder): VBinder = {
    val expectedTy = compileType(binder.ty)
    VBinder(binder.localRef, binder.ty, expectedTy, collectCaptures(binder.ty), binder.isInstance, None)
  }

  private def openPatternApp(env: Env, app: EPattern.App): OpenedPatternApp = {
    val fnV = evalTypeTerm(app.fn, env)
    val pi = requirePi(fnV)
    val binders = pi.binders
    val args = app.args

    if (binders.length != args.length) throw ArityMismatch(binders.length, args.length, Some(app.span))

    var callerEnv = env
    var calleeEnv = pi.env
    val argValues = Vector.newBuilder[Value]

    binders.zip(args).foreach { case (binder, arg) =>
      val opened = openBinderPattern(calleeEnv, binder)
      val (argValue, bindAsOpened) = arg match {
        case EPattern.Capture(ref, _) =>
          val value =
            if (hasLocal(callerEnv, ref)) callerEnv(ref)
            else {
              val fresh = FreshVar.freshVar(ref.name, opened.value)
              callerEnv = callerEnv.putLocal(ref, fresh)
              fresh
            }
          (value, true)

        case other =>
          val (openedArg, openedEnv) = openPattern(callerEnv, other)
          callerEnv = openedEnv
          (openedArg, false)
      }
      calleeEnv =
        if (bindAsOpened) bindOpenedAsExpected(opened, binder, argValue)
        else bindOpenedValue(opened, binder, argValue)
      argValues += argValue
    }

    OpenedPatternApp(fnV, argValues.result(), callerEnv)
  }

  private def initializePiCaptures(pattern: ElabAst.TypePattern, env: Env): Env = {
    var curEnv = env

    def loop(pattern: ElabAst.TypePattern): Unit =
      pattern match {
        case EPattern.Type(_) =>

        case EPattern.Capture(ref, span) =>
          if (!hasLocal(curEnv, ref)) throw PatternCaptureNeedsExpectedType(ref.name, Some(span))

        case EPattern.ConstrainedCapture(ref, constraint, _) =>
          val (constraintValue, constraintEnv) = openPattern(curEnv, constraint)
          TypeChecker.assertType(constraintValue)
          curEnv =
            if (hasLocal(constraintEnv, ref)) constraintEnv
            else constraintEnv.putLocal(ref, FreshVar.freshVar(ref.name, constraintValue))

        case EPattern.App(_, args, _) =>
          args.foreach(loop)

        case EPattern.Pi(binders, out, _, _) =>
          binders.foreach(binder => loop(binder.ty))
          loop(out)
      }

    loop(pattern)
    curEnv
  }

  private def openPattern(env: Env, pattern: ElabAst.TypePattern): (Value, Env) =
    pattern match {
      case app: EPattern.App =>
        val opened = openPatternApp(env, app)
        (Interpreter.evalApply(opened.fn, opened.args, opened.env), opened.env)
      case EPattern.Capture(ref, span) => throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
      case EPattern.ConstrainedCapture(ref, constraint, _) =>
        val (constraintValue, constraintEnv) = openPattern(env, constraint)
        val captureValue = FreshVar.freshVar(ref.name, constraintValue)
        if (hasLocal(constraintEnv, ref)) (constraintEnv(ref), constraintEnv)
        else (captureValue, constraintEnv.putLocal(ref, captureValue))
      case EPattern.Type(term) => (evalTypeTerm(term, env), env)
      case pi: EPattern.Pi =>
        val captureEnv = initializePiCaptures(pi, env)
        (evalTypeTerm(compileType(pi), captureEnv), captureEnv)
    }

  private[raccoonlang] def openBinderPattern(env: Env, binder: VBinder): OpenedBinderPattern = {
    val (value, openedEnv) = openPattern(env, binder.ty)
    OpenedBinderPattern(value, openedEnv, captureDeps(openedEnv, binder.captures) -- env.allDeps)
  }

  private[telescope] def freshenBinder(env: Env, binder: VBinder): Env = {
    val opened = openBinderPattern(env, binder)
    val value = FreshVar.freshVar(binder.name, opened.value)
    val instanceKey =
      if (binder.isInstance) Some(InstanceSearch.instanceKey(binder.name, value))
      else None
    opened.env.putLocal(binder.localRef, value, instanceKey)
  }

  private def captureDeps(env: Env, captures: Vector[VCapture]): DepSet =
    captures.foldLeft(DepSet.empty) { case (deps, capture) => deps ++ env(capture.localRef).synDeps }

  private def isUnsolvedCapture(before: Value, after: Value): Boolean =
    (before, after) match {
      case (Var(_, beforeId, _), Var(_, afterId, _)) => beforeId == afterId
      case _                                         => false
    }

  private def solveOpenedCaptures(
      opened: OpenedBinderPattern,
      binder: VBinder,
      actual: Value,
      normalizerMap: Normalizers.NormalizerMap
  ): (Env, Value) = {
    // Everything created from here on (Pi binders opened while matching under arrows, the actual type's own
    // pattern skolems) is local to this match: ids are monotonic, so anything above the watermark must not
    // survive into a capture solution.
    val solveWatermark = FreshVar.currentId
    val eqStore = TypePatternMatcher.matchBinderPattern(opened, actual.tpe, normalizerMap)
    val materializedEnv = ValueOps.materializeEnv(opened.env, eqStore)

    binder.captures.foreach { capture =>
      val before = opened.env(capture.localRef)
      val after = materializedEnv(capture.localRef)
      if (isUnsolvedCapture(before, after)) throw PatternCaptureNeedsExpectedType(capture.localRef.name)
    }

    binder.captures.foreach { capture =>
      val deps = materializedEnv(capture.localRef).synDeps
      if (deps.nonEmpty && deps.max > solveWatermark)
        throw PatternCaptureEscapesScope(capture.localRef.name)
    }

    (materializedEnv, ValueOps.materialize(opened.value, eqStore))
  }

  private def bindOpenedValue(opened: OpenedBinderPattern, binder: VBinder, actual: Value): Env =
    if (binder.captures.isEmpty) opened.env.putLocal(binder.localRef, actual)
    else {
      val (openedEnv, expectedTy) = solveOpenedCaptures(opened, binder, actual, opened.env.normalizers)
      openedEnv.putLocal(binder.localRef, Value.ascribe(actual, expectedTy))
    }

  private def bindOpenedAsExpected(opened: OpenedBinderPattern, binder: VBinder, actual: Value): Env =
    opened.env.putLocal(binder.localRef, Value.ascribe(actual, opened.value))

  def bindValue(env: Env, binder: VBinder, actual: Value): Env = {
    if (binder.captures.isEmpty) env.putLocal(binder.localRef, actual)
    else {
      val (openedEnv, expectedTy) = solveOpenedCaptures(openBinderPattern(env, binder), binder, actual, env.normalizers)
      openedEnv.putLocal(binder.localRef, Value.ascribe(actual, expectedTy))
    }
  }

  private def bindOpenedValueAndCheck(
      opened: OpenedBinderPattern,
      binder: VBinder,
      actual: Value,
      normalizerMap: Normalizers.NormalizerMap
  ): Env = {
    val (openedEnv, expectedTy) =
      if (binder.captures.isEmpty) (opened.env, opened.value)
      else solveOpenedCaptures(opened, binder, actual, normalizerMap)
    TypeChecker.checkType(actual, expectedTy, normalizerMap)
    openedEnv.putLocal(binder.localRef, Value.ascribe(actual, expectedTy))
  }

  private[telescope] def bindValueAndCheck(
      env: Env,
      binder: VBinder,
      actual: Value,
      normalizerMap: Normalizers.NormalizerMap
  ): Env =
    bindOpenedValueAndCheck(openBinderPattern(env, binder), binder, actual, normalizerMap)

}
