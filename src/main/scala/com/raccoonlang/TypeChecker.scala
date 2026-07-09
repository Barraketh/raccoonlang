package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang.ValueQuote.{quoteContext, quotePiType, quoteTerm, quoteType}
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

object TypeChecker {
  private final case class CheckedPi(
      vpi: VPi,
      bodyContext: TypingContext,
      outTy: Value,
      residual: EA.Term.Pi
  )
  final case class CheckedTerm(value: Value, residual: EA.Term)
  private[raccoonlang] final case class CheckedTypeTerm(value: Value, residual: EA.TypeTerm)
  private final case class CheckedApply(value: Value, residual: EA.Term.App)

  // An argument whose elaboration is deferred until its binder's expected type is known.
  private final case class PendingArg(
      synthArg: TypingContext => CheckedTerm,
      checkArg: (Value, TypingContext) => CheckedTerm
  ) {
    // Push the expected type into checking only when it is closed over the caller's env;
    // open expected types cannot be quoted into residual motives or implicit arguments.
    def check(expectedTy: Value, context: TypingContext): CheckedTerm =
      if (canQuoteFromContext(expectedTy, context)) checkArg(expectedTy, context)
      else synthArg(context)
  }

  private object PendingArg {
    def term(t: CA.Term): PendingArg =
      PendingArg(synthTerm(t, _), (expected, context) => checkTerm(t, expected, context))

    def typeTerm(t: CA.TypeTerm): PendingArg = {
      def toTerm(checked: CheckedTypeTerm) = CheckedTerm(checked.value, checked.residual)
      PendingArg(
        context => toTerm(checkTypeTerm(t, context)),
        (expected, context) => toTerm(checkTypeTerm(t, context, Some(expected)))
      )
    }

    def checked(c: CheckedTerm): PendingArg = PendingArg(_ => c, (_, _) => c)
  }

  def sortLeq(a: Value, b: Value): Boolean = {
    (a, b) match {
      case (Value.VSort(u), Value.VSort(v)) => Level.leq(u, v)
      case (l1: Level, l2: Level)           => Level.leq(l1, l2)
      case (l1: Level, v: Var)              => Level.leq(l1, Level.mk(v.id))
      case (v: Var, l2: Level)              => Level.leq(Level.mk(v.id), l2)
      case _                                => false
    }
  }

  def checkFits(actual: Value, expected: Value): Unit =
    if (!ValueEquivalence.defEq(actual, expected, propIrrelevant = true) && !sortLeq(actual, expected))
      throw TypeMismatch(expected, actual)

  def checkType(value: Value, tyVal: Value): Unit =
    checkFits(value.tpe, tyVal)

  def getUniverse(value: Value): VSort = {
    value.tpe match {
      case u: VSort => u
      case _        => throw NotAType(value.tpe)
    }
  }

  // A type is Prop-valued when it is itself a proposition (lives in Prop). The sort Prop is NOT
  // Prop-valued: `Prop : Sort 1`, so e.g. `Nat -> Prop` lives in Type, and predicates are data,
  // not proofs. Conflating the two made predicates proof-irrelevant (derived False).
  def isPropValuedType(value: Value): Boolean =
    getUniverse(value) == PropTpe

  private def assertNonRawRecursive(v: Value): Unit = {
    v match {
      case VLam(_, id, LamBody.Native(_, _, true)) => throw InvalidRecursiveOccurrence(s"$id")
      case _                                       =>
    }
  }

  private[raccoonlang] def constrainFits(actual: Value, expected: Value, eqStore: EqStore): EqStore =
    ValueEquivalence.tryUnify(actual, expected, eqStore, ValueEquivalence.UnifyMode.Solve) match {
      case Right(next) => next
      case Left(_) =>
        checkFits(ValueOps.materialize(actual, eqStore), ValueOps.materialize(expected, eqStore))
        eqStore
    }

  private def checkArgFits(actual: Value, expectedTy: Value, eqStore: EqStore): EqStore =
    constrainFits(actual.tpe, expectedTy, eqStore)

  private def checkTermFits(checked: CheckedTerm, expectedTy: Value): CheckedTerm = {
    checkType(checked.value, expectedTy)
    CheckedTerm(Value.ascribe(checked.value, expectedTy), checked.residual)
  }

  private def checkTypeTermFits(checked: CheckedTypeTerm, expectedTy: Value): CheckedTypeTerm = {
    checkType(checked.value, expectedTy)
    CheckedTypeTerm(Value.ascribe(checked.value, expectedTy), checked.residual)
  }

  private def canQuoteFromContext(value: Value, context: TypingContext): Boolean =
    (value.synDeps -- Value.envDeps(context.env)).isEmpty

  private def expectedPiResidual(expectedTy: Value, context: TypingContext, span: Span): Option[EA.Term.Pi] =
    try
      expectedTy match {
        case pi: VPi => Some(quotePiType(pi, quoteContext(context.env), span))
        case _       => None
      }
    catch {
      case _: CannotQuoteValue => None
    }

  private def quoteImplicitArg(
      value: Value,
      context: TypingContext,
      eqStore: EqStore,
      span: Span,
      name: String
  ): EA.Term =
    try
      ValueQuote.quoteTerm(
        ValueOps.materialize(value, eqStore),
        quoteContext(ValueOps.materializeEnv(context.env, eqStore)),
        span
      )
    catch {
      case e: CannotQuoteValue =>
        throw e.copy(reason = s"${e.reason} while quoting implicit $name")
    }

  private def freshMetaValue(name: String, tpe: Value, eqStore: EqStore): (Value, EqStore) = {
    val (id, value) = FreshVar.freshValue(name, tpe)
    (value, eqStore.allow(DepSet(id)))
  }

  private def freshPlaceholderValue(name: String, tpe: Value, deps: DepSet.Builder): Value = {
    val (id, value) = FreshVar.freshValue(name, tpe)
    deps.add(id)
    value
  }

  private def refineFromExpectedResult(
      pi: VPi,
      binderIdx: Int,
      calleeEnv: Env[Value],
      eqStore: EqStore,
      expected: Value
  ): EqStore = {
    val placeholderDepsBuilder = DepSet.newBuilder
    var probeEnv = calleeEnv

    pi.binders.drop(binderIdx).foreach { binder =>
      val expectedTy = ValueOps.materialize(Interpreter.evalTypeTerm(binder.ty, probeEnv), eqStore)
      val placeholder = freshPlaceholderValue(binder.name, expectedTy, placeholderDepsBuilder)
      probeEnv = BinderOps.bindValue(probeEnv, binder, placeholder)
    }

    val placeholderDeps = placeholderDepsBuilder.result()
    try {
      val next = constrainFits(pi.codomain(probeEnv), expected, eqStore)
      val invalidSolution =
        next.subst.exists { case (id, solution) =>
          !eqStore.subst.contains(id) && solution.synDeps.intersects(placeholderDeps)
        }
      if (invalidSolution) eqStore else next
    } catch {
      case _: TypeMismatch | _: UnificationFailed => eqStore
    }
  }

  private def checkApplyChecked(
      fnValue: Value,
      fnResidual: EA.Term,
      providedArgs: Vector[PendingArg],
      context: TypingContext,
      span: Span,
      expectedResult: Option[Value] = None
  ): CheckedApply =
    fnValue.tpe match {
      case pi: VPi =>
        // Telescope zones: [level implicits][other implicits][explicits].
        // Level implicits are always inferred. Callers supply either just the
        // explicit args (all implicits inferred) or all non-level args.
        val numImplicit = pi.binders.count(_.isImplicit)
        val numExplicit = pi.binders.length - numImplicit
        val numFillable = numImplicit - pi.numLevelParams
        val implicitsSupplied =
          if (providedArgs.length == numExplicit) false
          else if (providedArgs.length == numExplicit + numFillable) true
          else {
            val alt = Option.when(numFillable > 0)(numExplicit + numFillable)
            throw ArityMismatch(numExplicit, providedArgs.length, Some(span), alt)
          }

        val args = Vector.newBuilder[Value]
        val residualArgs = Vector.newBuilder[Either[(String, Value), EA.Term]]
        var calleeEnv = pi.env
        var eqStore = EqStore.empty
        var providedIdx = 0

        pi.binders.zipWithIndex.foreach { case (binder, binderIdx) =>
          val isLevelBinder = binderIdx < pi.numLevelParams
          val consumesArg = !binder.isImplicit || (implicitsSupplied && !isLevelBinder)
          val (arg, residualArg) =
            if (!consumesArg) {
              val expectedTy = ValueOps.materialize(Interpreter.evalTypeTerm(binder.ty, calleeEnv), eqStore)
              val (value, nextEq) = freshMetaValue(binder.name, expectedTy, eqStore)
              eqStore = nextEq
              (value, Left(binder.name -> value))
            } else {
              val evaluatedTy = ValueOps.materialize(Interpreter.evalTypeTerm(binder.ty, calleeEnv), eqStore)
              val expectedTy = expectedResult match {
                // Probing the expected result can only sharpen this binder's type when it
                // still mentions unsolved implicit metas.
                case Some(expected) if evaluatedTy.synDeps.intersects(eqStore.refinable) =>
                  eqStore = refineFromExpectedResult(pi, binderIdx, calleeEnv, eqStore, expected)
                  ValueOps.materialize(evaluatedTy, eqStore)
                case _ => evaluatedTy
              }
              val checked = providedArgs(providedIdx).check(expectedTy, context)
              providedIdx += 1
              eqStore = checkArgFits(checked.value, expectedTy, eqStore)
              assertNonRawRecursive(checked.value)
              (checked.value, Right(checked.residual))
            }

          calleeEnv = BinderOps.bindValue(calleeEnv, binder, arg)
          args += arg
          residualArgs += residualArg
        }

        expectedResult.foreach { expected =>
          eqStore = constrainFits(pi.codomain(calleeEnv), expected, eqStore)
        }

        val finalArgs = args.result().map(arg => ValueOps.materialize(arg, eqStore))
        val finalResidualArgs = residualArgs.result().map {
          case Left((name, value)) => quoteImplicitArg(value, context, eqStore, span, name)
          case Right(term)         => term
        }
        val residual = EA.Term.App(fnResidual, finalResidualArgs, span)
        val rawValue = Interpreter.evalApply(fnValue, finalArgs)
        val value = expectedResult match {
          case Some(expected) => Value.ascribe(rawValue, ValueOps.materialize(expected, eqStore))
          case None           => rawValue
        }
        CheckedApply(value, residual)

      case _ => throw CannotApplyNonFunction(fnValue)
    }

  private def elabRef(ref: CA.Term.Ref): EA.Term.Ref =
    ref match {
      case CA.Term.GlobalRef(name, span) => EA.Term.GlobalRef(name, span)
      case CA.Term.LocalRef(ref, span)   => EA.Term.LocalRef(ref, span)
    }

  private def checkPi(pi: CA.Term.Pi, context: TypingContext): CheckedPi = {
    // Telescope discipline (zones + implicit prefix) is enforced by BinderOps.toVBinders.
    val checkedBinders = BinderOps.toVBinders(pi.binders, context)
    val vBinders = checkedBinders.vBinders
    val binderContext = checkedBinders.context
    val binderEnv = binderContext.env
    val checkedOut = checkTypeTerm(pi.out, binderContext)
    val outV = checkedOut.value
    val freshArgs = vBinders.map(binder => binderEnv(binder.localRef))
    val classifier =
      if (isPropValuedType(outV)) PropTpe
      else {
        getUniverse(outV) match {
          case VSort(outLevel) =>
            val domLevels: Vector[Level] = freshArgs
              .map(v => getUniverse(v.tpe))
              .collect { case VSort(level) => level }

            VSort(Level.max(domLevels :+ outLevel))
        }
      }
    val checkedPi =
      EA.Term.Pi(checkedBinders.elabBinders, checkedOut.residual, classifier, checkedBinders.numLevelParams, pi.span)
    CheckedPi(evalPi(checkedPi, context.env, vBinders), binderContext, outV, checkedPi)
  }

  private[raccoonlang] def checkTypeTerm(
      term: CA.TypeTerm,
      context: TypingContext
  ): CheckedTypeTerm =
    checkTypeTerm(term, context, expectedTy = None)

  private def checkTypeTerm(
      term: CA.TypeTerm,
      context: TypingContext,
      expectedTy: Option[Value]
  ): CheckedTypeTerm = {
    val checked =
      term match {
        case t: CA.Term.TApp =>
          val fn = checkTypeTerm(t.fn, context)
          val args = t.args.map(PendingArg.typeTerm)
          val checkedApp = checkApplyChecked(fn.value, fn.residual, args, context, t.span, expectedTy)
          CheckedTypeTerm(checkedApp.value, checkedApp.residual)
        case CA.Term.TSelect(base, field, span) =>
          val checkedBase = checkTypeTerm(base, context)
          val checked =
            checkSelect(CheckedTerm(checkedBase.value, checkedBase.residual), field, span, context, expectedTy)
          checked.residual match {
            case tt: EA.TypeTerm => CheckedTypeTerm(checked.value, tt)
            case other           => throw NotAType(checked.value, Some(other.span))
          }
        case derive: CA.Term.Derive =>
          val goal = getType(derive.goal, context)
          val value = InstanceSearch.solve(goal, context)
          CheckedTypeTerm(value, quoteType(value, quoteContext(context.env), derive.span))
        case pi: CA.Term.Pi =>
          val checked = checkPi(pi, context)
          CheckedTypeTerm(checked.vpi, checked.residual)
        case ref: CA.Term.Ref =>
          val residual = elabRef(ref)
          CheckedTypeTerm(Interpreter.evalTypeTerm(residual, context.env), residual)
      }
    expectedTy.map(expected => checkTypeTermFits(checked, expected)).getOrElse(checked)
  }

  // Returning the residual term lets callers preserve checked let/lambda structure instead of re-checking.
  private def checkBody(body: CA.Term.Body, context: TypingContext, expectedTy: Option[Value] = None): CheckedTerm = {
    val checkedLets = Vector.newBuilder[EA.Let]
    var curContext = context

    body.lets.foreach { l =>
      val checkedTy = l.ty.map(tyTerm => checkTypeTerm(tyTerm, curContext))
      val checkedValue = checkedTy match {
        case Some(ty) => checkTerm(l.value, ty.value, curContext)
        case None     => checkTerm(l.value, curContext)
      }
      val bound = checkedTy.fold(checkedValue.value)(ty => Value.ascribe(checkedValue.value, ty.value))

      checkedLets += EA.Let(l.localRef, checkedTy.map(_.residual), checkedValue.residual, l.span, l.isInstance)
      curContext = curContext.putLocal(l.localRef, bound, isInstance = l.isInstance)
    }

    val checkedRes = expectedTy match {
      case Some(expected) => checkTerm(body.res, expected, curContext)
      case None           => checkTerm(body.res, curContext)
    }
    CheckedTerm(checkedRes.value, EA.Term.Body(checkedLets.result(), checkedRes.residual, body.span))
  }

  def inductiveFamilyOf(value: Value): Option[InductiveFamilyInstance] =
    value match {
      case InductiveFamilyValue(instance) => Some(instance)
      case _                              => None
    }

  private def checkSelect(
      base: CheckedTerm,
      field: String,
      span: Span,
      context: TypingContext,
      expectedTy: Option[Value] = None
  ): CheckedApply = {
    val vType = base.value.tpe
    val family = inductiveFamilyOf(vType).getOrElse(throw NotAType(vType))
    val indName = family.head.name
    val meta = family.meta

    if (!meta.isStruct) throw NotAStruct(indName)

    val selectorName = s"$indName.$field"
    val selector = context.env(selectorName)
    checkApplyChecked(
      selector,
      EA.Term.GlobalRef(selectorName, span),
      Vector(PendingArg.checked(base)),
      context,
      span,
      expectedTy
    )
  }

  private def checkLam(l: CA.Term.Lam, context: TypingContext): CheckedTerm = {
    val checkedVpi = checkPi(l.ty, context)
    val vpi = checkedVpi.vpi
    val bodyContext = checkedVpi.bodyContext
    val bodyEnv = bodyContext.env

    // Recursive self references stay local for the whole pipeline, even if the source used a qualified name.
    // While checking, the local contains a raw recursive value that enforces the decrease and can only appear as an
    // application head, so the body cannot store it as an ordinary value. The checked lambda keeps the same self ref;
    // when the lambda runs, Interpreter.runLam binds that ref to the final VLam. The declaration is published to
    // globals separately after the body has checked.
    val recurEnv =
      l.recursion match {
        case Some(CA.Recursion(ref, decreaseSpec)) =>
          val name = l.name.getOrElse(throw WTF("Recursive lambda must have a name", Some(l.span)))
          val recursiveSelf = TerminationChecker.rawRecursiveSelf(name, vpi, decreaseSpec, bodyContext)
          bodyEnv.putLocal(ref, recursiveSelf)
        case None => bodyEnv
      }
    val bodyContextWithRecursion = bodyContext.withEnv(recurEnv)

    val checkedBody = l.body match {
      case b: CA.Term.Body => checkBody(b, bodyContextWithRecursion, Some(checkedVpi.outTy))
      case _               => checkTerm(l.body, checkedVpi.outTy, bodyContextWithRecursion)
    }
    assertNonRawRecursive(checkedBody.value)

    checkType(checkedBody.value, checkedVpi.outTy)
    val checkedLam =
      EA.Term.Lam(
        checkedVpi.residual,
        checkedBody.residual,
        l.span,
        l.name,
        l.recursion.map(_.selfRef)
      )
    CheckedTerm(Interpreter.evalLam(checkedLam, vpi, context.env), checkedLam)
  }

  def getType(term: CA.TypeTerm, context: TypingContext): Value = {
    val res = checkTypeTerm(term, context).value
    assertType(res)
    res
  }

  def assertType(value: Value): Unit = {
    value match {
      case PropTpe =>
      case _ =>
        value.tpe match {
          case _: VSort | PropTpe =>
          case _                  => throw NotAType(value)
        }
    }
  }

  private def tryInstantiateImplicitOnly(
      checked: CheckedTerm,
      expectedTy: Value,
      context: TypingContext,
      span: Span
  ): Option[CheckedTerm] =
    checked.value.tpe match {
      case pi: VPi if pi.binders.forall(_.isImplicit) =>
        try {
          val app = checkApplyChecked(checked.value, checked.residual, Vector.empty, context, span, Some(expectedTy))
          Some(CheckedTerm(app.value, app.residual))
        } catch {
          case _: TypeMismatch | _: UnificationFailed => None
        }
      case _ => None
    }

  // The implicit-prefix discipline makes this the only eta-adaptation needed for bare polymorphic functions.
  private def tryInstantiateLeadingImplicits(
      checked: CheckedTerm,
      expectedTy: Value,
      context: TypingContext,
      span: Span
  ): Option[CheckedTerm] =
    (checked.value.tpe, expectedTy) match {
      case (actualPi: VPi, expectedPi: VPi)
          if actualPi.binders.headOption.exists(_.isImplicit) &&
            !actualPi.binders.forall(_.isImplicit) =>
        expectedPiResidual(expectedTy, context, span).flatMap { residualPi =>
          try {
            val bodyContext = BinderOps.freshen(expectedPi.binders, context)
            val bodyEnv = bodyContext.env
            val bodyArgs =
              expectedPi.binders.map { binder =>
                val value = bodyEnv(binder.localRef)
                val residual = EA.Term.LocalRef(binder.localRef, binder.ty.span)
                PendingArg.checked(CheckedTerm(value, residual))
              }
            val app =
              checkApplyChecked(
                checked.value,
                checked.residual,
                bodyArgs,
                bodyContext,
                span,
                Some(expectedPi.codomain(bodyEnv))
              )
            val lam = EA.Term.Lam(residualPi, app.residual, span, name = None, recursiveSelf = None)
            Some(CheckedTerm(Interpreter.evalLam(lam, expectedPi, context.env), lam))
          } catch {
            case _: TypeMismatch | _: UnificationFailed | _: ArityMismatch | _: CannotQuoteValue => None
          }
        }

      case _ => None
    }

  private def synthTerm(term: CA.Term, context: TypingContext): CheckedTerm =
    try {
      term match {
        case CA.Term.Select(base, field, span) =>
          val checkedBase = synthTerm(base, context)
          val checked = checkSelect(CheckedTerm(checkedBase.value, checkedBase.residual), field, span, context)
          CheckedTerm(checked.value, checked.residual)
        case l: CA.Term.Lam => checkLam(l, context)
        case app: CA.Term.App =>
          val checkedFn = synthTerm(app.fn, context)
          val checkedArgs = app.args.map(PendingArg.term)
          val checkedApp = checkApplyChecked(checkedFn.value, checkedFn.residual, checkedArgs, context, app.span)
          CheckedTerm(checkedApp.value, checkedApp.residual)
        case derive: CA.Term.Derive =>
          val goal = getType(derive.goal, context)
          val value = InstanceSearch.solve(goal, context)
          CheckedTerm(value, quoteTerm(value, quoteContext(context.env), derive.span))
        case m: CA.Term.Match => MatchChecker.checkMatch(m, context)
        case b: CA.Term.Body  => checkBody(b, context)
        case term: CA.TypeTerm =>
          val checked = checkTypeTerm(term, context)
          CheckedTerm(checked.value, checked.residual)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw e.withSpan(term.span)
    }

  // Adapt a synthesized value to the expected type: instantiate leading implicit binders
  // (by application or eta-expansion) if that helps, otherwise plain subsumption.
  private def subsume(checked: CheckedTerm, expectedTy: Value, context: TypingContext, span: Span): CheckedTerm =
    tryInstantiateImplicitOnly(checked, expectedTy, context, span)
      .orElse(tryInstantiateLeadingImplicits(checked, expectedTy, context, span))
      .getOrElse(checkTermFits(checked, expectedTy))

  def checkTerm(term: CA.Term, context: TypingContext): CheckedTerm =
    synthTerm(term, context)

  def checkTerm(term: CA.Term, expectedTy: Value, context: TypingContext): CheckedTerm =
    try {
      term match {
        case CA.Term.Select(base, field, span) =>
          val checkedBase = synthTerm(base, context)
          val checked =
            checkSelect(CheckedTerm(checkedBase.value, checkedBase.residual), field, span, context, Some(expectedTy))
          CheckedTerm(checked.value, checked.residual)
        case app: CA.Term.App =>
          val checkedFn = synthTerm(app.fn, context)
          val checkedArgs = app.args.map(PendingArg.term)
          val checkedApp =
            checkApplyChecked(checkedFn.value, checkedFn.residual, checkedArgs, context, app.span, Some(expectedTy))
          CheckedTerm(checkedApp.value, checkedApp.residual)
        case m: CA.Term.Match => MatchChecker.checkMatch(m, context, Some(expectedTy))
        case b: CA.Term.Body  => checkBody(b, context, Some(expectedTy))
        // Refs are matched before the TypeTerm case (Ref <: TypeTerm) so bare references
        // get implicit instantiation / eta-adaptation against the expected type.
        case ref: CA.Term.Ref => subsume(synthTerm(ref, context), expectedTy, context, ref.span)
        case term: CA.TypeTerm =>
          val checked = checkTypeTerm(term, context, Some(expectedTy))
          CheckedTerm(checked.value, checked.residual)
        case l: CA.Term.Lam => subsume(synthTerm(l, context), expectedTy, context, l.span)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw e.withSpan(term.span)
    }

}
