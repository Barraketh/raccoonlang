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
  private final case class CheckedArg(value: Value, residual: EA.Term)
  private final case class CheckedApply(value: Value, residual: EA.Term.App)
  private sealed trait PendingArg {
    def synth(context: TypingContext): CheckedArg
    def check(expectedTy: Value, context: TypingContext): CheckedArg
  }
  private final case class PendingTermArg(term: CA.Term) extends PendingArg {
    override def synth(context: TypingContext): CheckedArg = {
      val checked = synthTerm(term, context)
      CheckedArg(checked.value, checked.residual)
    }

    override def check(expectedTy: Value, context: TypingContext): CheckedArg =
      if (canQuoteFromContext(expectedTy, context)) {
        val checked = TypeChecker.checkTerm(term, expectedTy, context)
        CheckedArg(checked.value, checked.residual)
      } else synth(context)
  }
  private final case class PendingTypeArg(term: CA.TypeTerm) extends PendingArg {
    override def synth(context: TypingContext): CheckedArg = {
      val checked = checkTypeTerm(term, context)
      CheckedArg(checked.value, checked.residual)
    }

    override def check(expectedTy: Value, context: TypingContext): CheckedArg =
      if (canQuoteFromContext(expectedTy, context)) {
        val checked = checkTypeTerm(term, expectedTy, context)
        CheckedArg(checked.value, checked.residual)
      } else synth(context)
  }
  private final case class PendingCheckedArg(checked: CheckedArg) extends PendingArg {
    override def synth(context: TypingContext): CheckedArg = checked
    override def check(expectedTy: Value, context: TypingContext): CheckedArg = checked
  }
  final case class CheckedTerm(value: Value, residual: EA.Term)
  private[raccoonlang] final case class CheckedTypeTerm(value: Value, residual: EA.TypeTerm)

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

  def isPropValue(value: Value): Boolean = value match {
    case PropTpe => true
    case _       => false
  }

  def isPropValuedType(value: Value): Boolean =
    isPropValue(value) || getUniverse(value) == PropTpe

  private def assertNonRawRecursive(v: Value): Unit = {
    v match {
      case VLam(_, id, LamBody.Native(_, _, true)) => throw InvalidRecursiveOccurrence(s"$id")
      case _                                       =>
    }
  }

  private[raccoonlang] def constrainFits(actual: Value, expected: Value, eqStore: EqStore): EqStore =
    ValueEquivalence.tryUnify(actual, expected, eqStore) match {
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
    val fresh = FreshVar.freshVar(name, tpe)
    val nextEq = eqStore.allow(DepSet(fresh.id))
    val value =
      tpe match {
        case LevelTpe => Level.mk(fresh.id)
        case _        => fresh: Value
      }
    (value, nextEq)
  }

  private def freshPlaceholderValue(name: String, tpe: Value, deps: DepSet.Builder): Value = {
    val fresh = FreshVar.freshVar(name, tpe)
    deps.add(fresh.id)
    tpe match {
      case LevelTpe => Level.mk(fresh.id)
      case _        => fresh: Value
    }
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
        val args = Vector.newBuilder[Value]
        val residualArgs = Vector.newBuilder[Either[(String, Value), EA.Term]]
        var calleeEnv = pi.env
        var eqStore = EqStore.empty
        var providedIdx = 0

        pi.binders.zipWithIndex.foreach { case (binder, binderIdx) =>
          val remainingProvided = providedArgs.length - providedIdx
          val remainingExplicit = pi.binders.drop(binderIdx + 1).count(!_.isImplicit)
          val shouldConsumeImplicit = binder.isImplicit && remainingProvided > remainingExplicit
          def inferImplicit(): (Value, Either[(String, Value), EA.Term]) = {
            val expectedTy = ValueOps.materialize(Interpreter.evalTypeTerm(binder.ty, calleeEnv), eqStore)
            val (value, nextEq) = freshMetaValue(binder.name, expectedTy, eqStore)
            eqStore = nextEq
            (value, Left(binder.name -> value))
          }
          val (arg, residualArg) =
            if (binder.isImplicit && !shouldConsumeImplicit) {
              inferImplicit()
            } else if (binder.isImplicit && providedIdx < providedArgs.length) {
              expectedResult.foreach { expected =>
                eqStore = refineFromExpectedResult(pi, binderIdx, calleeEnv, eqStore, expected)
              }
              val expectedTy = ValueOps.materialize(Interpreter.evalTypeTerm(binder.ty, calleeEnv), eqStore)
              val before = eqStore
              try {
                val checked = providedArgs(providedIdx).check(expectedTy, context)
                eqStore = checkArgFits(checked.value, expectedTy, eqStore)
                assertNonRawRecursive(checked.value)
                providedIdx += 1
                (checked.value, Right(checked.residual))
              } catch {
                case _: TypeMismatch | _: UnificationFailed =>
                  eqStore = before
                  inferImplicit()
              }
            } else if (providedIdx < providedArgs.length) {
              expectedResult.foreach { expected =>
                eqStore = refineFromExpectedResult(pi, binderIdx, calleeEnv, eqStore, expected)
              }
              val expectedTy = ValueOps.materialize(Interpreter.evalTypeTerm(binder.ty, calleeEnv), eqStore)
              val checked = providedArgs(providedIdx).check(expectedTy, context)
              providedIdx += 1
              eqStore = checkArgFits(checked.value, expectedTy, eqStore)
              assertNonRawRecursive(checked.value)
              (checked.value, Right(checked.residual))
            } else {
              val explicitArity = pi.binders.count(!_.isImplicit)
              throw ArityMismatch(explicitArity, providedArgs.length, Some(span))
            }

          calleeEnv = BinderOps.bindValue(calleeEnv, binder, arg)
          args += arg
          residualArgs += residualArg
        }

        expectedResult.foreach { expected =>
          eqStore = constrainFits(pi.codomain(calleeEnv), expected, eqStore)
        }

        if (providedIdx != providedArgs.length) {
          val explicitArity = pi.binders.count(!_.isImplicit)
          throw ArityMismatch(explicitArity, providedArgs.length, Some(span))
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

  private def checkImplicitPrefixDiscipline(binders: Vector[CA.Binder]): Unit = {
    var seenNonImplicit = false
    binders.foreach { binder =>
      if (binder.isImplicit && seenNonImplicit)
        throw NonLeadingImplicitParam(binder.name, Some(binder.span))
      if (!binder.isImplicit)
        seenNonImplicit = true
    }
  }

  private def checkPi(pi: CA.Term.Pi, context: TypingContext): CheckedPi = {
    checkImplicitPrefixDiscipline(pi.binders)
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
      EA.Term.Pi(checkedBinders.elabBinders, checkedOut.residual, classifier, pi.span)
    CheckedPi(evalPi(checkedPi, context.env, vBinders), binderContext, outV, checkedPi)
  }

  private[raccoonlang] def checkTypeTerm(
      term: CA.TypeTerm,
      context: TypingContext
  ): CheckedTypeTerm =
    checkTypeTerm(term, context, expectedTy = None)

  private def checkTypeTerm(
      term: CA.TypeTerm,
      expectedTy: Value,
      context: TypingContext
  ): CheckedTypeTerm =
    checkTypeTerm(term, context, expectedTy = Some(expectedTy))

  private def checkTypeTerm(
      term: CA.TypeTerm,
      context: TypingContext,
      expectedTy: Option[Value]
  ): CheckedTypeTerm = {
    val checked =
      term match {
        case t: CA.Term.TApp =>
          val fn = checkTypeTerm(t.fn, context)
          val args = t.args.map(PendingTypeArg.apply)
          val checkedApp = checkApplyChecked(fn.value, fn.residual, args, context, t.span, expectedTy)
          CheckedTypeTerm(checkedApp.value, checkedApp.residual)
        case CA.Term.TSelect(base, field, span) =>
          val checkedBase = checkTypeTerm(base, context)
          val checked =
            checkSelect(CheckedArg(checkedBase.value, checkedBase.residual), field, span, context, expectedTy)
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
      val (resTyTerm, checkedValue, withType) =
        l.ty match {
          case Some(tyTerm) =>
            val checkedTy = checkTypeTerm(tyTerm, curContext)
            val tyV = checkedTy.value
            val checkedValue = checkTerm(l.value, tyV, curContext)
            (Some(checkedTy.residual), checkedValue, Value.ascribe(checkedValue.value, tyV))
          case None =>
            val checkedValue = checkTerm(l.value, curContext)
            (None, checkedValue, checkedValue.value)
        }

      checkedLets += EA.Let(l.localRef, resTyTerm, checkedValue.residual, l.span, l.isInstance)
      curContext = curContext.putLocal(l.localRef, withType, isInstance = l.isInstance)
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
      base: CheckedArg,
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
      Vector(PendingCheckedArg(base)),
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
                PendingCheckedArg(CheckedArg(value, residual))
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
          val checked = checkSelect(CheckedArg(checkedBase.value, checkedBase.residual), field, span, context)
          CheckedTerm(checked.value, checked.residual)
        case l: CA.Term.Lam => checkLam(l, context)
        case app: CA.Term.App =>
          val checkedFn = synthTerm(app.fn, context)
          val checkedArgs = app.args.map(PendingTermArg.apply)
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
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }

  def checkTerm(term: CA.Term, context: TypingContext): CheckedTerm =
    synthTerm(term, context)

  def checkTerm(term: CA.Term, expectedTy: Value, context: TypingContext): CheckedTerm =
    try {
      term match {
        case CA.Term.Select(base, field, span) =>
          val checkedBase = synthTerm(base, context)
          val checked =
            checkSelect(CheckedArg(checkedBase.value, checkedBase.residual), field, span, context, Some(expectedTy))
          CheckedTerm(checked.value, checked.residual)
        case app: CA.Term.App =>
          val checkedFn = synthTerm(app.fn, context)
          val checkedArgs = app.args.map(PendingTermArg.apply)
          val checkedApp =
            checkApplyChecked(checkedFn.value, checkedFn.residual, checkedArgs, context, app.span, Some(expectedTy))
          CheckedTerm(checkedApp.value, checkedApp.residual)
        case m: CA.Term.Match => MatchChecker.checkMatch(m, context, Some(expectedTy))
        case b: CA.Term.Body  => checkBody(b, context, Some(expectedTy))
        case ref: CA.Term.Ref =>
          val checked = synthTerm(ref, context)
          tryInstantiateImplicitOnly(checked, expectedTy, context, ref.span)
            .orElse(tryInstantiateLeadingImplicits(checked, expectedTy, context, ref.span))
            .getOrElse(checkTermFits(checked, expectedTy))
        case term: CA.TypeTerm =>
          val checked = checkTypeTerm(term, context, Some(expectedTy))
          CheckedTerm(checked.value, checked.residual)
        case _ =>
          val checked = synthTerm(term, context)
          tryInstantiateImplicitOnly(checked, expectedTy, context, term.span)
            .orElse(tryInstantiateLeadingImplicits(checked, expectedTy, context, term.span))
            .getOrElse(checkTermFits(checked, expectedTy))
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }

}
