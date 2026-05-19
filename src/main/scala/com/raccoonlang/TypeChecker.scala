package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.{BinderOps, ConstructorOps}
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

object TypeChecker {
  final case class Checked(value: Value, term: EA.Term)
  final case class CheckedType(value: Value, term: EA.TypeTerm)
  private final case class CheckedPi(value: VPi, term: EA.Term.Pi)
  private final case class CheckedSelect(value: Value, term: EA.Term.Select)
  private final case class InductiveFamily(name: String, meta: InductiveMeta)

  def sortLeq(a: Value, b: Value)(implicit eqStore: EqStore): Boolean = {
    (a, b).caseOf {
      case (Value.VSort(u), Value.VSort(v)) => Level.leq(u, v)
      case (l1: Level, l2: Level)           => Level.leq(l1, l2)
      case (l1: Level, v: Var)              => Level.leq(l1, Level.mk(v.id))
      case (v: Var, l2: Level)              => Level.leq(Level.mk(v.id), l2)
      case _                                => false
    }
  }

  def checkFits(actual: Value, expected: Value, normalizerMap: Normalizers.NormalizerMap)(implicit
      eqStore: EqStore
  ): Unit =
    if (!ValueEquivalence.defEq(actual, expected, normalizerMap) && !sortLeq(actual, expected))
      throw TypeMismatch(expected, actual)

  def checkType(value: Value, tyVal: Value, normalizerMap: Normalizers.NormalizerMap)(implicit eqStore: EqStore): Unit =
    checkFits(value.tpe, tyVal, normalizerMap)

  def getUniverse(value: Value)(implicit eqStore: EqStore): Universe = {
    value.tpe.caseOf {
      case u: Universe => u
      case _           => throw NotAType(value.tpe)
    }
  }

  def isPropValue(value: Value)(implicit eqStore: EqStore): Boolean = value.caseOf {
    case PropTpe => true
    case _       => false
  }

  def isPropValuedType(value: Value)(implicit eqStore: EqStore): Boolean =
    isPropValue(value) || getUniverse(value) == PropTpe

  private def checkApplyValue(fn: Value, args: Vector[BinderOps.CheckedArg], normalizerMap: Normalizers.NormalizerMap)(
      implicit eqStore: EqStore
  ): Value =
    fn.tpe.caseOf {
      case pi: VPi =>
        val values = args.map(_.value)
        BinderOps.checkAndInstantiate(pi.binders, pi.env, values, normalizerMap)
        Interpreter.evalApply(fn, values)
      case _ => throw CannotApplyNonFunction(fn)
    }

  private def residualizeBoundaryTerm(
      value: Value,
      checkedTerm: EA.Term,
      context: ValueQuote.QuoteContext,
      span: Span
  )(implicit eqStore: EqStore): EA.Term =
    checkedTerm match {
      case _: EA.Term.Body | _: EA.Term.Lam => checkedTerm
      case _ =>
        ValueOps.materialize(value, eqStore).caseOf {
          case _: Normalizer                                      => checkedTerm
          case VBlockedThunk(_: BlockedThunkBody.Match, _, _, _)  => checkedTerm
          case VApp(head, _, _) if head.name.startsWith("match#") => checkedTerm
          case _                                                  => ValueQuote.quoteTerm(value, context, span)
        }
    }

  private def residualizeChecked(checked: Checked, context: ValueQuote.QuoteContext, span: Span)(implicit
      eqStore: EqStore
  ): Checked =
    checked.copy(term = residualizeBoundaryTerm(checked.value, checked.term, context, span))

  private[raccoonlang] def residualizeTopLevelChecked(
      checked: Checked,
      context: ValueQuote.QuoteContext,
      span: Span
  )(implicit eqStore: EqStore): Checked =
    residualizeChecked(checked, context, span)

  private def checkPi(pi: CA.Term.Pi, env: TypecheckEnv)(implicit
      meta: EqStore
  ): CheckedPi = {
    val (vBinders, checkedBinders) = BinderOps.toVBinders(pi.binders, env)
    val binderEnv = BinderOps.freshen(vBinders, env)
    val checkedOut = getResidualizedType(pi.out, binderEnv)
    val freshArgs = vBinders.map(binder => binderEnv(binder.localRef))
    val classifier =
      if (isPropValuedType(checkedOut.value)) PropTpe
      else {
        getUniverse(checkedOut.value) match {
          case VSort(outLevel) =>
            val domLevels: Vector[Level] = freshArgs
              .map(v => getUniverse(v.tpe))
              .collect { case VSort(level) => level }

            VSort(Level.max(domLevels :+ outLevel))
        }
      }
    val checkedPi = EA.Term.Pi(checkedBinders, checkedOut.term, classifier, pi.span)
    CheckedPi(evalPi(checkedPi, env, vBinders), checkedPi)
  }

  def checkRef(ref: CA.Term.Ref, env: TypecheckEnv)(implicit
      meta: EqStore
  ): (Value, EA.Term.Ref) = {
    val checkedRef = ref match {
      case CA.Term.GlobalRef(name, span) => EA.Term.GlobalRef(name, span)
      case CA.Term.LocalRef(ref, span)   => EA.Term.LocalRef(ref, span)
    }
    (Interpreter.evalTypeTerm(checkedRef, env), checkedRef)
  }

  def checkTypeTerm(term: CA.TypeTerm, env: TypecheckEnv)(implicit
      meta: EqStore
  ): CheckedType = term match {
    case t: CA.Term.TApp =>
      val fn = checkTypeTerm(t.fn, env)
      val args = t.args.map { arg =>
        val checked = checkTypeTerm(arg, env)
        BinderOps.CheckedArg(checked.value, checked.term)
      }
      CheckedType(checkApplyValue(fn.value, args, env.normalizers), EA.Term.App(fn.term, args.map(_.term), t.span))
    case CA.Term.TSelect(base, field, span) =>
      val checkedBase = checkTypeTerm(base, env)
      val checkedSelect = checkSelect(checkedBase.value, checkedBase.term, field, span, env)
      CheckedType(checkedSelect.value, checkedSelect.term)
    case pi: CA.Term.Pi =>
      val checked = checkPi(pi, env)
      CheckedType(checked.value, checked.term)
    case ref: CA.Term.Ref => CheckedType.tupled(checkRef(ref, env))
  }

  def evalTypeTerm(term: CA.TypeTerm, env: TypecheckEnv)(implicit
      meta: EqStore
  ): Value = checkTypeTerm(term, env).value

  private def checkBody(body: CA.Term.Body, env: TypecheckEnv)(implicit
      meta: EqStore
  ): Checked = {
    val checkedLets = Vector.newBuilder[EA.Let]
    var curEnv = env

    body.lets.foreach { l =>
      val checkedValue = check(l.value, curEnv)
      val res = checkedValue.value
      var checkedTyTerm: Option[EA.TypeTerm] = None
      val withType = l.ty
        .map { tyTerm =>
          val checkedTy = getResidualizedType(tyTerm, curEnv)
          val tyV = checkedTy.value
          checkType(res, tyV, curEnv.normalizers)
          checkedTyTerm = Some(checkedTy.term)
          Value.ascribe(res, tyV)
        }
        .getOrElse(res)
      val residualValueTerm =
        residualizeBoundaryTerm(withType, checkedValue.term, ValueQuote.quoteContext(curEnv), l.value.span)(
          meta
        )
      checkedLets += EA.Let(l.localRef, checkedTyTerm, residualValueTerm, l.span, l.isInstance)
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.name, withType, meta)) else None
      curEnv = curEnv.putLocal(l.localRef, withType, instanceKey, Some(EA.Term.LocalRef(l.localRef, l.span)))
    }
    val checkedRes = check(body.res, curEnv)
    val residualRes =
      residualizeBoundaryTerm(checkedRes.value, checkedRes.term, ValueQuote.quoteContext(curEnv), body.res.span)(
        meta
      )
    Checked(checkedRes.value, EA.Term.Body(checkedLets.result(), residualRes, body.span))
  }

  private def checkBranch(br: CA.Case, args: Seq[Value], envWithScrut: TypecheckEnv, expectedTy: Value)(implicit
      eqStore: EqStore
  ): EA.Case = {
    if (args.length != br.argRefs.length)
      throw ArityMismatch(args.length, br.argRefs.length, Some(br.span))
    val branchEnv = br.argRefs.zip(args).foldLeft(envWithScrut) { case (curEnv, (argRef, argVal)) =>
      argRef match {
        case Some(ref) => curEnv.putLocal(ref, argVal)
        case None      => curEnv
      }
    }
    val branchRes = check(br.body, branchEnv)
    checkType(branchRes.value, expectedTy, branchEnv.normalizers)
    EA.Case(
      br.ctorName,
      br.argRefs,
      residualizeChecked(branchRes, ValueQuote.quoteContext(branchEnv), br.body.span).term,
      br.span
    )
  }

  private def inductiveFamilyOf(value: Value)(implicit eqStore: EqStore): Option[InductiveFamily] =
    value.caseOf {
      case VConst(n, Inductive(meta), _) => Some(InductiveFamily(n, meta))
      case VApp(VConst(n, Inductive(meta), _), args, _) if args.length == meta.familyArity =>
        Some(InductiveFamily(n, meta))
      case _ => None
    }

  private def checkSelect(baseValue: Value, baseTerm: EA.Term, field: String, span: Span, env: TypecheckEnv)(implicit
      eqStore: EqStore
  ): CheckedSelect = {
    val vType = Interpreter.resolveInEqStore(baseValue.tpe).value
    val InductiveFamily(indName, meta) = inductiveFamilyOf(vType).getOrElse(throw NotAType(vType))

    if (!meta.isStruct) throw NotAStruct(indName)

    env(meta.constructorNames.head) match {
      case head: ConstructorHead =>
        if (!head.isStruct) throw NotAStruct(indName)
        val shape = ConstructorOps.ConstructorShape.require(head)
        val fieldIdx = shape.fieldBinders.indexWhere(_.name == field)
        if (fieldIdx < 0) throw NotFound(field)

        // Freshen the full constructor telescope, including erased binders. The field type may depend on erased
        // constructor arguments and on earlier stored fields, so projection typing works over the full spine.
        val fresh = ConstructorOps.freshSpine(head)
        val refined =
          ValueEquivalence.unify(fresh.tpe, vType, eqStore.allow(fresh.synDeps), env.normalizers)
        val refinedFresh = fresh.materialize(refined)

        var projectionQuote = ValueQuote.quoteContext(env)(refined)
        shape.fieldBinders.take(fieldIdx).zipWithIndex.foreach { case (fieldBinder, idx) =>
          val priorFieldTyTerm = ValueQuote.quoteType(refinedFresh.fields(idx).tpe, projectionQuote, span)(refined)
          val priorFieldTerm = EA.Term.Select(baseTerm, fieldBinder.name, priorFieldTyTerm, span)
          projectionQuote = ValueQuote.withQuotedValue(projectionQuote, refinedFresh.fields(idx), priorFieldTerm)(
            refined
          )
        }

        val resultTyTerm =
          ValueQuote.quoteType(refinedFresh.fields(fieldIdx).tpe, projectionQuote, span)(refined)
        val resultTy = Interpreter.evalTypeTerm(resultTyTerm, env)
        val scrut = Interpreter.resolveInEqStore(baseValue).value
        checkPropElimination(
          indName,
          vType,
          resultTy,
          computeReachableCtors(scrut, vType, indName, meta.constructorNames, env),
          env.normalizers,
          span
        )

        val value = Interpreter.evalSelect(baseValue, field, env, span.nodeId, resultTy)
        CheckedSelect(value, EA.Term.Select(baseTerm, field, resultTyTerm, span))

      case _ => throw NotFound(meta.constructorNames.head)
    }
  }

  private final case class ReachableCtor(
      name: String,
      head: ConstructorHead,
      fieldArgs: Vector[Value],
      resultTy: Value,
      branchEqStore: EqStore
  )

  private def computeReachableCtors(
      scrut: Value,
      scrutTpe: Value,
      inductiveName: String,
      ctorNames: Vector[String],
      env: TypecheckEnv
  )(implicit eqStore: EqStore): Vector[ReachableCtor] = {
    def tryUnify(left: Value, right: Value, refinable: DepSet): Option[EqStore] =
      try Some(ValueEquivalence.unify(left, right, eqStore.allow(refinable), env.normalizers))
      catch { case _: UnificationFailed | _: OccursCheckFailed => None }

    def rootRefinable(value: Value): DepSet =
      value.caseOf {
        case blocker: Blocker => DepSet(blocker.blockerId)
        case _                => DepSet.empty
      }

    ctorNames.flatMap { ctorName =>
      env(ctorName) match {
        case h: ConstructorHead =>
          val fresh = ConstructorOps.freshSpine(h)
          val valueRefinable = rootRefinable(scrut) ++ fresh.synDeps
          val typeRefinable = scrutTpe.synDeps ++ fresh.synDeps

          val branchEqStore =
            tryUnify(scrut, fresh.value, valueRefinable)
              .orElse(tryUnify(fresh.tpe, scrutTpe, typeRefinable))

          branchEqStore.map { branchStore =>
            val refinedResultTy = ValueOps.materialize(scrutTpe, branchStore)
            ReachableCtor(ctorName, h, fresh.fields, refinedResultTy, branchStore)
          }

        case _ => throw UnknownConstructor(ctorName, inductiveName)
      }
    }
  }

  private def allowLargeElimination(
      scrutTpe: Value,
      reachable: Vector[ReachableCtor],
      normalizerMap: Normalizers.NormalizerMap
  )(implicit
      eqStore: EqStore
  ): Boolean = {
    if (reachable.isEmpty) return true
    if (reachable.length > 1) return false

    val only = reachable.head
    val copy1 = ConstructorOps.freshSpine(only.head)
    val copy2 = ConstructorOps.freshSpine(only.head)
    val (fields1, res1) = (copy1.fields, copy1.tpe)
    val (fields2, res2) = (copy2.fields, copy2.tpe)

    val refinable0 = DepSet.unionAll(scrutTpe.synDeps, res1.synDeps, res2.synDeps)

    val startEq =
      try {
        val eq1 = ValueEquivalence.unify(res1, scrutTpe, eqStore.allow(refinable0), normalizerMap)
        ValueEquivalence.unify(res2, scrutTpe, eq1, normalizerMap)
      } catch {
        case _: UnificationFailed | _: OccursCheckFailed => return false
      }

    fields1.zip(fields2).forall { case (f1, f2) =>
      TypeChecker.getUniverse(f1.tpe)(startEq) match {
        case PropTpe => true
        case _       => ValueEquivalence.defEq(f1, f2, normalizerMap)(startEq)
      }
    }
  }

  private def checkPropElimination(
      inductiveName: String,
      scrutTpe: Value,
      motiveTy: Value,
      reachable: => Vector[ReachableCtor],
      normalizerMap: Normalizers.NormalizerMap,
      span: Span
  )(implicit eqStore: EqStore): Unit =
    if (getUniverse(scrutTpe) == PropTpe && !isPropValuedType(motiveTy)) {
      if (!allowLargeElimination(scrutTpe, reachable, normalizerMap))
        throw PropEliminationRestricted(inductiveName, motiveTy, Some(span))
    }

  private def checkMatch(t: CA.Term.Match, env: TypecheckEnv)(implicit
      eqStore: EqStore
  ): Checked = {
    val scrutChecked = check(t.scrut, env)
    val scrut = Interpreter.resolveInEqStore(scrutChecked.value).value
    val scrutTpe = Interpreter.resolveInEqStore(scrut.tpe).value

    val InductiveFamily(inductiveName, inductiveMeta) =
      inductiveFamilyOf(scrutTpe).getOrElse(throw NonInductiveMatch(scrut.tpe))
    val inductiveCtorNames = inductiveMeta.constructorNames
    val cases = t.cases.map { c =>
      val candidates =
        if (c.isFullyQualified) inductiveMeta.constructors.collect {
          case ctor if ctor.canonicalName == c.ctorName => ctor.canonicalName
        }
        else
          inductiveMeta.constructors.collect {
            case ctor if ctor.shortName == c.ctorName => ctor.canonicalName
          }
      candidates match {
        case Vector(name) => c.copy(ctorName = name)
        case Vector()     => throw UnknownConstructor(c.ctorName, inductiveName, Some(c.span))
        case many         => throw AmbiguousName(c.ctorName, many, Some(c.span))
      }
    }

    cases.groupBy(_.ctorName).find(_._2.length > 1).foreach { case (ctor, duplicateCases) =>
      throw DuplicateCase(ctor, Some(duplicateCases(1).span))
    }

    lazy val reachableByType: Vector[ReachableCtor] =
      computeReachableCtors(scrut, scrutTpe, inductiveName, inductiveCtorNames, env)

    def inferMotiveFromReachable(reachable: Vector[ReachableCtor]): Value = {
      val first = reachable.headOption.getOrElse {
        throw MissingReturningClause("no constructors are reachable", Some(t.span))
      }
      val inferred = first.resultTy
      val allEqual = reachable.tail.forall { info =>
        ValueEquivalence.defEq(inferred, info.resultTy, env.normalizers)(eqStore)
      }
      if (!allEqual)
        throw MissingReturningClause("reachable constructors have different result types", Some(t.span))
      assertType(inferred)
      inferred
    }

    val checkedMotive = t.motive.map(motiveSyntax => getResidualizedType(motiveSyntax, env))
    val motiveTy = checkedMotive match {
      case Some(motive) => motive.value
      case None         => inferMotiveFromReachable(reachableByType)
    }

    checkPropElimination(inductiveName, scrutTpe, motiveTy, reachableByType, env.normalizers, t.span)

    var checkedByCtor = Map.empty[String, EA.Case]

    scrut match {
      case ctor @ VCtor(h, _, _) =>
        cases.find(_.ctorName != h.name).foreach { c =>
          throw UnreachableCase(c.ctorName, Some(c.span))
        }

        val br = cases.find(_.ctorName == h.name).getOrElse(throw MissingCase(h.name))
        checkedByCtor += h.name -> checkBranch(br, ctor.fields, env, motiveTy)

      case _ =>
        val reachableMap = reachableByType.map(info => info.name -> info).toMap

        inductiveCtorNames.foreach { ctorName =>
          reachableMap.get(ctorName) match {
            case None =>
              cases.find(_.ctorName == ctorName).foreach { c =>
                throw UnreachableCase(ctorName, Some(c.span))
              }

            case Some(info) =>
              val br = cases.find(_.ctorName == ctorName).getOrElse(throw MissingCase(ctorName))
              checkedByCtor += ctorName -> checkBranch(br, info.fieldArgs, env, motiveTy)(info.branchEqStore)
          }
        }
    }

    val checkedCases = cases.map { c =>
      checkedByCtor.getOrElse(c.ctorName, throw WTF(s"Unchecked reachable case ${c.ctorName}"))
    }
    val residualScrut = residualizeChecked(scrutChecked, ValueQuote.quoteContext(env), t.scrut.span).term
    val checkedMatch = EA.Term.Match(residualScrut, checkedMotive.map(_.term), checkedCases, t.span)
    Checked(Interpreter.evalTerm(checkedMatch, env), checkedMatch)
  }

  private def checkLam(l: CA.Term.Lam, env: TypecheckEnv)(implicit
      eqStore: EqStore
  ): Checked = {
    val envWithNormalizers = l.uses.foldLeft(env) { case (curEnv, nextUse) =>
      val normalizer = check(nextUse.normalizer, curEnv)(eqStore)
      normalizer.value match {
        case n: Value.Normalizer => curEnv.useNormalizer(n)
        case _ =>
          throw TypeMismatch(normalizer.value, NormalizerType)
      }
    }

    val checkedPi = checkPi(l.ty, envWithNormalizers)
    val vpi = checkedPi.value
    val bodyEnv = BinderOps.freshen(vpi.binders, envWithNormalizers)

    val recurEnv =
      l.name match {
        case Some(name) => bodyEnv.putGlobal(name, Value.VConst(name, Symbol, vpi))
        case None       => bodyEnv
      }

    val checkedBody = check(l.body, recurEnv)(eqStore)
    val resType = Interpreter.evalTypeTerm(checkedPi.term.out, bodyEnv)

    checkType(checkedBody.value, resType, recurEnv.normalizers)
    val residualBody = residualizeChecked(checkedBody, ValueQuote.quoteContext(recurEnv), l.body.span).term
    val checkedLam =
      EA.Term.Lam(checkedPi.term, Vector.empty, residualBody, l.span, l.name, l.isStable)
    Checked(Interpreter.evalLam(checkedLam, vpi, env), checkedLam)
  }

  def getResidualizedType(term: CA.TypeTerm, env: TypecheckEnv)(implicit
      ctx: EqStore
  ): CheckedType = {
    val res = checkTypeTerm(term, env)
    assertType(res.value)
    val residualTerm =
      res.term match {
        case _: EA.Term.Pi       => res.term
        case _: EA.Term.LocalRef => res.term
        case _                   => ValueQuote.quoteType(res.value, ValueQuote.quoteContext(env), term.span)
      }
    res.copy(term = residualTerm)
  }

  def getType(term: CA.TypeTerm, env: TypecheckEnv)(implicit ctx: EqStore): Value = {
    val res = checkTypeTerm(term, env)
    assertType(res.value)
    res.value
  }

  def assertType(value: Value)(implicit ctx: EqStore): Unit = {
    value.caseOf {
      case PropTpe =>
      case _ =>
        value.tpe.caseOf {
          case _: VSort | PropTpe =>
          case _                  => throw NotAType(value)
        }
    }
  }

  def check(term: CA.Term, env: TypecheckEnv)(implicit
      eqStore: EqStore
  ): Checked = {
    try {
      term match {
        case CA.Term.Select(base, field, span) =>
          val checkedBase = check(base, env)
          val checkedSelect = checkSelect(checkedBase.value, checkedBase.term, field, span, env)
          Checked(checkedSelect.value, checkedSelect.term)
        case app: CA.Term.App =>
          val fn = check(app.fn, env)
          val args = app.args.map { arg =>
            val checkedArg = check(arg, env)
            BinderOps.CheckedArg(checkedArg.value, checkedArg.term)
          }
          Checked(checkApplyValue(fn.value, args, env.normalizers), EA.Term.App(fn.term, args.map(_.term), app.span))

        case derive: CA.Term.Derive =>
          val goal = getType(derive.goal, env)
          val solved = InstanceSearch.solve(goal, env)
          residualizeChecked(Checked(solved.value, solved.term), ValueQuote.quoteContext(env), derive.span)

        case l: CA.Term.Lam   => checkLam(l, env)
        case m: CA.Term.Match => checkMatch(m, env)
        case b: CA.Term.Body  => checkBody(b, env)
        case term: CA.TypeTerm =>
          val checked = checkTypeTerm(term, env)
          Checked(checked.value, checked.term)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

}
