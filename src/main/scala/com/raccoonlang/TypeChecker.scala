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

  private def computePiClassifier(vars: Vector[Value], outType: Value)(implicit eqStore: EqStore): Universe =
    if (isPropValuedType(outType)) PropTpe
    else {
      TypeChecker.getUniverse(outType) match {
        case VSort(outLevel) =>
          val domLevels: Vector[Level] = vars
            .map(v => TypeChecker.getUniverse(v.tpe))
            .collect { case VSort(level) => level }

          VSort(Level.max(domLevels :+ outLevel))
      }
    }

  private def checkApp(app: CA.Term.App, env: TypecheckEnv)(implicit
      meta: EqStore
  ): Checked = {
    val fn = check(app.fn, env)
    val args = app.args.map { arg =>
      val checkedArg = check(arg, env)
      BinderOps.CheckedArg(checkedArg.value, checkedArg.term)
    }
    Checked(checkApplyValue(fn.value, args, env.normalizers), EA.Term.App(fn.term, args.map(_.term), app.span))
  }

  private def checkDerive(derive: CA.Term.Derive, env: TypecheckEnv)(implicit
      meta: EqStore
  ): Checked = {
    val goal = getCheckedType(derive.goal, env)
    val solved = InstanceSearch.solve(goal.value, env)
    Checked(solved.value, solved.term)
  }

  private def checkPi(pi: CA.Term.Pi, env: TypecheckEnv)(implicit
      meta: EqStore
  ): CheckedPi = {
    val (vBinders, checkedBinders) = BinderOps.toVBinders(pi.binders, env)
    val binderEnv = BinderOps.freshen(vBinders, env)
    val checkedOut = getCheckedType(pi.out, binderEnv)
    val freshArgs = vBinders.map(binder => binderEnv(binder.localRef))
    val classifier = computePiClassifier(freshArgs, checkedOut.value)
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
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val checkedValue = check(l.value, curEnv)
      val res = checkedValue.value
      val withType = l.ty
        .map { tyTerm =>
          val checkedTy = getCheckedType(tyTerm, curEnv)
          val tyV = checkedTy.value
          checkType(res, tyV, curEnv.normalizers)
          checkedLets += EA.Let(l.localRef, Some(checkedTy.term), checkedValue.term, l.span, l.isInstance)
          Value.ascribe(res, tyV)
        }
        .getOrElse {
          checkedLets += EA.Let(l.localRef, None, checkedValue.term, l.span, l.isInstance)
          res
        }
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.name, withType, meta)) else None
      curEnv.putLocal(l.localRef, withType, instanceKey, Some(EA.Term.LocalRef(l.localRef, l.span)))
    }
    val checkedRes = check(body.res, newEnv)
    Checked(checkedRes.value, EA.Term.Body(checkedLets.result(), checkedRes.term, body.span))
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
    EA.Case(br.ctorName, br.argRefs, branchRes.term, br.span)
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

        // Freshen the full constructor telescope, including erased binders. Erased binders are not stored in
        // runtime VCtors, but they still participate in the constructor result type and may be needed while
        // computing the projected field type.
        val fresh = ConstructorOps.freshSpine(head)
        val refined =
          ValueEquivalence.unify(fresh.tpe, vType, eqStore.allow(fresh.synDeps), env.normalizers)
        val refinedFresh = fresh.materialize(refined)

        var quoteContext = ValueQuote.Context.empty
        shape.fieldBinders.take(fieldIdx).zipWithIndex.foreach { case (fieldBinder, idx) =>
          // Constructor field binder refs are scoped to the constructor telescope, not to this projection site.
          // For a later field type like Vec(A, n), the in-scope syntax for the fresh constructor field `n`
          // is the earlier projection `base.n`, so teach the quoter that substitution before quoting later types.
          val priorFieldTy = refinedFresh.fields(idx).tpe
          val priorFieldTyTerm = ValueQuote.quoteType(priorFieldTy, env, span, quoteContext)(refined)
          val priorFieldTerm = EA.Term.Select(baseTerm, fieldBinder.name, priorFieldTyTerm, span)
          quoteContext = quoteContext.withValue(refinedFresh.fields(idx), priorFieldTerm)(refined)
        }

        val resultTyTerm =
          ValueQuote.quoteType(refinedFresh.fields(fieldIdx).tpe, env, span, quoteContext)(refined)
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

    val checkedMotive = t.motive.map(motiveSyntax => getCheckedType(motiveSyntax, env))
    val motiveTy = checkedMotive match {
      case Some(motive) => motive.value
      case None         => inferMotiveFromReachable(reachableByType)
    }

    checkPropElimination(inductiveName, scrutTpe, motiveTy, reachableByType, env.normalizers, t.span)

    var checkedByCtor = Map.empty[String, EA.Case]

    scrut match {
      case VCtor(h, fields, _) =>
        cases.find(_.ctorName != h.name).foreach { c =>
          throw UnreachableCase(c.ctorName, Some(c.span))
        }

        val br = cases.find(_.ctorName == h.name).getOrElse(throw MissingCase(h.name))
        checkedByCtor += h.name -> checkBranch(br, fields, env, motiveTy)

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
    val checkedMatch = EA.Term.Match(scrutChecked.term, checkedMotive.map(_.term), checkedCases, t.span)
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
    val checkedLam =
      EA.Term.Lam(checkedPi.term, Vector.empty, checkedBody.term, l.span, l.name, l.isStable)
    Checked(Interpreter.evalLam(checkedLam, vpi, env), checkedLam)
  }

  def getCheckedType(term: CA.TypeTerm, env: TypecheckEnv)(implicit
      ctx: EqStore
  ): CheckedType = {
    val res = checkTypeTerm(term, env)
    assertType(res.value)
    res
  }

  def getType(term: CA.TypeTerm, env: TypecheckEnv)(implicit ctx: EqStore): Value =
    getCheckedType(term, env).value

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
        case t: CA.Term.App    => checkApp(t, env)
        case d: CA.Term.Derive => checkDerive(d, env)
        case l: CA.Term.Lam    => checkLam(l, env)
        case m: CA.Term.Match  => checkMatch(m, env)
        case b: CA.Term.Body   => checkBody(b, env)
        case term: CA.TypeTerm =>
          val checked = checkTypeTerm(term, env)
          Checked(checked.value, checked.term)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

}
