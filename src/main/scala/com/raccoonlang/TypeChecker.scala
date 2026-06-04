package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang.ValueQuote.{quoteContext, quoteTerm, quoteType}
import com.raccoonlang.telescope.{BinderOps, ConstructorOps}
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

object TypeChecker {
  private final case class CheckedPi(vpi: VPi, bodyEnv: Env, outTy: Value)
  private final case class InductiveFamily(name: String, meta: InductiveMeta)

  def sortLeq(a: Value, b: Value): Boolean = {
    (a, b) match {
      case (Value.VSort(u), Value.VSort(v)) => Level.leq(u, v)
      case (l1: Level, l2: Level)           => Level.leq(l1, l2)
      case (l1: Level, v: Var)              => Level.leq(l1, Level.mk(v.id))
      case (v: Var, l2: Level)              => Level.leq(Level.mk(v.id), l2)
      case _                                => false
    }
  }

  def checkFits(actual: Value, expected: Value, normalizerMap: Normalizers.NormalizerMap): Unit =
    if (!ValueEquivalence.defEq(actual, expected, normalizerMap, propIrrelevant = true) && !sortLeq(actual, expected))
      throw TypeMismatch(expected, actual)

  def checkType(value: Value, tyVal: Value, normalizerMap: Normalizers.NormalizerMap): Unit =
    checkFits(value.tpe, tyVal, normalizerMap)

  def getUniverse(value: Value): Universe = {
    value.tpe match {
      case u: Universe => u
      case _           => throw NotAType(value.tpe)
    }
  }

  def isPropValue(value: Value): Boolean = value match {
    case PropTpe => true
    case _       => false
  }

  def isPropValuedType(value: Value): Boolean =
    isPropValue(value) || getUniverse(value) == PropTpe

  private def checkApplyValue(fn: Value, args: Vector[Value], normalizerMap: Normalizers.NormalizerMap): Value =
    fn.tpe match {
      case pi: VPi =>
        BinderOps.checkAndInstantiate(pi.binders, pi.env, args, normalizerMap)
        Interpreter.evalApply(fn, args)
      case _ =>
        throw CannotApplyNonFunction(fn)
    }

  private def checkPi(pi: CA.Term.Pi, env: Env): CheckedPi = {
    val (vBinders, checkedBinders) = BinderOps.toVBinders(pi.binders, env)
    val binderEnv = BinderOps.freshen(vBinders, env)
    val outV = checkTypeTerm(pi.out, binderEnv)
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
      EA.Term.Pi(checkedBinders, quoteType(outV, quoteContext(binderEnv), pi.out.span), classifier, pi.span)
    CheckedPi(evalPi(checkedPi, env, vBinders), binderEnv, outV)
  }

  def checkRef(ref: CA.Term.Ref, env: Env): Value = {
    val checkedRef = ref match {
      case CA.Term.GlobalRef(name, span) => EA.Term.GlobalRef(name, span)
      case CA.Term.LocalRef(ref, span)   => EA.Term.LocalRef(ref, span)
    }
    Interpreter.evalTypeTerm(checkedRef, env)
  }

  def checkTypeTerm(term: CA.TypeTerm, env: Env): Value =
    term match {
      case t: CA.Term.TApp =>
        val fn = checkTypeTerm(t.fn, env)
        val args = t.args.map(arg => checkTypeTerm(arg, env))
        checkApplyValue(fn, args, env.normalizers)
      case CA.Term.TSelect(base, field, span) =>
        val checkedBase = checkTypeTerm(base, env)
        checkSelect(checkedBase, field, span, env)
      case derive: CA.Term.Derive =>
        val goal = getType(derive.goal, env)
        InstanceSearch.solve(goal, env)
      case pi: CA.Term.Pi   => checkPi(pi, env).vpi
      case ref: CA.Term.Ref => checkRef(ref, env)
    }

  def evalTypeTerm(term: CA.TypeTerm, env: Env): Value = checkTypeTerm(term, env)

  // Returning (Value, EA.Term) allows us to maintain the 'let' structure while quoting the Body.
  // TODO: The returned term is used in top-level functions, but not in sub-expressions
  private def checkBody(body: CA.Term.Body, env: Env): (Value, EA.Term) = {
    val checkedLets = Vector.newBuilder[EA.Let]
    var curEnv = env

    body.lets.foreach { l =>
      val res = check(l.value, curEnv)
      val quoteCtx = ValueQuote.quoteContext(curEnv)

      var resTyTerm: Option[EA.TypeTerm] = None
      val withType = l.ty
        .map { tyTerm =>
          val tyV = getType(tyTerm, curEnv)
          checkType(res, tyV, curEnv.normalizers)
          resTyTerm = Some(ValueQuote.quoteType(tyV, quoteCtx, tyTerm.span))
          Value.ascribe(res, tyV)
        }
        .getOrElse(res)

      val quotedRes = quoteTerm(withType, quoteCtx, l.value.span)
      checkedLets += EA.Let(l.localRef, resTyTerm, quotedRes, l.span, l.isInstance)
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.name, withType)) else None
      curEnv = curEnv.putLocal(l.localRef, withType, instanceKey)
    }

    val checkedRes = check(body.res, curEnv)
    val residualRes = quoteTerm(checkedRes, ValueQuote.quoteContext(curEnv), body.res.span)
    (checkedRes, EA.Term.Body(checkedLets.result(), residualRes, body.span))
  }

  private def checkBranch(br: CA.Case, args: Seq[Value], envWithScrut: Env, expectedTy: Value): EA.Case = {
    if (args.length != br.argRefs.length)
      throw ArityMismatch(args.length, br.argRefs.length, Some(br.span))
    val branchEnv = br.argRefs.zip(args).foldLeft(envWithScrut) { case (curEnv, (argRef, argVal)) =>
      argRef match {
        case Some(ref) => curEnv.putLocal(ref, argVal)
        case None      => curEnv
      }
    }
    val branchRes = check(br.body, branchEnv)
    checkType(branchRes, expectedTy, branchEnv.normalizers)
    EA.Case(
      br.ctorName,
      br.argRefs,
      quoteTerm(branchRes, ValueQuote.quoteContext(branchEnv), br.body.span),
      br.span
    )
  }

  private def inductiveFamilyOf(value: Value): Option[InductiveFamily] =
    value match {
      case VConst(n, Inductive(meta), _) => Some(InductiveFamily(n, meta))
      case VApp(VConst(n, Inductive(meta), _), args, _) if args.length == meta.familyArity =>
        Some(InductiveFamily(n, meta))
      case _ => None
    }

  private def checkSelect(baseValue: Value, field: String, span: Span, env: Env): Value = {
    val vType = baseValue.tpe
    val InductiveFamily(indName, meta) = inductiveFamilyOf(vType).getOrElse(throw NotAType(vType))

    if (!meta.isStruct) throw NotAStruct(indName)

    val selectorName = s"$indName.$field"
    val selector = env(selectorName)
    checkApplyValue(selector, Vector(baseValue), env.normalizers)
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
      env: Env
  ): Vector[ReachableCtor] = {
    def tryUnify(left: Value, right: Value, refinable: DepSet): Option[EqStore] =
      try Some(ValueEquivalence.unify(left, right, EqStore.empty.allow(refinable), env.normalizers))
      catch { case _: UnificationFailed | _: OccursCheckFailed => None }

    def rootRefinable(value: Value): DepSet =
      value match {
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
        val eq1 = ValueEquivalence.unify(res1, scrutTpe, EqStore.empty.allow(refinable0), normalizerMap)
        ValueEquivalence.unify(res2, scrutTpe, eq1, normalizerMap)
      } catch {
        case _: UnificationFailed | _: OccursCheckFailed => return false
      }

    fields1.zip(fields2).forall { case (f1, f2) =>
      val mf1 = ValueOps.materialize(f1, startEq)
      val mf2 = ValueOps.materialize(f2, startEq)
      TypeChecker.getUniverse(mf1.tpe) match {
        case PropTpe => true
        case _       => ValueEquivalence.defEq(mf1, mf2, normalizerMap, propIrrelevant = true)
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
  ): Unit =
    if (getUniverse(scrutTpe) == PropTpe && !isPropValuedType(motiveTy)) {
      if (!allowLargeElimination(scrutTpe, reachable, normalizerMap))
        throw PropEliminationRestricted(inductiveName, motiveTy, Some(span))
    }

  private def checkMatch(t: CA.Term.Match, env: Env): Value = {
    val scrutChecked = check(t.scrut, env)
    val scrut = scrutChecked
    val scrutTpe = scrut.tpe

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
        ValueEquivalence.defEq(inferred, info.resultTy, env.normalizers, propIrrelevant = true)
      }
      if (!allEqual)
        throw MissingReturningClause("reachable constructors have different result types", Some(t.span))
      assertType(inferred)
      inferred
    }

    val checkedMotive = t.motive.map(motiveSyntax => check(motiveSyntax, env))
    val motiveTy = checkedMotive match {
      case Some(motive) => motive
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
              val branchStore = info.branchEqStore
              val branchEnv = ValueOps.materializeEnv(env, branchStore)
              val branchArgs = info.fieldArgs.map(arg => ValueOps.materialize(arg, branchStore))
              val branchMotiveTy = ValueOps.materialize(motiveTy, branchStore)
              checkedByCtor += ctorName -> checkBranch(br, branchArgs, branchEnv, branchMotiveTy)
          }
        }
    }

    val checkedCases = cases.map { c =>
      checkedByCtor.getOrElse(c.ctorName, throw WTF(s"Unchecked reachable case ${c.ctorName}"))
    }
    val quoteCtx = ValueQuote.quoteContext(env)
    val residualScrut = quoteTerm(scrutChecked, quoteCtx, t.scrut.span)
    val checkedMatch = EA.Term.Match(
      residualScrut,
      checkedMotive.map(v => quoteType(v, quoteCtx, t.motive.get.span)),
      checkedCases,
      t.span
    )
    Interpreter.evalTerm(checkedMatch, env)
  }

  private def checkLam(l: CA.Term.Lam, env: Env): VLam = {
    val envWithNormalizers = l.uses.foldLeft(env) { case (curEnv, nextUse) =>
      val normalizer = check(nextUse.normalizer, curEnv)
      normalizer match {
        case n: Value.Normalizer => curEnv.useNormalizer(n)
        case _ =>
          throw TypeMismatch(normalizer, NormalizerType)
      }
    }

    val checkedVpi = checkPi(l.ty, envWithNormalizers)
    val vpi = checkedVpi.vpi
    val bodyEnv = checkedVpi.bodyEnv

    // Recursive self references stay local for the whole pipeline, even if the source used a qualified name.
    // While checking, the local contains a raw recursive value that enforces the decrease and can only quote as
    // an application head, so the body cannot store it as an ordinary value. The checked lambda keeps the same
    // self ref; when the lambda runs, Interpreter.runLam patches that slot with the final VLam. The declaration
    // is published to globals separately after the body has checked.
    val recurEnv =
      l.recursion match {
        case Some(CA.Recursion(ref, decreaseSpec)) =>
          val name = l.name.getOrElse(throw WTF("Recursive lambda must have a name", Some(l.span)))
          val recursiveSelf = TerminationChecker.rawRecursiveSelf(name, vpi, decreaseSpec, bodyEnv, l.isStable)
          bodyEnv.putLocal(ref, recursiveSelf, quotePolicy = LocalQuotePolicy.AppHeadOnly(name))
        case None => bodyEnv
      }

    val quoteCtx = quoteContext(recurEnv)
    val (checkedBody, bodyTerm) = l.body match {
      case b: CoreAst.Term.Body => checkBody(b, recurEnv)
      case _ =>
        val bodyV = check(l.body, recurEnv)
        (bodyV, quoteTerm(bodyV, quoteCtx, l.body.span))
    }

    checkType(checkedBody, checkedVpi.outTy, recurEnv.normalizers)
    val quotedPi = quoteTerm(vpi, quoteCtx, l.ty.span) match {
      case pi: ElabAst.Term.Pi => pi
      case other               => throw WTF(s"Failed to quote $vpi, got $other ")
    }
    val checkedLam =
      EA.Term.Lam(quotedPi, Vector.empty, bodyTerm, l.span, l.name, l.isStable, l.recursion.map(_.selfRef))
    Interpreter.evalLam(checkedLam, vpi, env)
  }

  def getType(term: CA.TypeTerm, env: Env): Value = {
    val res = checkTypeTerm(term, env)
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

  def check(term: CA.Term, env: Env): Value = {
    try {
      term match {
        case CA.Term.Select(base, field, span) =>
          val checkedBase = check(base, env)
          checkSelect(checkedBase, field, span, env)
        case app: CA.Term.App =>
          val fn = check(app.fn, env)
          val args = app.args.map { arg => check(arg, env) }
          checkApplyValue(fn, args, env.normalizers)
        case derive: CA.Term.Derive =>
          val goal = getType(derive.goal, env)
          InstanceSearch.solve(goal, env)

        case l: CA.Term.Lam    => checkLam(l, env)
        case m: CA.Term.Match  => checkMatch(m, env)
        case b: CA.Term.Body   => checkBody(b, env)._1
        case term: CA.TypeTerm => checkTypeTerm(term, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

}
