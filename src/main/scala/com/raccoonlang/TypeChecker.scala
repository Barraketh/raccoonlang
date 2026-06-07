package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang.ValueQuote.{quoteContext, quoteTerm, quoteType}
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

object TypeChecker {
  private final case class CheckedPi(vpi: VPi, bodyEnv: Env, outTy: Value, residual: EA.Term.Pi)
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

  def checkFits(actual: Value, expected: Value, normalizerMap: Normalizers.NormalizerMap): Unit =
    if (!ValueEquivalence.defEq(actual, expected, normalizerMap, propIrrelevant = true) && !sortLeq(actual, expected))
      throw TypeMismatch(expected, actual)

  def checkType(value: Value, tyVal: Value, normalizerMap: Normalizers.NormalizerMap): Unit =
    checkFits(value.tpe, tyVal, normalizerMap)

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

  private def checkApplyValue(fn: Value, args: Vector[Value], normalizerMap: Normalizers.NormalizerMap): Value =
    fn.tpe match {
      case pi: VPi =>
        BinderOps.checkAndInstantiate(pi.binders, pi.env, args, normalizerMap)
        Interpreter.evalApply(fn, args)
      case _ => throw CannotApplyNonFunction(fn)
    }

  private def elabRef(ref: CA.Term.Ref): EA.Term.Ref =
    ref match {
      case CA.Term.GlobalRef(name, span) => EA.Term.GlobalRef(name, span)
      case CA.Term.LocalRef(ref, span)   => EA.Term.LocalRef(ref, span)
    }

  private def rejectStoredAppHeadOnlyRefs(term: EA.Term, env: Env): Unit = {
    def loop(t: EA.Term, appHead: Boolean): Unit =
      t match {
        case EA.Term.LocalRef(ref, span) =>
          if (ref.id >= 0 && ref.id < env.locals.length) {
            val binding = env.localBinding(ref)
            binding.residualPolicy match {
              case LocalResidualPolicy.AppHeadOnly(name) if !appHead =>
                throw CannotQuoteValue(binding.value, s"$name is only available as an application head", Some(span))
              case _ =>
            }
          }
        case EA.Term.GlobalRef(_, _) =>
        case EA.Term.App(fn, args, _) =>
          loop(fn, appHead = true)
          args.foreach(arg => loop(arg, appHead = false))
        case EA.Term.Pi(binders, out, _, _) =>
          binders.foreach(b => loopBinderType(b.ty))
          loop(out, appHead = false)
        case EA.Term.Body(lets, res, _) =>
          lets.foreach { l =>
            l.ty.foreach(loop(_, appHead = false))
            loop(l.value, appHead = false)
          }
          loop(res, appHead = false)
        case EA.Term.Lam(_, _, _, _, _, _) =>
        case EA.Term.Match(scrut, motive, cases, _) =>
          loop(scrut, appHead = false)
          motive.foreach(loop(_, appHead = false))
          cases.foreach(c => loop(c.body, appHead = false))
      }

    def loopBinderType(t: EA.BinderType): Unit =
      t match {
        case EA.BinderType.TypePattern(tp, _)                   => loopTypePattern(tp)
        case EA.BinderType.ConstrainedCapture(_, constraint, _) => loopTypePattern(constraint)
      }

    def loopTypePattern(t: EA.TypePattern): Unit =
      t match {
        case EA.TypePattern.Type(term) => loop(term, appHead = false)
        case EA.TypePattern.App(fn, args, _) =>
          loop(fn, appHead = true)
          args.foreach(loopTypePattern)
        case EA.TypePattern.Capture(_, _) =>
      }

    loop(term, appHead = false)
  }

  private def checkPi(pi: CA.Term.Pi, env: Env): CheckedPi = {
    val (vBinders, checkedBinders) = BinderOps.toVBinders(pi.binders, env)
    val binderEnv = BinderOps.freshen(vBinders, env)
    val checkedOut = checkTypeTerm(pi.out, binderEnv)
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
      EA.Term.Pi(checkedBinders, checkedOut.residual, classifier, pi.span)
    CheckedPi(evalPi(checkedPi, env, vBinders), binderEnv, outV, checkedPi)
  }

  private[raccoonlang] def checkTypeTerm(term: CA.TypeTerm, env: Env): CheckedTypeTerm =
    term match {
      case t: CA.Term.TApp =>
        val fn = checkTypeTerm(t.fn, env)
        val args = t.args.map(arg => checkTypeTerm(arg, env))
        val value = checkApplyValue(fn.value, args.map(_.value), env.normalizers)
        val residual = EA.Term.App(fn.residual, args.map(_.residual), t.span)
        CheckedTypeTerm(value, residual)
      case CA.Term.TSelect(base, field, span) =>
        val checkedBase = checkTypeTerm(base, env)
        val (selectorName, value) = checkSelect(checkedBase.value, field, span, env)
        CheckedTypeTerm(value, EA.Term.App(EA.Term.GlobalRef(selectorName, span), Vector(checkedBase.residual), span))
      case derive: CA.Term.Derive =>
        val goal = getType(derive.goal, env)
        val value = InstanceSearch.solve(goal, env)
        CheckedTypeTerm(value, quoteType(value, quoteContext(env), derive.span))
      case pi: CA.Term.Pi =>
        val checked = checkPi(pi, env)
        CheckedTypeTerm(checked.vpi, checked.residual)
      case ref: CA.Term.Ref =>
        val residual = elabRef(ref)
        CheckedTypeTerm(Interpreter.evalTypeTerm(residual, env), residual)
    }

  // Returning the residual term lets callers preserve checked let/lambda structure instead of re-checking.
  private def checkBody(body: CA.Term.Body, env: Env): CheckedTerm = {
    val checkedLets = Vector.newBuilder[EA.Let]
    var curEnv = env

    body.lets.foreach { l =>
      val checkedValue = checkTerm(l.value, curEnv)
      rejectStoredAppHeadOnlyRefs(checkedValue.residual, curEnv)

      var resTyTerm: Option[EA.TypeTerm] = None
      val withType = l.ty
        .map { tyTerm =>
          val checkedTy = checkTypeTerm(tyTerm, curEnv)
          val tyV = checkedTy.value
          checkType(checkedValue.value, tyV, curEnv.normalizers)
          resTyTerm = Some(checkedTy.residual)
          Value.ascribe(checkedValue.value, tyV)
        }
        .getOrElse(checkedValue.value)

      checkedLets += EA.Let(l.localRef, resTyTerm, checkedValue.residual, l.span, l.isInstance)
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.name, withType)) else None
      curEnv = curEnv.putLocal(l.localRef, withType, instanceKey)
    }

    val checkedRes = checkTerm(body.res, curEnv)
    CheckedTerm(checkedRes.value, EA.Term.Body(checkedLets.result(), checkedRes.residual, body.span))
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
    val branchRes = checkTerm(br.body, branchEnv)
    checkType(branchRes.value, expectedTy, branchEnv.normalizers)
    EA.Case(
      br.ctorName,
      br.argRefs,
      branchRes.residual,
      br.span
    )
  }

  private def inductiveFamilyOf(value: Value): Option[InductiveFamilyInstance] =
    value match {
      case InductiveFamilyValue(instance) => Some(instance)
      case _                              => None
    }

  private def checkSelect(baseValue: Value, field: String, span: Span, env: Env): (String, Value) = {
    val vType = baseValue.tpe
    val family = inductiveFamilyOf(vType).getOrElse(throw NotAType(vType))
    val indName = family.head.name
    val meta = family.meta

    if (!meta.isStruct) throw NotAStruct(indName)

    val selectorName = s"$indName.$field"
    val selector = env(selectorName)
    (selectorName, checkApplyValue(selector, Vector(baseValue), env.normalizers))
  }

  private final case class ReachableCtor(
      name: String,
      head: ConstructorHead,
      fieldArgs: Vector[Value],
      resultTy: Value,
      branchEqStore: EqStore
  )

  private def freshCtorArgsAndResult(head: ConstructorHead): (Vector[Value], Value) =
    head.tpe match {
      case pi: VPi =>
        val fresh = BinderOps.freshen(pi)
        val args = pi.binders.map(binder => fresh(binder.localRef))
        (args, pi.codomain(fresh))

      case _ => (Vector.empty, head.tpe)
    }

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
        case Blocker(blockerId) => DepSet(blockerId)
        case _                  => DepSet.empty
      }

    ctorNames.flatMap { ctorName =>
      env(ctorName) match {
        case h: ConstructorHead =>
          val (freshArgs, resultTy) = freshCtorArgsAndResult(h)
          val fieldArgs = freshArgs.drop(h.numErased)
          val ctorValue = VCtor(h, fieldArgs, resultTy)
          val valueRefinable = rootRefinable(scrut) ++ ctorValue.synDeps
          val typeRefinable = scrutTpe.synDeps ++ ctorValue.synDeps

          val branchEqStore =
            tryUnify(scrut, ctorValue, valueRefinable)
              .orElse(tryUnify(resultTy, scrutTpe, typeRefinable))

          branchEqStore.map { branchStore =>
            val refinedResultTy = ValueOps.materialize(scrutTpe, branchStore)
            ReachableCtor(ctorName, h, fieldArgs, refinedResultTy, branchStore)
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
    val (args1, res1) = freshCtorArgsAndResult(only.head)
    val (args2, res2) = freshCtorArgsAndResult(only.head)
    val fields1 = args1.drop(only.head.numErased)
    val fields2 = args2.drop(only.head.numErased)

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

  private def checkMatch(t: CA.Term.Match, env: Env): CheckedTerm = {
    val scrutChecked = checkTerm(t.scrut, env)
    val scrut = scrutChecked.value
    val scrutTpe = scrut.tpe

    val inductiveFamily = inductiveFamilyOf(scrutTpe).getOrElse(throw NonInductiveMatch(scrut.tpe))
    val inductiveName = inductiveFamily.head.name
    val inductiveMeta = inductiveFamily.meta
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

    val checkedMotive = t.motive.map(motiveSyntax => checkTypeTerm(motiveSyntax, env))
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
    val checkedMatch = EA.Term.Match(
      scrutChecked.residual,
      checkedMotive.map(_.residual),
      checkedCases,
      t.span
    )
    CheckedTerm(Interpreter.evalTerm(checkedMatch, env), checkedMatch)
  }

  private def checkLam(l: CA.Term.Lam, env: Env): CheckedTerm = {
    val envWithNormalizers = l.uses.foldLeft(env) { case (curEnv, nextUse) =>
      val normalizer = checkTerm(nextUse.normalizer, curEnv).value
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
    // While checking, the local contains a raw recursive value that enforces the decrease and can only appear as an
    // application head, so the body cannot store it as an ordinary value. The checked lambda keeps the same self ref;
    // when the lambda runs, Interpreter.runLam patches that slot with the final VLam. The declaration is published to
    // globals separately after the body has checked.
    val recurEnv =
      l.recursion match {
        case Some(CA.Recursion(ref, decreaseSpec)) =>
          val name = l.name.getOrElse(throw WTF("Recursive lambda must have a name", Some(l.span)))
          val recursiveSelf = TerminationChecker.rawRecursiveSelf(name, vpi, decreaseSpec, bodyEnv, l.isStable)
          bodyEnv.putLocal(ref, recursiveSelf, residualPolicy = LocalResidualPolicy.AppHeadOnly(name))
        case None => bodyEnv
      }

    val checkedBody = l.body match {
      case b: CA.Term.Body => checkBody(b, recurEnv)
      case _               => checkTerm(l.body, recurEnv)
    }

    checkType(checkedBody.value, checkedVpi.outTy, recurEnv.normalizers)
    rejectStoredAppHeadOnlyRefs(checkedBody.residual, recurEnv)
    val checkedLam =
      EA.Term.Lam(
        checkedVpi.residual,
        checkedBody.residual,
        l.span,
        l.name,
        l.isStable,
        l.recursion.map(_.selfRef)
      )
    CheckedTerm(Interpreter.evalLam(checkedLam, vpi, env), checkedLam)
  }

  def getType(term: CA.TypeTerm, env: Env): Value = {
    val res = checkTypeTerm(term, env).value
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

  def checkTerm(term: CA.Term, env: Env): CheckedTerm =
    try {
      term match {
        case CA.Term.Select(base, field, span) =>
          val checkedBase = checkTerm(base, env)
          val (selectorName, value) = checkSelect(checkedBase.value, field, span, env)
          CheckedTerm(value, EA.Term.App(EA.Term.GlobalRef(selectorName, span), Vector(checkedBase.residual), span))
        case l: CA.Term.Lam => checkLam(l, env)
        case app: CA.Term.App =>
          val checkedFn = checkTerm(app.fn, env)
          val checkedArgs = app.args.map(arg => checkTerm(arg, env))
          val value = checkApplyValue(checkedFn.value, checkedArgs.map(_.value), env.normalizers)
          val residual = EA.Term.App(checkedFn.residual, checkedArgs.map(_.residual), app.span)
          CheckedTerm(value, residual)
        case derive: CA.Term.Derive =>
          val goal = getType(derive.goal, env)
          val value = InstanceSearch.solve(goal, env)
          CheckedTerm(value, quoteTerm(value, quoteContext(env), derive.span))
        case m: CA.Term.Match => checkMatch(m, env)
        case b: CA.Term.Body  => checkBody(b, env)
        case term: CA.TypeTerm =>
          val checked = checkTypeTerm(term, env)
          CheckedTerm(checked.value, checked.residual)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }

}
