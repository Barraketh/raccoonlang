package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.{BinderOps, ConstructorOps}
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

object TypeChecker {
  final case class Checked(value: Value, term: EA.Term)
  final case class CheckedType(value: Value, term: EA.TypeTerm)
  private final case class CheckedPi(value: VPi, term: EA.Term.Pi)

  private def toCheckedRef(ref: CA.Term.Ref): EA.Term.Ref = ref match {
    case CA.Term.GlobalRef(name, span) => EA.Term.GlobalRef(name, span)
    case CA.Term.LocalRef(ref, span)   => EA.Term.LocalRef(ref, span)
  }

  def sortLeq(a: Value, b: Value)(implicit eqStore: EqStore): Boolean = {
    (Interpreter.resolveInEqStore(a), Interpreter.resolveInEqStore(b)) match {
      case (Value.VSort(u), Value.VSort(v)) => Level.leq(u, v)
      case (l1: Level, l2: Level)           => Level.leq(l1, l2)
      case (l1: Level, v: Var)              => Level.leq(l1, Level.mk(v.id))
      case (v: Var, l2: Level)              => Level.leq(Level.mk(v.id), l2)
      case _                                => false
    }
  }

  def checkFits(actual: Value, expected: Value)(implicit eqStore: EqStore, normalizers: NormalizerMap): Unit =
    if (!ValueEquivalence.defEq(actual, expected) && !sortLeq(actual, expected))
      throw TypeMismatch(expected, actual)

  def checkType(value: Value, tyVal: Value)(implicit eqStore: EqStore, normalizers: NormalizerMap): Unit =
    checkFits(value.tpe, tyVal)

  def getUniverse(value: Value)(implicit eqStore: EqStore): Universe = {
    resolveInEqStore(value.tpe) match {
      case u: Universe           => u
      case _ if value == PropTpe => PropTpe
      case _ =>
        throw NotAType(value.tpe)
    }
  }

  private def checkApply(
      fn: Value,
      args: Vector[BinderOps.CheckedArg],
      fnTerm: EA.Term,
      env: TypecheckEnv,
      span: Span
  )(implicit eqStore: EqStore, normalizers: NormalizerMap): Checked = {
    val fn0 = Interpreter.resolveInEqStore(fn)
    val fnTy0 = Interpreter.resolveInEqStore(fn0.tpe)

    fnTy0 match {
      case pi: VPi =>
        val completed = BinderOps.checkAndInstantiate(pi.binders, pi.env, args, env)

        Checked(
          Interpreter.evalApply(fn0, completed.values),
          EA.Term.App(fnTerm, completed.terms, span)
        )
      case _ => throw CannotApplyNonFunction(fnTy0)
    }
  }

  private def checkedArg(arg: CheckedType): BinderOps.CheckedArg = BinderOps.CheckedArg(arg.value, arg.term)

  private def computePiClassifier(vars: Vector[Value], outType: Value)(implicit eqStore: EqStore): Universe =
    TypeChecker.getUniverse(outType) match {
      case PropTpe => PropTpe
      case VSort(outLevel) =>
        val domLevels: Vector[Level] = vars
          .map(v => TypeChecker.getUniverse(v.tpe))
          .collect { case VSort(level) => level }

        VSort(Level.max(domLevels :+ outLevel))
    }

  private def checkTypeApply(
      fn: Value,
      args: Vector[BinderOps.CheckedArg],
      fnTerm: EA.Term,
      env: TypecheckEnv,
      span: Span
  )(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): CheckedType = {
    val checked = checkApply(fn, args, fnTerm, env, span)
    CheckedType(checked.value, checked.term.asInstanceOf[EA.TypeTerm])
  }

  private def checkApp(app: CA.Term.App, env: TypecheckEnv)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): Checked = {
    val fn = check(app.fn, env)
    val args = app.args.map { arg =>
      val checkedArg = check(arg, env)
      BinderOps.CheckedArg(checkedArg.value, checkedArg.term)
    }
    checkApply(fn.value, args, fn.term, env, app.span)
  }

  private def checkPi(pi: CA.Term.Pi, env: TypecheckEnv)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): CheckedPi = {
    val (vBinders, checkedBinders) = BinderOps.toVBinders(pi.binders, env)
    val binderEnv = BinderOps.freshen(vBinders, env)
    val checkedOut = getCheckedType(pi.out, binderEnv)
    val freshArgs = vBinders.map(binder => binderEnv(binder.localRef))
    val classifier = computePiClassifier(freshArgs, checkedOut.value)
    val checkedPi = EA.Term.Pi(checkedBinders, checkedOut.term, classifier, pi.span)
    CheckedPi(evalPi(checkedPi, env, vBinders), checkedPi)
  }

  def checkTypeTerm(term: CA.TypeTerm, env: TypecheckEnv)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): CheckedType = term match {
    case t: CA.Term.TApp =>
      val fn = checkTypeTerm(t.fn, env)
      val args = t.args.map(arg => checkedArg(checkTypeTerm(arg, env)))
      checkTypeApply(fn.value, args, fn.term, env, t.span)
    case CA.Term.TSelect(base, field, span) =>
      val checkedBase = checkTypeTerm(base, env)
      CheckedType(
        Interpreter.evalSelect(checkedBase.value, field, env, span.start),
        EA.Term.Select(checkedBase.term, field, span)
      )
    case pi: CA.Term.Pi =>
      val checked = checkPi(pi, env)
      CheckedType(checked.value, checked.term)
    case ref: CA.Term.Ref =>
      val checkedRef = toCheckedRef(ref)
      CheckedType(Interpreter.evalTypeTerm(checkedRef, env), checkedRef)
  }

  def evalTypeTerm(term: CA.TypeTerm, env: TypecheckEnv)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): Value = checkTypeTerm(term, env).value

  private def checkBody(body: CA.Term.Body, env: TypecheckEnv)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): Checked = {
    val checkedLets = Vector.newBuilder[EA.Let]
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val checkedValue = check(l.value, curEnv)
      val res = checkedValue.value
      val withType = l.ty
        .map { tyTerm =>
          val checkedTy = getCheckedType(tyTerm, curEnv)
          val tyV = checkedTy.value
          checkType(res, tyV)
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
      eqStore: EqStore,
      normalizers: NormalizerMap
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
    checkType(branchRes.value, expectedTy)
    EA.Case(br.ctorName, br.argRefs, branchRes.term, br.span)
  }

  case class ReachableCtor(
      name: String,
      head: ConstructorHead,
      fieldArgs: Vector[Value],
      resultTy: Value,
      branchEqStore: EqStore
  )

  private def checkMatch(t: CA.Term.Match, env: TypecheckEnv)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Checked = {

    def computeReachableCtors(
        scrut: Value,
        inductiveName: String,
        ctorNames: Vector[String],
        scrutTypeParams: Vector[Value]
    ): Vector[ReachableCtor] =
      ctorNames.flatMap { ctorName =>
        env(ctorName) match {
          case h: ConstructorHead =>
            val fresh = ConstructorOps.freshFromParams(h, scrutTypeParams)
            val appliedCtor: Value = fresh

            val branchEqStore: Option[EqStore] =
              try {
                val refinable = scrut.synDeps ++ appliedCtor.synDeps
                Some(ValueEquivalence.unify(scrut, appliedCtor, eqStore.allow(refinable)))
              } catch {
                case _: UnificationFailed | _: OccursCheckFailed =>
                  val refinable = scrut.tpe.synDeps ++ appliedCtor.tpe.synDeps
                  try {
                    Some(ValueEquivalence.unify(scrut.tpe, appliedCtor.tpe, eqStore.allow(refinable)))
                  } catch {
                    case _: UnificationFailed | _: OccursCheckFailed => None
                  }
              }

            branchEqStore.map(eqStore => ReachableCtor(ctorName, h, fresh.fields, fresh.tpe, eqStore))

          case _ => throw UnknownConstructor(ctorName, inductiveName)
        }
      }

    def allowLargeElimination(scrutTpe: Value, reachable: Vector[ReachableCtor]): Boolean = {
      if (reachable.isEmpty) return true
      if (reachable.length > 1) return false

      val only = reachable.head
      val copy1 = ConstructorOps.freshAll(only.head)
      val copy2 = ConstructorOps.freshAll(only.head)
      val (fields1, res1) = (copy1.fields, copy1.tpe)
      val (fields2, res2) = (copy2.fields, copy2.tpe)

      val refinable0 = DepSet.unionAll(scrutTpe.synDeps, res1.synDeps, res2.synDeps)

      val startEq =
        try {
          val eq1 = ValueEquivalence.unify(res1, scrutTpe, eqStore.allow(refinable0))
          ValueEquivalence.unify(res2, scrutTpe, eq1)
        } catch {
          case _: UnificationFailed | _: OccursCheckFailed => return false
        }

      fields1.zip(fields2).forall { case (f1, f2) =>
        TypeChecker.getUniverse(f1.tpe)(startEq) match {
          case PropTpe => true
          case _       => ValueEquivalence.defEq(f1, f2)(startEq, normalizers)
        }
      }
    }

    val scrutChecked = check(t.scrut, env)
    val scrut = Interpreter.resolveInEqStore(scrutChecked.value)
    val scrutTpe = Interpreter.resolveInEqStore(scrut.tpe)

    val (inductiveName, inductiveCtorNames, scrutTypeParams) = scrutTpe match {
      case VConst(n, Inductive(meta), _)                => (n, meta.constructorNames, Vector.empty[Value])
      case VApp(VConst(n, Inductive(meta), _), args, _) => (n, meta.constructorNames, args.take(meta.paramCount))
      case _                                            => throw NonInductiveMatch(scrut.tpe)
    }
    val inductiveCtorSet = inductiveCtorNames.toSet

    t.cases.groupBy(_.ctorName).find(_._2.length > 1).foreach { case (ctor, cases) =>
      throw DuplicateCase(ctor, Some(cases(1).span))
    }

    t.cases.find(c => !inductiveCtorSet.contains(c.ctorName)).foreach { c =>
      throw UnknownConstructor(c.ctorName, inductiveName, Some(c.span))
    }

    lazy val reachableByType: Vector[ReachableCtor] =
      computeReachableCtors(scrut, inductiveName, inductiveCtorNames, scrutTypeParams)

    def inferMotiveFromReachable(reachable: Vector[ReachableCtor]): Value = {
      val first = reachable.headOption.getOrElse {
        throw MissingReturningClause("no constructors are reachable", Some(t.span))
      }
      val inferred = first.resultTy
      val allEqual = reachable.tail.forall { info =>
        ValueEquivalence.defEq(inferred, info.resultTy)
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

    if (
      getUniverse(scrut.tpe) == PropTpe &&
      getUniverse(motiveTy) != PropTpe &&
      !allowLargeElimination(scrutTpe, reachableByType)
    ) {
      throw PropEliminationRestricted(inductiveName, motiveTy, Some(t.span))
    }

    var checkedByCtor = Map.empty[String, EA.Case]

    scrut match {
      case VCtor(h, fields, _) =>
        t.cases.find(_.ctorName != h.name).foreach { c =>
          throw UnreachableCase(c.ctorName, Some(c.span))
        }

        val br = t.cases.find(_.ctorName == h.name).getOrElse(throw MissingCase(h.name))
        checkedByCtor += h.name -> checkBranch(br, fields, env, motiveTy)

      case _ =>
        val reachableMap = reachableByType.map(info => info.name -> info).toMap

        inductiveCtorNames.foreach { ctorName =>
          reachableMap.get(ctorName) match {
            case None =>
              t.cases.find(_.ctorName == ctorName).foreach { c =>
                throw UnreachableCase(ctorName, Some(c.span))
              }

            case Some(info) =>
              val br = t.cases.find(_.ctorName == ctorName).getOrElse(throw MissingCase(ctorName))
              checkedByCtor += ctorName -> checkBranch(br, info.fieldArgs, env, motiveTy)(
                info.branchEqStore,
                normalizers
              )
          }
        }
    }

    val checkedCases = t.cases.map { c =>
      checkedByCtor.getOrElse(c.ctorName, throw WTF(s"Unchecked reachable case ${c.ctorName}"))
    }
    val checkedMatch = EA.Term.Match(scrutChecked.term, checkedMotive.map(_.term), checkedCases, t.span)
    Checked(Interpreter.evalTerm(checkedMatch, env), checkedMatch)
  }

  private def checkLam(l: CA.Term.Lam, env: TypecheckEnv, normalizers: NormalizerMap)(implicit
      eqStore: EqStore
  ): Checked = {
    implicit val nextNormalizerMap = l.uses.foldLeft(normalizers) { case (curNormalizers, nextUse) =>
      val normalizer = check(nextUse.normalizer, env)(eqStore, curNormalizers)
      normalizer.value match {
        case n: Value.Normalizer => curNormalizers.use(n)
        case _ =>
          throw TypeMismatch(normalizer.value, NormalizerType)
      }
    }

    val checkedPi = checkPi(l.ty, env)
    val vpi = checkedPi.value
    val bodyEnv = BinderOps.freshen(vpi.binders, env)

    val recurEnv =
      l.name match {
        case Some(name) => bodyEnv.putGlobal(name, Value.VConst(name, Symbol, vpi))
        case None       => bodyEnv
      }

    val checkedBody = check(l.body, recurEnv)
    val resType = Interpreter.evalTypeTerm(checkedPi.term.out, bodyEnv)

    checkType(checkedBody.value, resType)
    val checkedLam =
      EA.Term.Lam(checkedPi.term, Vector.empty, checkedBody.term, l.span, l.name, l.isStable)
    Checked(Interpreter.evalLam(checkedLam, vpi, env), checkedLam)
  }

  def getCheckedType(term: CA.TypeTerm, env: TypecheckEnv)(implicit
      ctx: EqStore,
      normalizerMap: NormalizerMap
  ): CheckedType = {
    val res = checkTypeTerm(term, env)
    assertType(res.value)
    res
  }

  def getType(term: CA.TypeTerm, env: TypecheckEnv)(implicit ctx: EqStore, normalizerMap: NormalizerMap): Value =
    getCheckedType(term, env).value

  def assertType(value: Value)(implicit ctx: EqStore): Unit = {
    Interpreter.resolveInEqStore(value) match {
      case PropTpe =>
      case _ =>
        Interpreter.resolveInEqStore(value.tpe) match {
          case _: VSort | PropTpe =>
          case _ =>
            throw NotAType(value)
        }
    }
  }

  def check(term: CA.Term, env: TypecheckEnv)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Checked = {
    try {
      term match {
        case CA.Term.Select(base, field, span) =>
          val checkedBase = check(base, env)
          Checked(
            Interpreter.evalSelect(checkedBase.value, field, env, span.start),
            EA.Term.Select(checkedBase.term, field, span)
          )
        case t: CA.Term.App   => checkApp(t, env)
        case l: CA.Term.Lam   => checkLam(l, env, normalizers)
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
