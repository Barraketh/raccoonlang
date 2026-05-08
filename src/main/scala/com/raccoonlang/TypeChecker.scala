package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.{BinderOps, ConstructorOps}
import com.raccoonlang.{CoreAst => CA}

object TypeChecker {
  final case class Checked(value: Value, term: CA.CheckedTerm)
  final case class CheckedType(value: Value, term: CA.CheckedTypeTerm)
  private final case class CheckedPi(value: VPi, term: CA.Term.Pi[CA.Checked])

  private def toCheckedRef(ref: CA.RawRef): CA.CheckedRef = ref match {
    case CA.Term.GlobalRef(name, span) => CA.Term.GlobalRef[CA.Checked](name, span)
    case CA.Term.LocalRef(ref, span)   => CA.Term.LocalRef[CA.Checked](ref, span)
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
    if (!defEq(actual, expected) && !sortLeq(actual, expected))
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
      fnTerm: CA.CheckedTerm,
      env: Env,
      span: Span
  )(implicit eqStore: EqStore, normalizers: NormalizerMap): Checked = {
    val fn0 = Interpreter.resolveInEqStore(fn)
    val fnTy0 = Interpreter.resolveInEqStore(fn0.tpe)

    fnTy0 match {
      case pi: VPi =>
        val completed = BinderOps.checkAndInstantiate(pi.binders, pi.env, args, env)

        Checked(
          Interpreter.evalApply(fn0, completed.values),
          CA.Term.App[CA.Checked](fnTerm, completed.terms, span)
        )
      case _ => throw CannotApplyNonFunction(fnTy0)
    }
  }

  private def checkedArg(arg: CheckedType): BinderOps.CheckedArg = BinderOps.CheckedArg(arg.value, arg.term)

  private def checkTypeApply(
      fn: Value,
      args: Vector[BinderOps.CheckedArg],
      fnTerm: CA.CheckedTerm,
      env: Env,
      span: Span
  )(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): CheckedType = {
    val checked = checkApply(fn, args, fnTerm, env, span)
    CheckedType(checked.value, checked.term.asInstanceOf[CA.CheckedTypeTerm])
  }

  private def checkApp(app: CA.Term.App[CA.Raw], env: Env)(implicit
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

  private def checkPi(pi: CA.Term.Pi[CA.Raw], env: Env)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): CheckedPi = {
    val freshened = BinderOps.freshenRawBinders(pi.binders, env)
    val checkedOut = getCheckedType(pi.out, freshened.env)
    val checkedPi = CA.Term.Pi[CA.Checked](freshened.checkedBinders, checkedOut.term, pi.span)
    CheckedPi(evalPi(checkedPi, env, freshened.vBinders), checkedPi)
  }

  def checkTypeTerm(term: CA.RawTypeTerm, env: Env)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): CheckedType = term match {
    case app: CA.Term.App[CA.Raw] =>
      val checked = checkApp(app, env)
      CheckedType(checked.value, checked.term.asInstanceOf[CA.CheckedTypeTerm])
    case CA.Term.Select(base, field, span) =>
      val checkedBase = check(base, env)
      CheckedType(
        Interpreter.evalSelect(checkedBase.value, field, env, span.start),
        CA.Term.Select[CA.Checked](checkedBase.term, field, span)
      )
    case t: CA.Term.TApp[CA.Raw] =>
      val fn = checkTypeTerm(t.fn, env)
      val args = t.args.map(arg => checkedArg(checkTypeTerm(arg, env)))
      checkTypeApply(fn.value, args, fn.term, env, t.span)
    case CA.Term.TSelect(base, field, span) =>
      val checkedBase = checkTypeTerm(base, env)
      CheckedType(
        Interpreter.evalSelect(checkedBase.value, field, env, span.start),
        CA.Term.Select[CA.Checked](checkedBase.term, field, span)
      )
    case pi: CA.Term.Pi[CA.Raw] =>
      val checked = checkPi(pi, env)
      CheckedType(checked.value, checked.term)
    case ref: CA.RawRef =>
      val checkedRef = toCheckedRef(ref)
      CheckedType(Interpreter.evalTypeTerm(checkedRef, env), checkedRef)
  }

  def evalTypeTerm(term: CA.RawTypeTerm, env: Env)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): Value = checkTypeTerm(term, env).value

  private def checkBody(body: CA.Term.Body[CA.Raw], env: Env)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): Checked = {
    val checkedLets = Vector.newBuilder[CA.CheckedLet]
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val checkedValue = check(l.value, curEnv)
      val res = checkedValue.value
      val withType = l.ty
        .map { tyTerm =>
          val checkedTy = getCheckedType(tyTerm, curEnv)
          val tyV = checkedTy.value
          checkType(res, tyV)
          checkedLets += CA.Let[CA.Checked](l.localRef, Some(checkedTy.term), checkedValue.term, l.span, l.isInstance)
          Value.ascribe(res, tyV)
        }
        .getOrElse {
          checkedLets += CA.Let[CA.Checked](l.localRef, None, checkedValue.term, l.span, l.isInstance)
          res
        }
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.name, withType, meta)) else None
      curEnv.putLocal(l.localRef, withType, instanceKey, Some(CA.Term.LocalRef[CA.Checked](l.localRef, l.span)))
    }
    val checkedRes = check(body.res, newEnv)
    Checked(checkedRes.value, CA.Term.Body[CA.Checked](checkedLets.result(), checkedRes.term, body.span))
  }

  private def checkBranch(br: CA.RawCase, args: Seq[Value], envWithScrut: Env, expectedTy: Value)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): CA.CheckedCase = {
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
    CA.Case[CA.Checked](br.ctorName, br.argRefs, branchRes.term, br.span)
  }

  case class ReachableCtor(
      name: String,
      head: ConstructorHead,
      fieldArgs: Vector[Value],
      resultTy: Value,
      branchEqStore: EqStore
  )

  private def checkMatch(t: CA.Term.Match[CA.Raw], env: Env)(implicit
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
            val appliedCtor: Value = fresh.value

            val branchEqStore: Option[EqStore] =
              try {
                val refinable = scrut.synDeps ++ appliedCtor.synDeps
                Some(Unify.unify(scrut, appliedCtor, eqStore.allow(refinable)))
              } catch {
                case _: UnificationFailed | _: OccursCheckFailed =>
                  val refinable = scrut.tpe.synDeps ++ appliedCtor.tpe.synDeps
                  try {
                    Some(Unify.unify(scrut.tpe, appliedCtor.tpe, eqStore.allow(refinable)))
                  } catch {
                    case _: UnificationFailed | _: OccursCheckFailed => None
                  }
              }

            branchEqStore.map(eqStore => ReachableCtor(ctorName, h, fresh.value.fields, fresh.value.tpe, eqStore))

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
          val eq1 = Unify.unify(res1, scrutTpe, eqStore.allow(refinable0))
          Unify.unify(res2, scrutTpe, eq1)
        } catch {
          case _: UnificationFailed | _: OccursCheckFailed => return false
        }

      fields1.zip(fields2).forall { case (f1, f2) =>
        TypeChecker.getUniverse(f1.tpe)(startEq) match {
          case PropTpe => true
          case _       => TypeChecker.defEq(f1, f2)(startEq, normalizers)
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
        defEq(inferred, info.resultTy)
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

    var checkedByCtor = Map.empty[String, CA.CheckedCase]

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
    val checkedMatch = CA.Term.Match[CA.Checked](scrutChecked.term, checkedMotive.map(_.term), checkedCases, t.span)
    Checked(Interpreter.evalTerm(checkedMatch, env), checkedMatch)
  }

  private def checkLam(l: CA.Term.Lam[CA.Raw], env: Env, normalizers: NormalizerMap)(implicit
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
    val freshBody = BinderOps.freshen(vpi)
    val bodyEnv = freshBody.env

    val recurEnv =
      l.name match {
        case Some(name) => bodyEnv.putGlobal(name, Value.VConst(name, Symbol, vpi))
        case None       => bodyEnv
      }

    val checkedBody = check(l.body, recurEnv)
    val resType = Interpreter.evalTypeTerm(checkedPi.term.out, bodyEnv)

    checkType(checkedBody.value, resType)
    val checkedLam =
      CA.Term.Lam[CA.Checked](checkedPi.term, Vector.empty, checkedBody.term, l.span, l.name, l.isStable)
    Checked(Interpreter.evalLam(checkedLam, vpi, env), checkedLam)
  }

  def getCheckedType(term: CA.RawTypeTerm, env: Env)(implicit
      ctx: EqStore,
      normalizerMap: NormalizerMap
  ): CheckedType = {
    val res = checkTypeTerm(term, env)
    assertType(res.value)
    res
  }

  def getType(term: CA.RawTypeTerm, env: Env)(implicit ctx: EqStore, normalizerMap: NormalizerMap): Value =
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

  def check(term: CA.RawTerm, env: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Checked = {
    try {
      term match {
        case CA.Term.Select(base, field, span) =>
          val checkedBase = check(base, env)
          Checked(
            Interpreter.evalSelect(checkedBase.value, field, env, span.start),
            CA.Term.Select[CA.Checked](checkedBase.term, field, span)
          )
        case t: CA.Term.App[CA.Raw]   => checkApp(t, env)
        case l: CA.Term.Lam[CA.Raw]   => checkLam(l, env, normalizers)
        case m: CA.Term.Match[CA.Raw] => checkMatch(m, env)
        case b: CA.Term.Body[CA.Raw]  => checkBody(b, env)
        case term: CA.RawTypeTerm =>
          val checked = checkTypeTerm(term, env)
          Checked(checked.value, checked.term)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

  case class RelatedPis(vars: Vector[Value], out1: Value, out2: Value)

  def relatePis(pi1: VPi, pi2: VPi)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): RelatedPis = {
    if (
      pi1.binders
        .zip(pi2.binders)
        .exists { case (b1, b2) => b1.isDerived != b2.isDerived || b1.isInstance != b2.isInstance }
    )
      throw TypeMismatch(pi1, pi2)

    val freshPi1 = BinderOps.freshen(pi1)
    val sharedVars = freshPi1.vars
    val nextEnv1 = freshPi1.env
    val nextEnv2 = BinderOps.checkAndInstantiateFull(pi2.binders, pi2.env, sharedVars)

    val out1 = pi1.codomain(nextEnv1, eqStore)
    val out2 = pi2.codomain(nextEnv2, eqStore)

    RelatedPis(sharedVars, out1, out2)
  }

  private def defEqPi(pi1: VPi, pi2: VPi)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Option[Vector[Value]] = {
    try {
      val related = relatePis(pi1, pi2)
      if (defEq(related.out1, related.out2)) Some(related.vars)
      else None
    } catch {
      case _: UnificationFailed | _: TypeMismatch => None
    }
  }

  private def defEqLamId(id1: ValueId, id2: ValueId)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Boolean = {
    (id1, id2) match {
      case (ValueId.Const(n1), ValueId.Const(n2)) if n1 == n2 => true
      case (l1: ValueId.LocalId, l2: ValueId.LocalId)
          if l1.nodeId == l2.nodeId && l1.captures.length == l2.captures.length =>
        l1.captures.zip(l2.captures).forall { case (v1, v2) => defEq(v1, v2) }
      case _ => false
    }
  }

  def getNormalizerF(v1: Value, v2: Value)(implicit eqStore: EqStore, normalizers: NormalizerMap): Value => Value = {
    val key1 = Normalizers.getCarrierKey(v1.tpe)
    val key2 = Normalizers.getCarrierKey(v2.tpe)
    val normalizer =
      if (key1 == key2) key1.flatMap(normalizers.get)
      else None

    normalizer match {
      case Some(n) => (v: Value) => n.normalize(v, eqStore)
      case None    => (v: Value) => v
    }
  }

  private def sameValueObject(v1: Value, v2: Value): Boolean =
    v1.asInstanceOf[AnyRef] eq v2.asInstanceOf[AnyRef]

  private def hasSolvedDeps(v: Value)(implicit eqStore: EqStore): Boolean = v.synDeps.intersects(eqStore.solvedIds)

  private def shouldTryStructuralDefEq(a: Value, b: Value)(implicit eqStore: EqStore): Boolean =
    hasSolvedDeps(a) || hasSolvedDeps(b) || a.needsExtensionalEq || b.needsExtensionalEq

  private def defEqStructural(a: Value, b: Value)(implicit eqStore: EqStore, normalizers: NormalizerMap): Boolean =
    (a, b) match {
      case (PropTpe, PropTpe)                               => true
      case (NormalizerType, NormalizerType)                 => true
      case (LevelTpe, LevelTpe)                             => true
      case (l1: Level, l2: Level)                           => l1 == l2 || Level.leq(l1, l2) && Level.leq(l2, l1)
      case (s1: VSort, s2: VSort)                           => defEq(s1.level, s2.level)
      case (VConst(n1, _, _), VConst(n2, _, _)) if n1 == n2 => true
      case (p1: VPi, p2: VPi) if p1.binders.length == p2.binders.length => defEqPi(p1, p2).isDefined
      case (l1: VLam, l2: VLam) if l1.tpe.binders.length == l2.tpe.binders.length =>
        if (l1.eq(l2) || defEqLamId(l1.id, l2.id)) true
        else {
          defEqPi(l1.tpe, l2.tpe) match {
            case Some(vars) =>
              val res1 = l1.run(vars, eqStore)
              val res2 = l2.run(vars, eqStore)
              defEq(res1, res2)
            case None => false
          }
        }
      case (v1: AppliedValue, v2: AppliedValue) if v1.args.length == v2.args.length =>
        defEq(v1.head, v2.head) && v1.args.zip(v2.args).forall { case (arg1, arg2) => defEq(arg1, arg2) }

      case (c1: VCtor, c2: VCtor) if c1.fields.length == c2.fields.length =>
        defEq(c1.head, c2.head) && c1.fields.zip(c2.fields).forall { case (a, b) => defEq(a, b) }

      case (c1: ConstructorHead, c2: ConstructorHead) if c1.name == c2.name => true

      case (s1: VBlockedThunk, s2: VBlockedThunk) => defEqLamId(s1.id, s2.id)

      case (Var(_, id1, _), Var(_, id2, _)) if id1 == id2 => true
      case _                                              => false
    }

  def defEq(v1: Value, v2: Value)(implicit eqStore: EqStore, normalizers: NormalizerMap): Boolean = {
    if (sameValueObject(v1, v2)) true
    else {
      val normalizerF = getNormalizerF(v1, v2)

      val a = normalizerF(resolveInEqStore(v1))
      val b = normalizerF(resolveInEqStore(v2))

      sameValueObject(a, b) || a.key == b.key || (shouldTryStructuralDefEq(a, b) && defEqStructural(a, b))
    }
  }
}
