package com.raccoonlang

import com.raccoonlang.CoreAst.Term.{Ident, Lam, Match}
import com.raccoonlang.CoreAst._
import com.raccoonlang.FreshVar.{assignFreshVars, freshVar}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

object TypeChecker {

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
      case _                     => throw NotAType(value.tpe)
    }
  }

  private def typecheckApply(fn: Value, args: NEL[Value])(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Value = {
    val fn0 = Interpreter.resolveInEqStore(fn)
    val fnTy0 = Interpreter.resolveInEqStore(fn0.tpe)

    fnTy0 match {
      case VPi(env, binders, _, _, _, _, _) =>
        if (binders.length != args.length)
          throw ArityMismatch(binders.length, args.length)

        // Typecheck args against binder types and extend pi env
        binders.toList.zip(args.toList).foldLeft(env.newScope) { case (curEnv, (binder, value)) =>
          val openedEnv = TypePatternOps.matchValue(curEnv, binder.ty, value.tpe, eqStore)
          openedEnv.putLocal(binder.name, value)
        }

        // Since we've already typechecked everything we care about, now we can just evalTerm
        Interpreter.evalApply(fn0, args)
      case _ => throw CannotApplyNonFunction(fnTy0)
    }
  }

  private def typecheckTApp(app: Term.TApp, env: Env)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): Value = {
    val fn = typecheckTT(app.fn, env)
    val args = app.args.map(arg => typecheckTT(arg, env))
    typecheckApply(fn, args)
  }

  private def typecheckApp(app: Term.App, env: Env)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): Value = {
    val fn = typecheck(app.fn, env)
    val args = app.args.map(arg => typecheck(arg, env))
    typecheckApply(fn, args)
  }

  // Check that all type terms typecheck under a fresh var assignment to binders
  private def typecheckPi(pi: Term.Pi, env: Env)(implicit meta: EqStore, normalizers: NormalizerMap): VPi = {
    val bodyEnv = pi.binders.foldLeft(env.newScope) { case (curEnv, b) =>
      val (openedEnv, domTy, _) = TypePatternOps.freshOpen(curEnv, b.ty, meta)
      openedEnv.putLocal(b.name, freshVar(b.name, domTy))
    }
    getType(pi.out, bodyEnv)
    evalPi(pi, env)
  }

  private def typecheckTT(term: TypeTerm, env: Env)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): Value = term match {
    case t: Term.TApp => typecheckTApp(t, env)
    case pi: Term.Pi  => typecheckPi(pi, env)
    case ident: Ident => Interpreter.evalTerm(ident, env)
  }

  private def typecheckBody(body: Term.Body, env: Env)(implicit
      meta: EqStore,
      normalizers: NormalizerMap
  ): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = typecheck(l.value, curEnv)
      val withType = l.ty
        .map { tyTerm =>
          val tyV = getType(tyTerm, curEnv)
          checkType(res, tyV)
          res match {
            case u: UpdatableType => u.withTpe(tyV)
            case _                => res
          }
        }
        .getOrElse(res)
      curEnv.putLocal(l.name, withType)
    }
    typecheck(body.res, newEnv)
  }

  private def typecheckBranch(br: Case, args: Seq[Value], envWithScrut: Env, motive: TypeTerm)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Unit = {
    if (args.length != br.argNames.length)
      throw ArityMismatch(args.length, br.argNames.length, Some(br.span))
    val branchEnv = br.argNames.zip(args).foldLeft(envWithScrut.newScope) { case (curEnv, (argName, argVal)) =>
      curEnv.putLocal(argName, argVal)
    }
    val branchRes = typecheck(br.body, branchEnv)
    val expectedTy = getType(motive, branchEnv)
    checkType(branchRes, expectedTy)
  }

  case class ReachableCtor(
      name: String,
      head: ConstructorHead,
      fieldArgs: Vector[Value],
      resultTy: Value,
      branchEqStore: EqStore
  )

  private def typecheckMatch(t: Match, env: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Value = {

    def freshCtorCopy(h: ConstructorHead): (Vector[Value], Value) =
      h.tpe match {
        case pi: VPi =>
          val (freshArgs, ctorEnv, _) = assignFreshVars(pi, eqStore)
          val ctorResTy = pi.codomain(ctorEnv, eqStore)
          (freshArgs.drop(h.numParams).map(v => v: Value), ctorResTy)

        case otherTy => (Vector.empty, otherTy)
      }

    def computeReachableCtors(
        scrutTpe: Value,
        inductiveName: String,
        ctorNames: Vector[String]
    ): Vector[ReachableCtor] =
      ctorNames.flatMap { ctorName =>
        env.find(ctorName).getOrElse(throw NotFound(ctorName)) match {
          case h @ ConstructorHead(_, numParams, _, ctorTy) =>
            val (freshArgs, ctorEnv, _) = ctorTy match {
              case pi: VPi => assignFreshVars(pi, eqStore)
              case _       => (Vector.empty[Var], env, scala.collection.immutable.BitSet.empty)
            }

            val ctorResTy: Value = ctorTy match {
              case VPi(_, _, codomain, _, _, _, _) => codomain(ctorEnv, eqStore)
              case otherTy                         => otherTy
            }

            val refinable = scrutTpe.synDeps ++ ctorResTy.synDeps

            try {
              val branchEqStore = Unify.unify(scrutTpe, ctorResTy, eqStore.allow(refinable))
              Some(
                ReachableCtor(
                  name = ctorName,
                  head = h,
                  fieldArgs = freshArgs.drop(numParams).map(v => v: Value),
                  resultTy = ctorResTy,
                  branchEqStore = branchEqStore
                )
              )
            } catch {
              case _: UnificationFailed | _: OccursCheckFailed => None
            }

          case _ => throw UnknownConstructor(ctorName, inductiveName)
        }
      }

    def allowLargeElimination(scrutTpe: Value, reachable: Vector[ReachableCtor]): Boolean = {
      if (reachable.isEmpty) return true
      if (reachable.length > 1) return false

      val only = reachable.head
      val (fields1, res1) = freshCtorCopy(only.head)
      val (fields2, res2) = freshCtorCopy(only.head)

      val refinable0 = scrutTpe.synDeps ++ res1.synDeps ++ res2.synDeps

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

    val scrut = Interpreter.resolveInEqStore(typecheck(t.scrut, env))
    val scrutTpe = Interpreter.resolveInEqStore(scrut.tpe)

    val (inductiveName, inductiveCtorNames) = scrutTpe match {
      case VConst(n, Inductive(meta), _)             => (n, meta.constructorNames)
      case VApp(VConst(n, Inductive(meta), _), _, _) => (n, meta.constructorNames)
      case _                                         => throw NonInductiveMatch(scrut.tpe)
    }
    val inductiveCtorSet = inductiveCtorNames.toSet

    // Duplicate / unknown branch checks are purely syntactic.
    t.cases.groupBy(_.ctorName).find(_._2.length > 1).foreach { case (ctor, cases) =>
      throw DuplicateCase(ctor, Some(cases(1).span))
    }

    t.cases.find(c => !inductiveCtorSet.contains(c.ctorName)).foreach { c =>
      throw UnknownConstructor(c.ctorName, inductiveName, Some(c.span))
    }

    val withScrut = env.newScope.putLocal(t.scrutName, scrut)
    val motiveTy = getType(t.motive, withScrut)

    // Shared type-based reachability analysis.
    lazy val reachableByType: Vector[ReachableCtor] =
      computeReachableCtors(scrutTpe, inductiveName, inductiveCtorNames)

    // Large elimination from Prop is allowed only for empty / singleton-like propositions.
    if (
      getUniverse(scrut.tpe) == PropTpe &&
      getUniverse(motiveTy) != PropTpe &&
      !allowLargeElimination(scrutTpe, reachableByType)
    ) {
      throw PropEliminationRestricted(inductiveName, motiveTy, Some(t.span))
    }

    scrut match {
      case VCtor(h, fields, _) =>
        // Exact-value fast path: once the scrutinee is known to be a specific constructor,
        // every other constructor branch is unreachable.
        t.cases.find(_.ctorName != h.name).foreach { c =>
          throw UnreachableCase(c.ctorName, Some(c.span))
        }

        val br = t.cases.find(_.ctorName == h.name).getOrElse(throw MissingCase(h.name))
        typecheckBranch(br, fields, withScrut, t.motive)

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
              val appliedCtor = VCtor(info.head, info.fieldArgs, info.resultTy)
              val envWithBranchScrut = env.newScope.putLocal(t.scrutName, appliedCtor)
              typecheckBranch(br, info.fieldArgs, envWithBranchScrut, t.motive)(info.branchEqStore, normalizers)
          }
        }
    }

    Interpreter.evalTerm(t, env)
  }

  def typecheckLam(l: Lam, env: Env, normalizers: NormalizerMap)(implicit eqStore: EqStore): Value = {
    implicit val nextNormalizerMap = l.uses.foldLeft(normalizers) { case (curNormalizers, nextUse) =>
      val normalizer = typecheck(nextUse.normalizer, env)(eqStore, curNormalizers)
      normalizer match {
        case n: Value.Normalizer => curNormalizers.use(n)
        case _ =>
          throw TypeMismatch(normalizer, NormalizerType)
      }
    }

    val vpi = typecheckPi(l.ty, env)
    val (_, bodyEnv, _) = assignFreshVars(vpi, eqStore)

    val recurEnv =
      l.name match {
        case Some(name) => bodyEnv.putGlobal(name, Value.VConst(name, Symbol, vpi))
        case None       => bodyEnv
      }

    val bodyV = typecheck(l.body, recurEnv)
    val resType = Interpreter.evalTypeTerm(l.ty.out, bodyEnv)

    checkType(bodyV, resType)
    Interpreter.evalLam(l, vpi, env)
  }

  def getType(term: TypeTerm, env: Env)(implicit ctx: EqStore, normalizerMap: NormalizerMap): Value = {
    val res = typecheckTT(term, env)
    assertType(res)
    res
  }

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

  def typecheck(term: CoreAst.Term, env: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Value = {
    try {
      term match {
        case term: TypeTerm => typecheckTT(term, env)
        case t: Term.App    => typecheckApp(t, env)
        case l: Term.Lam    => typecheckLam(l, env, normalizers)
        case m: Term.Match  => typecheckMatch(m, env)
        case b: Term.Body   => typecheckBody(b, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }

  }

  private def defEqPi(pi1: VPi, pi2: VPi)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Option[(Vector[Var], EqStore)] = {
    val (vars1, nextEnv1, newVars1) = FreshVar.assignFreshVars(pi1, eqStore)
    val (vars2, nextEnv2, newVars2) = FreshVar.assignFreshVars(pi2, eqStore)

    val newEqStore = vars1.zip(vars2).foldLeft(eqStore.allow(newVars1 ++ newVars2)) { case (curEqStore, (var1, var2)) =>
      Unify.unify(var1, var2, curEqStore)
    }

    val out1 = pi1.codomain(nextEnv1, newEqStore)
    val out2 = pi2.codomain(nextEnv2, newEqStore)
    if (defEq(out1, out2)(newEqStore, normalizers)) Some((vars1, newEqStore))
    else None
  }

  private def defEqLamId(id1: LamId, id2: LamId)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Boolean = {
    (id1, id2) match {
      case (LamId.Const(n1), LamId.Const(n2)) if n1 == n2 => true
      case (l1: LamId.LocalId, l2: LamId.LocalId) if l1.nodeId == l2.nodeId && l1.params.length == l2.params.length =>
        l1.params.zip(l2.params).forall { case (v1, v2) => defEq(v1, v2) }
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

  def defEq(v1: Value, v2: Value)(implicit eqStore: EqStore, normalizers: NormalizerMap): Boolean = {
    val normalizerF = getNormalizerF(v1, v2)

    val a = normalizerF(resolveInEqStore(v1))
    val b = normalizerF(resolveInEqStore(v2))

    (a, b) match {
      case (VSort(l1), VSort(l2)) if l1 == l2                           => true
      case (PropTpe, PropTpe)                                           => true
      case (NormalizerType, NormalizerType)                             => true
      case (LevelTpe, LevelTpe)                                         => true
      case (l1: Level, l2: Level)                                       => Level.leq(l1, l2) && Level.leq(l2, l1)
      case (s1: VSort, s2: VSort)                                       => defEq(s1.level, s2.level)
      case (VConst(n1, _, _), VConst(n2, _, _)) if n1 == n2             => true
      case (p1: VPi, p2: VPi) if p1.binders.length == p2.binders.length => defEqPi(p1, p2).isDefined
      case (l1: VLam, l2: VLam) if l1.tpe.binders.length == l2.tpe.binders.length =>
        if (l1.eq(l2) || defEqLamId(l1.id, l2.id)) true
        else {
          defEqPi(l1.tpe, l2.tpe) match {
            case Some((vars, nextEqStore)) =>
              val varsNEL = NEL.mk(vars)
              val res1 = l1.run(varsNEL, nextEqStore)
              val res2 = l2.run(varsNEL, nextEqStore)
              defEq(res1, res2)(nextEqStore, normalizers)
            case None => false
          }
        }
      case (v1: AppliedValue, v2: AppliedValue) if v1.args.length == v2.args.length =>
        defEq(v1.head, v2.head) && v1.args.zip(v2.args).forall { case (arg1, arg2) => defEq(arg1, arg2) }

      case (c1: VCtor, c2: VCtor) if c1.fields.length == c2.fields.length =>
        defEq(c1.head, c2.head) && c1.fields.zip(c2.fields).forall { case (a, b) => defEq(a, b) } && defEq(
          c1.tpe,
          c2.tpe
        )

      case (c1: ConstructorHead, c2: ConstructorHead) if c1.name == c2.name => true

      case (s1: VMatch, s2: VMatch) => defEqLamId(s1.id, s2.id) && defEq(s1.scrut, s2.scrut)

      case (Var(_, id1, _), Var(_, id2, _)) if id1 == id2 => true
      case _                                              => false
    }
  }

}
