package com.raccoonlang

import com.raccoonlang.CoreAst.Term.{Ident, Lam, Match}
import com.raccoonlang.CoreAst._
import com.raccoonlang.FreshVar.{assignFreshVars, freshVar}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Util.NEL

import scala.annotation.tailrec
import scala.util.Try

object TypeChecker {

  private def checkType(value: Value, tyVal: Value)(implicit eqStore: EqStore): Unit = {
    if (!defEq(value.tpe, tyVal)) throw TypeMismatch(value, tyVal)
  }

  private def typecheckApply(fn: Value, args: NEL[Term], argEnv: Env)(implicit eqStore: EqStore): Value = {
    val fn0 = Interpreter.whnf(fn)
    val fnTy0 = Interpreter.whnf(fn0.tpe)

    fnTy0 match {
      case VPi(env, binders, outTy, _) =>
        if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

        // Typecheck argument terms in argEnv
        val vArgs = args.foldLeft(Vector.empty[Value]) { case (acc, nextArg) =>
          val v = typecheck(nextArg, argEnv)
          acc :+ v
        }

        // Typecheck args against binder types and extend pi env
        val envWithArgs =
          binders.toList.zip(vArgs).foldLeft(env.newScope) { case (curEnv, (binder, value)) =>
            val argTy = Interpreter.evalTerm(binder.ty, curEnv)
            checkType(value, argTy)
            curEnv.putLocal(binder.name, value)
          }

        // Since we've already typechecked everything we care about, now we can just evalTerm
        fn0 match {
          case VLam(body, _, _) => Interpreter.evalTerm(body, envWithArgs)
          case head: Head       => VApp(head, NEL.mk(vArgs), Interpreter.evalTerm(outTy, envWithArgs))
          case _                => throw CannotApplyNonFunction(fnTy0)
        }
      case _ => throw CannotApplyNonFunction(fnTy0)
    }
  }

  private def typecheckApplyTerm(fn: Term, args: NEL[Term], env: Env)(implicit meta: EqStore): Value = {
    val vf = typecheck(fn, env)
    typecheckApply(vf, args, env)
  }

  // Check that all type terms typecheck under a fresh var assignment to binders
  private def typecheckPi(pi: Term.Pi, env: Env)(implicit meta: EqStore): VPi = {
    val bodyEnv = pi.binders.foldLeft(env.newScope) { case (curEnv, b) =>
      val tyV = getType(b.ty, curEnv)
      curEnv.putLocal(b.name, freshVar(b.name, tyV))
    }
    getType(pi.out, bodyEnv)
    evalPi(pi, env)
  }

  private def typecheckTT(term: TypeTerm, env: Env)(implicit meta: EqStore): Value = term match {
    case t: Term.TApp => typecheckApplyTerm(t.fn, t.args, env)
    case pi: Term.Pi  => typecheckPi(pi, env)
    case ident: Ident => Interpreter.evalTerm(ident, env)
  }

  private def typecheckBody(body: Term.Body, env: Env)(implicit meta: EqStore): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = typecheck(l.value, curEnv)
      l.ty.foreach { tyTerm =>
        val tyV = getType(tyTerm, curEnv)
        checkType(res, tyV)
      }
      curEnv.putLocal(l.name, res)
    }
    typecheck(body.res, newEnv)
  }

  @tailrec
  private def peelHead(v: Value): Value = v match {
    case VApp(h, _, _) => peelHead(h)
    case other         => other
  }

  private def typecheckBranch(br: Case, args: Seq[Value], envWithScrut: Env, motive: TypeTerm)(implicit
      eqStore: EqStore
  ): Unit = {
    if (args.length != br.argNames.length) throw ArityMismatch(args.length, br.argNames.length, Some(br.span))
    val branchEnv = br.argNames.zip(args).foldLeft(envWithScrut) { case (curEnv, (argName, argVal)) =>
      curEnv.putLocal(argName, argVal)
    }
    val branchRes = typecheck(br.body, branchEnv)
    val expectedTy = getType(motive, branchEnv)
    checkType(branchRes, expectedTy)
  }

  private def typecheckMatch(t: Match, env: Env)(implicit eqStore: EqStore): Value = {
    val scrut = Interpreter.whnf(typecheck(t.scrut, env))

    val (inductiveName, inductiveCtors) = peelHead(Interpreter.whnf(scrut.tpe)) match {
      case VConst(n, Inductive(names), _) => (n, names.toSet)
      case _                              => throw NonInductiveMatch(scrut.tpe)
    }

    // Check for duplicate constructors
    t.cases.groupBy(_.ctorName).find(_._2.length > 1).foreach { case (ctor, cases) =>
      throw DuplicateCase(ctor, Some(cases(1).span))
    }

    // Check for unknown constructors
    t.cases.find(c => !inductiveCtors.contains(c.ctorName)).foreach { c =>
      throw UnknownConstructor(c.ctorName, inductiveName, Some(c.span))
    }

    val scrutConst = scrut match {
      case VConst(name, `ConstructorHead`, _)                => Some((name, Nil))
      case VApp(VConst(name, `ConstructorHead`, _), args, _) => Some((name, args.toList))
      case _                                                 => None
    }

    scrutConst match {
      case Some((head, args)) =>
        // Scrut is a constructor - we need to make sure that we have exactly one matching branch and then typecheck it
        t.cases.find(c => c.ctorName != head).foreach { c => throw UnreachableCase(c.ctorName, Some(c.span)) }
        val br = t.cases.find(c => c.ctorName == head).getOrElse(throw MissingCase(head))
        typecheckBranch(br, args, env.newScope.putLocal(t.scrutName, scrut), t.motive)
      case None =>
        // We don't know scrut to be a specific constructor - gotta check exhaustivity and typecheck all branches
        // For every possible ctor, we will try to unify its type with scrut type. If this fails, then this ctor is
        // unreachable, and so we will make sure it is not in the match. If it is possible, then the ctor is reachable,
        // and we make sure it is in the match and typecheck the branch with the resulting eqStore

        inductiveCtors.foreach { ctorName =>
          val ctorVal = env.find(ctorName).getOrElse(throw NotFound(ctorName))

          ctorVal match {
            case h @ VConst(_, ConstructorHead, ctorTy) =>
              val (freshArgs, ctorEnv) = ctorTy match {
                case pi: VPi => assignFreshVars(pi, eqStore)
                case _       => (Vector.empty[Value], env)
              }

              val ctorResTy: Value = ctorTy match {
                case VPi(_, _, out, _) =>
                  Interpreter.evalTerm(out, ctorEnv)(
                    eqStore
                  ) // Again, we've already typechecked out, so we can just eval it
                case otherTy: Value => otherTy
              }

              Try(Unify.unify(scrut.tpe, ctorResTy, eqStore, Set.empty)) match {
                case util.Failure(_) =>
                  // Case is unreachable - make sure it's not in the match
                  t.cases.find(c => c.ctorName == ctorName).foreach(c => throw UnreachableCase(ctorName, Some(c.span)))
                case util.Success(branchEqStore) =>
                  // Case is reachable - typecheck its branch
                  val br = t.cases.find(c => c.ctorName == ctorName).getOrElse(throw MissingCase(ctorName))
                  val appliedConstr =
                    if (freshArgs.nonEmpty) VApp(h, NEL.mk(freshArgs), ctorResTy)
                    else h

                  val envWithScrut = env.newScope.putLocal(t.scrutName, appliedConstr)

                  typecheckBranch(br, freshArgs, envWithScrut, t.motive)(branchEqStore)
              }

            case _ => throw UnknownConstructor(ctorName, inductiveName)
          }
        }
    }

    Interpreter.evalTerm(t, env)
  }

  def typecheckLam(l: Lam, env: Env)(implicit eqStore: EqStore): Value = {
    val vpi = typecheckPi(l.ty, env)
    val (_, bodyEnv) = assignFreshVars(vpi, eqStore)

    val bodyV = typecheck(l.body, bodyEnv)
    val resType = Interpreter.evalTerm(l.ty.out, bodyEnv)

    checkType(bodyV, resType)
    Interpreter.evalLam(l, vpi, env)
  }

  def getType(term: TypeTerm, env: Env)(implicit ctx: EqStore): Value = {
    val res = typecheck(term, env)

    Interpreter.whnf(res.tpe) match {
      case VUniverse => res
      case _         => throw NotAType(res)
    }
  }

  def typecheck(term: CoreAst.Term, env: Env)(implicit eqStore: EqStore): Value = {
    try {
      term match {
        case term: TypeTerm => typecheckTT(term, env)
        case t: Term.App    => typecheckApplyTerm(t.fn, t.args, env)
        case l: Term.Lam    => typecheckLam(l, env)
        case m: Term.Match  => typecheckMatch(m, env)
        case b: Term.Body   => typecheckBody(b, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }

  }

  private def defEqPi(pi1: VPi, pi2: VPi)(implicit eqStore: EqStore): Option[(Env, Env)] = {
    val (nextEnv1, nextEnv2) = pi1.binders.zip(pi2.binders).foldLeft((pi1.env.newScope, pi2.env.newScope)) {
      case ((curEnv1, curEnv2), (b1, b2)) =>
        val t1 = Interpreter.evalTerm(b1.ty, curEnv1)
        val t2 = evalTerm(b2.ty, curEnv2)
        if (!defEq(t1, t2)) return None

        val x = FreshVar.freshVar(b1.name, t1)
        (curEnv1.putLocal(b1.name, x), curEnv2.putLocal(b2.name, x))
    }
    val out1 = evalTerm(pi1.out, nextEnv1)
    val out2 = evalTerm(pi2.out, nextEnv2)
    if (defEq(out1, out2)) Some((nextEnv1, nextEnv2))
    else None

  }

  private def defEqLamId(id1: LamId, id2: LamId)(implicit eqStore: EqStore): Boolean = {
    (id1, id2) match {
      case (LamId.Const(n1), LamId.Const(n2)) if n1 == n2 => true
      case (l1: LamId.LocalId, l2: LamId.LocalId) if l1.nodeId == l2.nodeId && l1.params.length == l2.params.length =>
        l1.params.zip(l2.params).forall { case (v1, v2) => defEq(v1, v2) }
      case _ => false
    }
  }

  private def defEq(v1: Value, v2: Value)(implicit eqStore: EqStore): Boolean = {
    val a = whnf(v1)
    val b = whnf(v2)

    (a, b) match {
      case (VUniverse, VUniverse)                                       => true
      case (VConst(n1, _, _), VConst(n2, _, _)) if n1 == n2             => true
      case (p1: VPi, p2: VPi) if p1.binders.length == p2.binders.length => defEqPi(p1, p2).isDefined
      case (l1: VLam, l2: VLam) if l1.tpe.binders.length == l2.tpe.binders.length =>
        if (l1.eq(l2) || defEqLamId(l1.id, l2.id)) true
        else {
          defEqPi(l1.tpe, l2.tpe) match {
            case Some((env1, env2)) =>
              val res1 = evalTerm(l1.body, env1)
              val res2 = evalTerm(l2.body, env2)
              defEq(res1, res2)
            case None => false
          }
        }
      case (VApp(h1, args1, _), VApp(h2, args2, _)) if args1.length == args2.length =>
        defEq(h1, h2) && args1.zip(args2).forall { case (arg1, arg2) => defEq(arg1, arg2) }

      case (s1: StuckMatch, s2: StuckMatch) => defEqLamId(s1.id, s2.id) && defEq(s1.scrut, s2.scrut)

      case (Var(_, id1, _), Var(_, id2, _)) if id1 == id2 => true
      case _                                              => false
    }
  }

}
