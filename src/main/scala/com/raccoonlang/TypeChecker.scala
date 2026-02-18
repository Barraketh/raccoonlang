package com.raccoonlang

import com.raccoonlang.CoreAst.Term.Match
import com.raccoonlang.CoreAst._
import com.raccoonlang.Interpreter._
import com.raccoonlang.Util.NEL

import scala.annotation.tailrec
import scala.util.Try

object TypeChecker {

  // Fresh symbol name helper
  private var gensymId: Long = 0L
  private def freshVar(name: String, tpe: Value) = {
    gensymId += 1
    Var(name, gensymId, tpe)
  }

  private def check(value: Value, tyVal: Value, env: Env): Unit = { unify(value.tpe, tyVal, env); () }

  private def typecheckApply(fn: Value, args: NEL[Term], argsEnv: Env): Value = {
    fn.tpe match {
      case VPi(env, binders, outTy) =>
        if (binders.length != args.length)
          error(s"Cannot apply function - expected ${binders.length} params, got ${args.length}")

        val vArgs = args.map(a => typecheck(a, argsEnv))
        val envWithArgs = binders.zip(vArgs).foldLeft(env.newScope) { case (curEnv, (binder, value)) =>
          val argTy = getType(binder.ty, curEnv)
          check(value, argTy, curEnv)
          curEnv.put(binder.name, value)
        }
        fn match {
          case VLam(body, _, _) =>
            evalTerm(body, envWithArgs) match {
              case StuckMatch(tpe) => VApp(fn, vArgs, tpe)
              case other           => other
            }
          case _ => VApp(fn, vArgs, typecheckTT(outTy, envWithArgs))
        }
      case _ => error(s"Cannot apply non-fn type ${fn.tpe}")
    }
  }

  private def typecheckTT(term: TypeTerm, env: Env): Value = term match {
    case t: Term.TApp =>
      val fn = typecheck(t.fn, env)
      typecheckApply(fn, t.args, env)
    case _ => evalTerm(term, env)
  }

  private def assignFreshVars(vpi: VPi): (Vector[Value], Env) = vpi.binders.foldLeft(Vector.empty[Value] -> vpi.env) {
    case ((curValues, curEnv), binder) =>
      val tyV = getType(binder.ty, curEnv)
      val fresh = freshVar(binder.name, tyV)
      (curValues :+ fresh, curEnv.put(binder.name, fresh))
  }

  private def typecheckBody(body: Term.Body, env: Env): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = typecheck(l.value, curEnv)
      l.ty.foreach { tyTerm =>
        val tyV = getType(tyTerm, curEnv)
        check(res, tyV, curEnv)
      }
      curEnv.put(l.name, res)
    }
    typecheck(body.res, newEnv)
  }

  @tailrec
  private def peelHead(v: Value): Value = v match {
    case VApp(h, _, _) => peelHead(h)
    case other         => other
  }

  private def tyecheckMatch(m: Match, env: Env): Value = {
    val scrut = typecheck(m.scrut, env)
    val withScrut = env.put(m.scrutName, scrut)

    def unifyScrutWithCtor(ctorName: String): (Env, Vector[Value]) = {
      val ctorVal = env.find(ctorName).getOrElse(error(s"Constructor ${ctorName} not found"))

      ctorVal match {
        case VConst(_, ConstructorHead, ctorTy) =>
          val (freshArgs, ctorEnv) = ctorTy match {
            case pi: VPi => assignFreshVars(pi)
            case _       => (Vector.empty[Value], env)
          }

          val ctorResTy: Value = ctorTy match {
            case VPi(_, _, out) => getType(out, ctorEnv)
            case otherTy: Value => otherTy
          }

          val appliedConstr =
            if (freshArgs.nonEmpty) VApp(ctorVal, NEL.mk(freshArgs), ctorResTy)
            else ctorVal

          // Refine env by unifying scrutinee with applied constructor
          val refinedEnv = unify(scrut, appliedConstr, withScrut)
          (refinedEnv, freshArgs)
        case other => error(s"${ctorName} is not a constructor: $other")
      }
    }

    val ctrSet = peelHead(scrut.tpe) match {
      case VConst(_, Inductive(names), _) => names.toSet
      case _                              => error(s"Cannot match on non-inductive type ${scrut.tpe}")
    }
    val userCtrs = m.cases.map(_.ctorName)

    val duplicates = userCtrs.groupBy(n => n).filter(_._2.length > 1)
    if (duplicates.nonEmpty) error(s"Duplicate cases for ctrs ${duplicates.keys}")

    val missing = ctrSet -- userCtrs
    // Each missing ctor must be unreachable - that is, must fail to unify with scrut
    // TODO: don't use exceptions
    missing.foreach { ctorName =>
      Try(unifyScrutWithCtor(ctorName)) match {
        case util.Failure(_) =>
        case util.Success(_) => error(s"Missing match case: $ctorName")
      }
    }

    m.cases.foreach { br =>
      val (refinedEnv, freshArgs) = unifyScrutWithCtor(br.ctorName)
      if (br.argNames.length != freshArgs.length)
        error(s"Wrong number of args - expected ${freshArgs.length}, got ${br.argNames.length}")

      val branchEnv = br.argNames.zip(freshArgs).foldLeft(refinedEnv.newScope) { case (curEnv, (argName, argVal)) =>
        curEnv.put(argName, argVal)
      }

      val branchRes = typecheck(br.body, branchEnv)
      val expectTy = getType(m.motive, refinedEnv)
      check(branchRes, expectTy, refinedEnv)

    }

    evalTerm(m, env)
  }

  private def occurs(id: Long, v: Value, env: Env): Boolean = v match {
    case Var(_, vid, _) if vid == id                  => true
    case Var(_, vid, _) if env.varLinks.contains(vid) => occurs(id, env.getVarTop(vid), env)
    case VPi(piEnv, binders, out)                     =>
      // Check binder types first
      val inBinders = binders.toList.exists { b =>
        val tv = getType(b.ty, piEnv)
        occurs(id, tv, env)
      }
      if (inBinders) true
      else {
        // Check codomain under fresh assignments for binders
        val (_, extEnv) = assignFreshVars(VPi(piEnv, binders, out))
        val outV = getType(out, extEnv)
        occurs(id, outV, env)
      }
    case VApp(h, args, _) => occurs(id, h, env) || args.toList.exists(a => occurs(id, a, env))
    case _                => false
  }

  private def unify(v1: Value, v2: Value, env: Env): Env = {
    (v1, v2) match {
      case (VUniverse, VUniverse)                                                             => env
      case (VConst(n1, c1, _), VConst(n2, c2, _)) if n1 == n2 && c1 == c2                     => env
      case (p1 @ VPi(env1, bs1, out1), p2 @ VPi(env2, bs2, out2)) if bs1.length == bs2.length =>
        // Extensional unification for Pi types: unify binder types and codomain under shared fresh vars
        val (envAfterBinders, extEnv1, extEnv2) =
          bs1.toList.zip(bs2.toList).foldLeft((env, env1.newScope, env2.newScope)) {
            case ((curEnv, curEnv1, curEnv2), (b1, b2)) =>
              val t1 = getType(b1.ty, curEnv1)
              val t2 = getType(b2.ty, curEnv2)
              val nextEnv = unify(t1, t2, curEnv)
              val x = freshVar(b1.name, t1)
              (nextEnv, curEnv1.put(b1.name, x), curEnv2.put(b2.name, x))
          }
        val outT1 = getType(out1, extEnv1)
        val outT2 = getType(out2, extEnv2)
        unify(outT1, outT2, envAfterBinders)
      case (l1 @ VLam(_, t1 @ VPi(env1, bs1, out1), id1), l2 @ VLam(_, t2 @ VPi(env2, bs2, out2), id2))
          if bs1.length == bs2.length =>
        // Lambda equality: first try ids, then referential equality, then extensional fallback
        if (id1.isDefined && id1 == id2) env
        else if (l1.eq(l2)) env
        else {
          val (envAfterBinders, extEnv1, extEnv2) =
            bs1.toList.zip(bs2.toList).foldLeft((env, env1.newScope, env2.newScope)) {
              case ((curEnv, curEnv1, curEnv2), (b1, b2)) =>
                val ty1 = getType(b1.ty, curEnv1)
                val ty2 = getType(b2.ty, curEnv2)
                val nextEnv = unify(ty1, ty2, curEnv)
                val x = freshVar(b1.name, ty1)
                (nextEnv, curEnv1.put(b1.name, x), curEnv2.put(b2.name, x))
            }
          val args1: NEL[Term] = NEL.mk(bs1.toList.map(b => Term.Ident(b.name, Span(0, 0))))
          val args2: NEL[Term] = NEL.mk(bs2.toList.map(b => Term.Ident(b.name, Span(0, 0))))
          val app1 = typecheckApply(l1, args1, extEnv1)
          val app2 = typecheckApply(l2, args2, extEnv2)
          unify(app1, app2, envAfterBinders)
        }
      case (VApp(h1, args1, _), VApp(h2, args2, _)) if args1.length == args2.length =>
        val startCtx = unify(h1, h2, env)
        args1.zip(args2).foldLeft(startCtx) { case (newCtx, (arg1, arg2)) => unify(arg1, arg2, newCtx) }

      // Unify FreshVars through ctx. Basic idea: FreshVars can point at things through context
      // unify creates a ctx of pointers. We only create pointers from the top of the chain

      case (Var(_, id1, _), Var(_, id2, _)) if id1 == id2 => env

      // If we have FreshVars, resolve the tops of the chain
      case (Var(_, id, _), _) if env.varLinks.contains(id) => unify(env.getVarTop(id), v2, env)
      case (_, Var(_, id, _)) if env.varLinks.contains(id) => unify(v1, env.getVarTop(id), env)

      // Link two distinct, unlinked Vars: smaller id points to larger id
      case (v1 @ Var(_, id1, ty1), v2 @ Var(_, id2, ty2)) =>
        val (smallId, largeVar, smallTy, largeTy) =
          if (id1 < id2) (id1, v2: Value, ty1, ty2) else (id2, v1: Value, ty2, ty1)
        val env1 = unify(smallTy, largeTy, env)
        env1.addVarLink(smallId, largeVar)

      // Link unlinked Var (left) to a non-Var value
      case (v @ Var(_, id, ty), other) =>
        if (occurs(id, other, env))
          error(s"Occurs check failed: $id in $other")
        val env1 = unify(ty, other.tpe, env)
        env1.addVarLink(id, other)

      // Symmetric: link unlinked Var (right) to non-Var value
      case (other, v @ Var(_, id, ty)) =>
        if (occurs(id, other, env))
          error(s"Occurs check failed: $id in $other")
        val env1 = unify(ty, other.tpe, env)
        env1.addVarLink(id, other)

      case _ => error(s"Failed to unify $v1 and $v2")
    }
  }

  def getType(term: TypeTerm, env: Env): Value = {
    val res = typecheck(term, env)
    res.tpe match {
      case VUniverse => res
      case _         => error(s"$res is not a type")
    }
  }

  def typecheck(term: CoreAst.Term, env: Env): Value = {
    try {
      term match {
        case term: TypeTerm => typecheckTT(term, env)
        case t: Term.App =>
          val fn = typecheck(t.fn, env)
          typecheckApply(fn, t.args, env)
        case Term.Lam(ty, body, _) =>
          val vpi = VPi(env, ty.binders, ty.out)
          val (_, nextEnv) = assignFreshVars(vpi)

          val bodyV = typecheck(body, nextEnv)
          val resType = getType(vpi.out, nextEnv)

          check(bodyV, resType, nextEnv)
          VLam(body, vpi, None)

        case m: Term.Match => tyecheckMatch(m, env)
        case b: Term.Body  => typecheckBody(b, env)
      }
    } catch {
      case e: TypeErr => throw TypeErrWithSpan(e.message, term.span)
    }

  }

}
