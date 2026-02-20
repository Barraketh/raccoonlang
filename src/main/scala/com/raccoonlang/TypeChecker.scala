package com.raccoonlang

import com.raccoonlang.CoreAst.Term.{Ident, Lam, Match}
import com.raccoonlang.CoreAst._
import com.raccoonlang.FreshVar.{assignFreshVars, freshVar}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Unify.unify
import com.raccoonlang.Util.NEL

import scala.annotation.tailrec
import scala.util.Try

object TypeChecker {

  private def defEq(value: Value, tyVal: Value, meta: MetaStore): MetaStore = unify(value.tpe, tyVal, meta)

  private def typecheckApply(fn: Value, args: NEL[Term], meta: MetaStore, argEnv: Env): (Value, MetaStore) = {
    val fn0 = whnf(fn, meta)
    val fnTy0 = whnf(fn0.tpe, meta)

    fnTy0 match {
      case VPi(env, binders, outTy, _) =>
        if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

        // Typecheck argument terms in argEnv
        val (vArgs, meta1) = args.foldLeft((Vector.empty[Value], meta)) { case ((acc, m), nextArg) =>
          val (v, m2) = typecheck(nextArg, m)(argEnv)
          (acc :+ v, m2)
        }

        // Typecheck args against binder types and extend pi env
        val (envWithArgs, meta2) =
          binders.toList.zip(vArgs).foldLeft((env.newScope, meta1)) { case ((curEnv, m), (binder, value)) =>
            val (argTy, m1) = getType(binder.ty, m)(curEnv)
            val m2 = defEq(value, argTy, m1)
            (curEnv.put(binder.name, value), m2)
          }

        // Since we've already typechecked everything we care about, now we can just evalTerm
        fn match {
          case VLam(body, _, _) => (evalTerm(body, meta2)(envWithArgs), meta2)
          case head: Head       => (VApp(head, NEL.mk(vArgs), evalTerm(outTy, meta2)(envWithArgs)), meta2)
          case _                => throw CannotApplyNonFunction(fnTy0)
        }
      case _ => throw CannotApplyNonFunction(fnTy0)
    }
  }

  private def typecheckApplyTerm(fn: Term, args: NEL[Term], meta: MetaStore)(implicit env: Env): (Value, MetaStore) = {
    val (vf, m1) = typecheck(fn, meta)
    typecheckApply(vf, args, m1, env)
  }

  // Check that all type terms typecheck under a fresh var assignment to binders
  private def typecheckPi(pi: Term.Pi, meta: MetaStore, env: Env): (VPi, MetaStore) = {
    val (finalMeta, bodyEnv) = pi.binders.foldLeft((meta, env.newScope)) { case ((curMeta, curEnv), b) =>
      val (tyV, nextMeta) = getType(b.ty, curMeta)(curEnv)
      (nextMeta, curEnv.put(b.name, freshVar(b.name, tyV)))
    }
    typecheckTT(pi.out, finalMeta)(bodyEnv)
    (evalPi(pi)(env), meta)
  }

  private def typecheckTT(term: TypeTerm, meta: MetaStore)(implicit env: Env): (Value, MetaStore) = term match {
    case t: Term.TApp => typecheckApplyTerm(t.fn, t.args, meta)
    case pi: Term.Pi  => typecheckPi(pi, meta, env)
    case ident: Ident => (evalTerm(ident, meta), meta)
  }

  private def typecheckBody(body: Term.Body, meta: MetaStore, env: Env): (Value, MetaStore) = {
    val (newEnv, newMeta) = body.lets.foldLeft((env, meta)) { case ((curEnv, curMeta), l) =>
      val (res, m1) = typecheck(l.value, curMeta)(curEnv)
      val m2 = l.ty
        .map { tyTerm =>
          val (tyV, m21) = getType(tyTerm, m1)(curEnv)
          defEq(res, tyV, m21)
        }
        .getOrElse(m1)
      (curEnv.put(l.name, res), m2)
    }
    typecheck(body.res, newMeta)(newEnv)
  }

  @tailrec
  private def peelHead(v: Value): Value = v match {
    case VApp(h, _, _) => peelHead(h)
    case other         => other
  }

  private def typecheckMatch(t: Match, meta: MetaStore, env: Env): (Value, MetaStore) = {
    val (scrut, m1) = typecheck(t.scrut, meta)(env)
    val withScrut = env.put(t.scrutName, scrut)

    val (inductiveName, inductiveCtors) = peelHead(scrut.tpe) match {
      case VConst(n, Inductive(names), _) => (n, names.toSet)
      case _                              => throw NonInductiveMatch(scrut.tpe)
    }

    def unifyScrutWithCtor(ctorName: String): (MetaStore, Vector[Value]) = {
      val ctorVal = env.find(ctorName).getOrElse(throw NotFound(ctorName))

      ctorVal match {
        case h @ VConst(_, ConstructorHead, ctorTy) =>
          val (freshArgs, ctorEnv) = ctorTy match {
            case pi: VPi => assignFreshVars(pi, m1)
            case _       => (Vector.empty[Value], env)
          }

          val ctorResTy: Value = ctorTy match {
            case VPi(_, _, out, _) =>
              evalTerm(out, m1)(ctorEnv) // Again, we've already typechecked out, so we can just eval it
            case otherTy: Value => otherTy
          }

          val appliedConstr =
            if (freshArgs.nonEmpty) VApp(h, NEL.mk(freshArgs), ctorResTy)
            else h

          (unify(scrut, appliedConstr, m1), freshArgs)
        case _ => throw UnknownConstructor(ctorName, inductiveName)
      }
    }

    // Check for duplicate constructors
    t.cases.groupBy(_.ctorName).find(_._2.length > 1).foreach { case (ctor, cases) =>
      throw DuplicateCase(ctor, Some(cases(1).span))
    }

    // Check exhaustivity. Each missing ctor must be unreachable - that is, must fail to unify with scrut
    // TODO: don't use exceptions
    val missing = inductiveCtors -- t.cases.map(_.ctorName)
    missing.foreach { ctorName =>
      Try(unifyScrutWithCtor(ctorName)) match {
        case util.Failure(_) =>
        case util.Success(_) => throw MissingCase(ctorName)
      }
    }

    // Check for unknown constructors
    t.cases.find(c => !inductiveCtors.contains(c.ctorName)).foreach { c =>
      throw UnknownConstructor(c.ctorName, inductiveName, Some(c.span))
    }

    t.cases.foreach { br =>
      try {
        val (branchMetas, freshArgs) =
          try {
            unifyScrutWithCtor(br.ctorName)
          } catch {
            case _: UnificationFailed => throw UnreachableCase(br.ctorName, Some(br.span))
          }

        if (br.argNames.length != freshArgs.length)
          throw ArityMismatch(freshArgs.length, br.argNames.length)

        val branchEnv = br.argNames.zip(freshArgs).foldLeft(withScrut.newScope) { case (curEnv, (argName, argVal)) =>
          curEnv.put(argName, argVal)
        }

        val (branchRes, m2) = typecheck(br.body, branchMetas)(branchEnv)
        val (expectTy, m3) = getType(t.motive, m2)(branchEnv)
        defEq(branchRes, expectTy, m3)
      } catch {
        case t: TypeError if t.span.isEmpty => throw TypeError.withSpan(t, br.span)
      }
    }

    (evalTerm(t, m1)(withScrut), m1)
  }

  def typecheckLam(l: Lam, meta: MetaStore, env: Env): (Value, MetaStore) = {
    val (vpi, m1) = typecheckPi(l.ty, meta, env)
    val (_, bodyEnv) = assignFreshVars(vpi, m1)

    val (bodyV, m2) = typecheck(l.body, m1)(bodyEnv)
    val resType = evalTerm(l.ty.out, m2)(bodyEnv)

    val m3 = defEq(bodyV, resType, m2)
    (VLam(l.body, vpi, None), m3)
  }

  def getType(term: TypeTerm, meta: MetaStore)(implicit env: Env): (Value, MetaStore) = {
    val res = typecheck(term, meta)
    res._1.tpe match {
      case VUniverse => res
      case _         => throw NotAType(res._1)
    }
  }

  def typecheck(term: CoreAst.Term, meta: MetaStore)(implicit env: Env): (Value, MetaStore) = {
    try {
      term match {
        case term: TypeTerm => typecheckTT(term, meta)
        case t: Term.App    => typecheckApplyTerm(t.fn, t.args, meta)
        case l: Term.Lam    => typecheckLam(l, meta, env)
        case m: Term.Match  => typecheckMatch(m, meta, env)
        case b: Term.Body   => typecheckBody(b, meta, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }

  }

}
