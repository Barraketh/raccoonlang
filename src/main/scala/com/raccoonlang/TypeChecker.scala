package com.raccoonlang

import com.raccoonlang.CoreAst.Term.{Ident, Lam, Match}
import com.raccoonlang.CoreAst._
import com.raccoonlang.FreshVar.{assignFreshVars, freshVar}
import com.raccoonlang.Interpreter._
import com.raccoonlang.Util.NEL

import scala.annotation.tailrec
import scala.util.Try

object TypeChecker {

  private def checkType(value: Value, tyVal: Value)(implicit meta: MetaCtx): Unit = meta.unify(value.tpe, tyVal)

  private def typecheckApply(fn: Value, args: NEL[Term], argEnv: Env)(implicit meta: MetaCtx): Value = {
    val fn0 = meta.whnf(fn)
    val fnTy0 = meta.whnf(fn0.tpe)

    fnTy0 match {
      case VPi(env, binders, outTy, _) =>
        if (binders.length != args.length) throw ArityMismatch(binders.length, args.length)

        // Typecheck argument terms in argEnv
        val vArgs = args.foldLeft(Vector.empty[Value]) { case (acc, nextArg) =>
          val v = typecheck(nextArg)(argEnv, meta)
          acc :+ v
        }

        // Typecheck args against binder types and extend pi env
        val envWithArgs =
          binders.toList.zip(vArgs).foldLeft(env.newScope) { case (curEnv, (binder, value)) =>
            val argTy = meta.eval(binder.ty)(curEnv)
            checkType(value, argTy)
            curEnv.putLocal(binder.name, value)
          }

        // Since we've already typechecked everything we care about, now we can just evalTerm
        fn0 match {
          case VLam(body, _, _) => meta.eval(body)(envWithArgs)
          case head: Head       => VApp(head, NEL.mk(vArgs), meta.eval(outTy)(envWithArgs))
          case _                => throw CannotApplyNonFunction(fnTy0)
        }
      case _ => throw CannotApplyNonFunction(fnTy0)
    }
  }

  private def typecheckApplyTerm(fn: Term, args: NEL[Term])(implicit env: Env, meta: MetaCtx): Value = {
    val vf = typecheck(fn)
    typecheckApply(vf, args, env)
  }

  // Check that all type terms typecheck under a fresh var assignment to binders
  private def typecheckPi(pi: Term.Pi, env: Env)(implicit meta: MetaCtx): VPi = {
    val bodyEnv = pi.binders.foldLeft(env.newScope) { case (curEnv, b) =>
      val tyV = getType(b.ty)(curEnv, meta)
      curEnv.putLocal(b.name, freshVar(b.name, tyV))
    }
    getType(pi.out)(bodyEnv, meta)
    evalPi(pi)(env)
  }

  private def typecheckTT(term: TypeTerm)(implicit env: Env, meta: MetaCtx): Value = term match {
    case t: Term.TApp => typecheckApplyTerm(t.fn, t.args)
    case pi: Term.Pi  => typecheckPi(pi, env)
    case ident: Ident => meta.eval(ident)
  }

  private def typecheckBody(body: Term.Body, env: Env)(implicit meta: MetaCtx): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = typecheck(l.value)(curEnv, meta)
      l.ty.foreach { tyTerm =>
        val tyV = getType(tyTerm)(curEnv, meta)
        checkType(res, tyV)
      }
      curEnv.putLocal(l.name, res)
    }
    typecheck(body.res)(newEnv, meta)
  }

  @tailrec
  private def peelHead(v: Value): Value = v match {
    case VApp(h, _, _) => peelHead(h)
    case other         => other
  }

  private def unifyScrutWithCtor(
      scrut: Value,
      ctorName: String,
      inductiveName: String,
      env: Env,
      meta: MetaCtx
  ): Vector[Value] = {
    val ctorVal = env.find(ctorName).getOrElse(throw NotFound(ctorName))

    ctorVal match {
      case h @ VConst(_, ConstructorHead, ctorTy) =>
        val (freshArgs, ctorEnv) = ctorTy match {
          case pi: VPi => assignFreshVars(pi, meta.meta)
          case _       => (Vector.empty[Value], env)
        }

        val ctorResTy: Value = ctorTy match {
          case VPi(_, _, out, _) =>
            meta.eval(out)(ctorEnv) // Again, we've already typechecked out, so we can just eval it
          case otherTy: Value => otherTy
        }

        val appliedConstr =
          if (freshArgs.nonEmpty) VApp(h, NEL.mk(freshArgs), ctorResTy)
          else h

        meta.unify(scrut, appliedConstr)
        freshArgs
      case _ => throw UnknownConstructor(ctorName, inductiveName)
    }
  }

  private def typecheckMatch(t: Match, env: Env)(implicit meta: MetaCtx): Value = {
    val scrut = typecheck(t.scrut)(env, meta)

    val (inductiveName, inductiveCtors) = peelHead(meta.whnf(scrut.tpe)) match {
      case VConst(n, Inductive(names), _) => (n, names.toSet)
      case _                              => throw NonInductiveMatch(scrut.tpe)
    }

    // Check for duplicate constructors
    t.cases.groupBy(_.ctorName).find(_._2.length > 1).foreach { case (ctor, cases) =>
      throw DuplicateCase(ctor, Some(cases(1).span))
    }

    // Check exhaustivity. Each missing ctor must be unreachable - that is, must fail to unify with scrut
    // TODO: don't use exceptions
    val missing = inductiveCtors -- t.cases.map(_.ctorName)
    missing.foreach { ctorName =>
      Try(unifyScrutWithCtor(scrut, ctorName, inductiveName, env, meta.fork())) match {
        case util.Failure(_) =>
        case util.Success(_) => throw MissingCase(ctorName)
      }
    }

    // Check for unknown constructors
    t.cases.find(c => !inductiveCtors.contains(c.ctorName)).foreach { c =>
      throw UnknownConstructor(c.ctorName, inductiveName, Some(c.span))
    }

    val withScrut = env.newScope.putLocal(t.scrutName, scrut)
    t.cases.foreach { br =>
      try {
        val branchCtx = meta.fork()
        val freshArgs =
          try {
            unifyScrutWithCtor(scrut, br.ctorName, inductiveName, env, branchCtx)
          } catch {
            case _: UnificationFailed => throw UnreachableCase(br.ctorName, Some(br.span))
          }

        if (br.argNames.length != freshArgs.length)
          throw ArityMismatch(freshArgs.length, br.argNames.length)

        val branchEnv = br.argNames.zip(freshArgs).foldLeft(withScrut.newScope) { case (curEnv, (argName, argVal)) =>
          curEnv.putLocal(argName, argVal)
        }

        val branchRes = typecheck(br.body)(branchEnv, branchCtx)
        val expectTy = getType(t.motive)(branchEnv, branchCtx)
        checkType(branchRes, expectTy)(branchCtx)
      } catch {
        case t: TypeError if t.span.isEmpty => throw TypeError.withSpan(t, br.span)
      }
    }

    meta.eval(t)(env)
  }

  def typecheckLam(l: Lam, env: Env)(implicit ctx: MetaCtx): Value = {
    val vpi = typecheckPi(l.ty, env)
    val (_, bodyEnv) = assignFreshVars(vpi, ctx.meta)

    val bodyV = typecheck(l.body)(bodyEnv, ctx)
    val resType = ctx.eval(l.ty.out)(bodyEnv)

    checkType(bodyV, resType)
    Interpreter.evalLam(l, vpi)(env)
  }

  def getType(term: TypeTerm)(implicit env: Env, ctx: MetaCtx): Value = {
    val res = typecheck(term)

    ctx.whnf(res.tpe) match {
      case VUniverse => res
      case _         => throw NotAType(res)
    }
  }

  def typecheck(term: CoreAst.Term)(implicit env: Env, meta: MetaCtx): Value = {
    try {
      term match {
        case term: TypeTerm => typecheckTT(term)
        case t: Term.App    => typecheckApplyTerm(t.fn, t.args)
        case l: Term.Lam    => typecheckLam(l, env)
        case m: Term.Match  => typecheckMatch(m, env)
        case b: Term.Body   => typecheckBody(b, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }

  }

  /** A way to store the current metastore and make sure that it gets updated with the latest version after every
    * modification. Calls to 'unify' modify the underlying metaStore.
    *
    * This is essentially an alternative to using a state monad and having every function that modifies the metastore
    * return the new metastore. Using the state monad makes the code a bit too unwieldy, and just threading the
    * metastore through is a bit too error-prone.
    *
    * This really only works because there is exactly one place where fork, and that is the pattern match, so we don't
    * really need to reason about the mutable state - updating the meta by default is the correct behavior
    */
  final class MetaCtx(var meta: Interpreter.MetaStore) {
    def whnf(v: Interpreter.Value): Interpreter.Value =
      Interpreter.whnf(v, meta)

    def eval(t: CoreAst.Term)(implicit env: Interpreter.Env): Interpreter.Value =
      Interpreter.evalTerm(t, meta)

    def unify(a: Interpreter.Value, b: Interpreter.Value): Unit =
      meta = Unify.unify(a, b, meta)

    /** Snapshot-style fork, useful for branch-local constraints (matches). */
    def fork(): MetaCtx = new MetaCtx(meta)
  }

  object MetaCtx {
    def empty = new MetaCtx(MetaStore.empty)
  }

}
