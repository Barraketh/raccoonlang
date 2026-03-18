package com.raccoonlang

import com.raccoonlang.CoreAst.Term.Match
import com.raccoonlang.CoreAst._
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

object Interpreter {
  def resolveInEqStore(v: Value)(implicit eqStore: EqStore): Value = {
    val v0 = eqStore.force(v)
    v0 match {
      case v0: Blocked if eqStore.links.contains(v0.blockerId) =>
        v0 match {
          case VBlockedApp(h, args, tpe, _) =>
            val h0 = resolveInEqStore(h)
            h0 match {
              case lam: VLam =>
                val res = lam.run(args, eqStore)
                resolveInEqStore(res)
              case b: Blocker =>
                // Head is not reducible
                VBlockedApp(b, args, tpe, b.blockerId)
            }
          case vm: BlockedMatch =>
            val scrut0 = resolveInEqStore(vm.scrut)
            val head = scrut0 match {
              case VApp(h, _, _) => h
              case c: VConst     => c
              case b: Blocker    => return vm.copy(scrut = scrut0, blockerId = b.blockerId)
            }

            head match {
              case VConst(_, `ConstructorHead`, _) => resolveInEqStore(evalMatchBody(vm.term, scrut0, vm.env))
            }
        }

      case _ => v0
    }
  }

  private def getEnvWithArgs(fnTpe: VPi, args: NEL[Value]): Env = {
    if (fnTpe.binders.length != args.length) throw ArityMismatch(fnTpe.binders.length, args.length)

    fnTpe.binders.map(_.name).zip(args).foldLeft(fnTpe.env.newScope) { case (curEnv, (name, value)) =>
      curEnv.putLocal(name, value)
    }
  }

  def evalPi(pi: Term.Pi, env: Env): VPi = {
    val captureNames = FreeNames
      .getFreeNames(pi, Set.empty)
      .toVector
      .filter(n => env.findLocal(n).isDefined)
      .sorted
    val captureVals = captureNames.map(n => env.findLocal(n).get)
    val id = LamId.LocalId(pi.span.start, captureVals)
    VPi(env, pi.binders, pi.out, FreeNames.getDeps(pi, env, Set.empty), id)
  }

  // Evaluate a type-position expression without enforcing it is a type yet
  private def evalTT(tt: TypeTerm, env: Env)(implicit meta: EqStore): Value = tt match {
    case Term.Ident(name, sp)   => env.find(name).getOrElse { throw TypeError.withSpan(NotFound(name), sp) }
    case Term.TApp(fn, args, _) => evalApplyTerm(fn, args, env)
    case pi: Term.Pi            => evalPi(pi, env)
  }

  def evalApply(fn: Value, vArgs: NEL[Value])(implicit eqStore: EqStore): Value = {
    val fn0 = resolveInEqStore(fn)
    val tpe0 = resolveInEqStore(fn0.tpe)

    tpe0 match {
      case pi: VPi =>
        val envWithArgs: Env = getEnvWithArgs(pi, vArgs)
        fn0 match {
          case VLam(_, _, isStable, run) =>
            val res = run(vArgs, eqStore)
            (isStable, res) match {
              case (true, b: Blocked) =>
                b match {
                  case VBlockedApp(VLam(_, _, true, _), _, _, _) => res
                  case _                                         => VBlockedApp(fn0, vArgs, b.tpe, b.blockerId)
                }
              case _ => res
            }
          case h: VConst  => VApp(h, vArgs, evalTT(pi.out, envWithArgs))
          case b: Blocker => VBlockedApp(b, vArgs, evalTT(pi.out, envWithArgs), b.blockerId)
          case _          => throw CannotApplyNonFunction(fn)
        }
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }
  }

  private def evalApplyTerm(fn: Term, args: NEL[Term], env: Env)(implicit eqStore: EqStore): Value = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    evalApply(vf, vArgs)
  }

  def evalLam(l: Term.Lam, vpi: VPi, env: Env): VLam = {
    val id = l.name match {
      case Some(funcName) => LamId.Const(funcName)
      case None =>
        val captureNames =
          FreeNames.getFreeNames(l, Set.empty).toVector.filter(n => env.findLocal(n).isDefined).sorted
        val captureVals = captureNames.map(n => env.findLocal(n).get)
        LamId.LocalId(l.span.start, captureVals)

    }
    VLam(
      vpi,
      id,
      l.isStable,
      (args, eqStore) => {
        val bodyEnv = getEnvWithArgs(vpi, args)
        evalTerm(l.body, bodyEnv)(eqStore)
      }
    )
  }

  private def evalLam(l: Term.Lam, env: Env): VLam = {
    val vpi = evalPi(l.ty, env)
    evalLam(l, vpi, env)
  }

  def evalTerm(term: Term, env: Env)(implicit eqStore: EqStore): Value = {
    try {
      term match {
        case tt: TypeTerm          => evalTT(tt, env)
        case Term.App(fn, args, _) => evalApplyTerm(fn, args, env)
        case l: Term.Lam           => evalLam(l, env)
        case m: Term.Match         => evalMatch(m, env)
        case b: Term.Body          => evalBody(b, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

  private def evalMatch(m: Match, env: Env)(implicit eqStore: EqStore): Value = {
    val scrut = resolveInEqStore(evalTerm(m.scrut, env))
    evalMatchBody(m, scrut, env)
  }

  private def evalMatchBody(m: Match, scrut: Value, env: Env)(implicit eqStore: EqStore): Value = {
    val withScrut = env.newScope.putLocal(m.scrutName, scrut)

    lazy val stuckMatchId = {
      // Get all the free locals referenced in the body of the match - we will use them as the key, just like VLam
      // We can treat scrutName as bound, since we are including it in StuckMatch and will unify it separately
      val freeNames = m.cases
        .foldLeft(Set.empty[String]) { case (curNames, c) =>
          val nextNames = FreeNames.getFreeNames(c.body, bound = (c.argNames :+ m.scrutName).toSet)
          curNames.union(nextNames)
        }
        .toVector
        .filter(n => withScrut.findLocal(n).isDefined)
        .sorted
      val captures = freeNames.map(n => withScrut.findLocal(n).get)
      LamId.LocalId(m.span.start, captures)
    }

    lazy val outType = evalTerm(m.motive, withScrut)

    val (head, args) = scrut match {
      case VApp(head, args, _) => (head, args.toList)
      case c: VConst           => (c, Nil)
      case b: Blocker          => return BlockedMatch(stuckMatchId, m, scrut, withScrut, outType, b.blockerId)
    }

    head match {
      case VConst(ctorName, `ConstructorHead`, _) =>
        val branch =
          m.cases.find(c => c.ctorName == ctorName).getOrElse(throw UnknownConstructor(ctorName, "", Some(m.span)))
        if (args.length != branch.argNames.length)
          throw ArityMismatch(branch.argNames.length, args.length, Some(branch.span))
        val newEnv = args.zip(branch.argNames).foldLeft(withScrut.newScope) { case (curEnv, (argV, argName)) =>
          curEnv.putLocal(argName, argV)
        }
        evalTerm(branch.body, newEnv)
      case _ => StuckMatch(stuckMatchId, scrut, outType)
    }
  }

  def evalBody(body: Term.Body, env: Env)(implicit eqStore: EqStore): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      curEnv.putLocal(l.name, res)
    }
    evalTerm(body.res, newEnv)
  }

  private def familyArity(inductiveTy: Value): Int = inductiveTy match {
    case pi: VPi => pi.binders.length
    case _       => 0
  }

  private def evalCtorResultType(ctorTy: Value)(implicit eqStore: EqStore): Value = ctorTy match {
    case pi: VPi =>
      // Instantiate constructor binders with fresh locals so we can evaluate the result type
      // under arbitrary arguments. We are *not* unifying here.
      val (_, ctorEnv) = FreshVar.assignFreshVars(pi, eqStore)
      evalTerm(pi.out, ctorEnv)
    case other =>
      other
  }

  private def decomposeCtorResult(v: Value)(implicit eqStore: EqStore): (Value, Vector[Value]) = {
    resolveInEqStore(v) match {
      case h: VConst        => (h, Vector.empty)
      case VApp(h, args, _) => (h, args.toVector)
      case other            => (other, Vector.empty)
    }
  }

  private def checkCtorReturnsInductive(
      ctor: Constructor,
      ctorTy: Value,
      inductiveHead: VConst,
      inductiveArity: Int
  )(implicit eqStore: EqStore, normalizers: NormalizerMap): Unit = {
    val ctorResTy = evalCtorResultType(ctorTy)
    val (head, args) = decomposeCtorResult(ctorResTy)

    // Result must reduce to the inductive family head
    if (!TypeChecker.defEq(head, inductiveHead))
      throw InvalidConstructorResult(
        ctor = ctor.name,
        inductive = inductiveHead.name,
        got = ctorResTy,
        expectedArity = inductiveArity,
        gotArity = args.length,
        span = Some(ctor.span)
      )

    // For now, since you are not distinguishing parameters vs indices,
    // require the constructor result to apply the family to *all* family args.
    if (args.length != inductiveArity)
      throw InvalidConstructorResult(
        ctor = ctor.name,
        inductive = inductiveHead.name,
        got = ctorResTy,
        expectedArity = inductiveArity,
        gotArity = args.length,
        span = Some(ctor.span)
      )
  }

  private def evalInductiveDecl(decl: Decl.InductiveDecl, env: Env): Env = {
    implicit val eqStore: EqStore = EqStore.empty
    implicit val normalizers: NormalizerMap = NormalizerMap.empty

    val inductiveType = TypeChecker.getType(decl.ty, env)
    val inductiveHead = VConst(decl.name, Inductive(decl.ctors.map(_.name)), inductiveType)
    val inductiveArity = familyArity(inductiveType)

    // Constructors should be checked in an environment where the inductive itself is available,
    // but not where previous constructors are available.
    val envWithInductive = env.putGlobal(decl.name, inductiveHead)

    decl.ctors.foreach { ctor =>
      val ctorTy = TypeChecker.getType(ctor.ty, envWithInductive)
      checkCtorReturnsInductive(ctor, ctorTy, inductiveHead, inductiveArity)
    }

    // Once all constructors are validated, add them to the final environment.
    decl.ctors.foldLeft(envWithInductive) { case (curEnv, ctor) =>
      val ctorTy = TypeChecker.getType(ctor.ty, envWithInductive)
      curEnv.putGlobal(ctor.name, VConst(ctor.name, ConstructorHead, ctorTy))
    }
  }

  private def evalDecl(decl: Decl, env: Env): Env = {
    implicit val eqStore = EqStore.empty
    implicit val normalizers = NormalizerMap.empty

    decl match {
      case Decl.ConstDecl(unfoldStrategy, name, ty, body, _) =>
        val tyV = TypeChecker.getType(ty, env)
        val declConst = VConst(name, Symbol, tyV)

        // Allow recursive references by pre-binding a symbolic self during body checking
        val bodyV = TypeChecker.typecheck(body, env.putGlobal(name, declConst))
        val value: Value = unfoldStrategy match {
          case Some(_) => bodyV
          case None    => declConst
        }
        val nextEnv = env.putGlobal(name, value)

        value match {
          case VLam(tpe, _, _, _) => tpe.env = nextEnv
          case _                  =>
        }

        nextEnv

      case d: Decl.InductiveDecl => evalInductiveDecl(d, env)

    }

  }

  def run(p: Program, builtIn: List[(String, TypeTerm, (NEL[Value], EqStore) => Value)] = List.empty): Value = {
    val baseEnv =
      Env.empty
        .putGlobal("Type", VUniverse)
        .putGlobal("Normalizer", NormalizerType)

    val nextEnv = builtIn.foldLeft(baseEnv) { case (curEnv, (name, tpe, lam)) =>
      val tpeV = evalTT(tpe, baseEnv)(EqStore.empty)
      tpeV match {
        case pi: VPi =>
          curEnv.putGlobal(name, VLam(pi, LamId.Const(name), isStable = false, lam))
      }
    }

    val env = p.decls.foldLeft(nextEnv) { case (env, decl) => evalDecl(decl, env) }
    TypeChecker.typecheck(p.body, env)(EqStore.empty, NormalizerMap.empty)
  }
}
