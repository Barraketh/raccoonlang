package com.raccoonlang

import com.raccoonlang.CoreAst.Term.Match
import com.raccoonlang.CoreAst._
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

import scala.collection.immutable.BitSet

object Interpreter {
  private def normalizeLevel(l: Level)(implicit eqStore: EqStore): Level = {
    val pieces = Vector(Level(Map.empty, l.c)) ++
      l.atoms.toVector.map { case (varId, k) =>
        val base = eqStore.links.get(varId) match {
          case Some(sol) =>
            eqStore.force(sol) match {
              case next: Level   => normalizeLevel(next)
              case Var(_, id, _) => Level.mk(id)
              case other         => throw NotALevel(other)
            }
          case None => Level.mk(varId)
        }
        Level.addOffset(base, k)
      }
    Level.max(pieces)
  }

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
                // Head is not reducible; remain blocked on this blocker
                VBlockedApp(b, args, tpe, b.blockerId)
              case other =>
                // Now that the head is resolved and not blocked, perform the application
                resolveInEqStore(evalApply(other, args))
            }
          case vm: BlockedMatch =>
            val scrut0 = resolveInEqStore(vm.scrut)
            scrut0 match {
              case b: Blocker => vm.copy(scrut = scrut0, blockerId = b.blockerId)
              case _          => resolveInEqStore(evalMatchBody(vm.term, scrut0, vm.env))
            }
        }

      case l: Level if l.atoms.keySet.intersect(eqStore.links.keySet).nonEmpty => normalizeLevel(l)

      case _ => v0
    }
  }

  private def getEnvWithArgs(fnTpe: VPi, args: NEL[Value])(implicit eqStore: EqStore) = {
    if (fnTpe.binders.length != args.length)
      throw ArityMismatch(fnTpe.binders.length, args.length)

    fnTpe.binders.toList.zip(args.toList).foldLeft(fnTpe.env.newScope) { case (curEnv, (binder, value)) =>
      val openedEnv = TypePatternOps.bindValue(curEnv, binder.ty, value.tpe, eqStore)
      openedEnv.putLocal(binder.name, value)
    }
  }

  def evalPi(pi: Term.Pi, env: Env)(implicit eqStore: EqStore): VPi = {
    val captureNames = FreeNames
      .getFreeNames(pi, Set.empty)
      .toVector
      .filter(n => env.findLocal(n).isDefined)
      .sorted
    val captureVals = captureNames.map(n => env.findLocal(n).get)
    val id = LamId.LocalId(pi.span.start, captureVals)

    val (vars, bodyEnv, _) = FreshVar.assignFreshVars(pi.binders, env, eqStore)
    val outType = evalTypeTerm(pi.out, bodyEnv)

    // Determine classifier for Pi: Prop if codomain is Prop, otherwise predicative max

    val piClassifier: Universe = TypeChecker.getUniverse(outType) match {
      case PropTpe => PropTpe
      case VSort(outLevel) =>
        val domLevels: Vector[Level] = vars
          .map(v => TypeChecker.getUniverse(v.tpe))
          .collect { case VSort(level) => level }

        VSort(Level.max(domLevels :+ outLevel))
    }

    VPi(
      env,
      pi.binders,
      codomain = (env, eqStore) => evalTypeTerm(pi.out, env)(eqStore),
      Some(pi.out),
      FreeNames.getDeps(pi, env, Set.empty),
      id,
      piClassifier
    )
  }

  private def evalTApp(app: Term.TApp, env: Env)(implicit meta: EqStore): Value = {
    val fn = evalTypeTerm(app.fn, env)
    val args = app.args.map(arg => evalTypeTerm(arg, env))
    evalApply(fn, args)
  }

  // Evaluate a type-position expression without enforcing it is a type yet
  def evalTypeTerm(tt: TypeTerm, env: Env)(implicit meta: EqStore): Value = tt match {
    case i: Term.Ident => evalIdent(i, env)
    case a: Term.TApp  => evalTApp(a, env)
    case pi: Term.Pi   => evalPi(pi, env)
  }

  private def evalIdent(i: Term.Ident, env: Env): Value = {
    val res = env.find(i.name).getOrElse {
      throw TypeError.withSpan(NotFound(i.name), i.span)
    }
    res match {
      case h: ConstructorHead if h.totalArity == 0 => VCtor(h, Vector.empty, h.tpe)
      case _                                       => res
    }
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
          case h: VConst => VApp(h, vArgs, pi.codomain(envWithArgs, eqStore))
          case h: ConstructorHead =>
            val resultTy = pi.codomain(envWithArgs, eqStore)
            val fields = vArgs.toVector.drop(h.numParams)
            VCtor(h, fields, resultTy)
          case b: Blocker => VBlockedApp(b, vArgs, pi.codomain(envWithArgs, eqStore), b.blockerId)
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
        val bodyEnv = getEnvWithArgs(vpi, args)(eqStore)
        evalTerm(l.body, bodyEnv)(eqStore)
      }
    )
  }

  private def evalLam(l: Term.Lam, env: Env)(implicit eqStore: EqStore): VLam = {
    val vpi = evalPi(l.ty, env)
    evalLam(l, vpi, env)
  }

  def getLevel(v: Value)(implicit eqStore: EqStore): Level = {
    resolveInEqStore(v) match {
      case l: Level => l
      case v: Var   => Level.mk(v.id)
      case v        => throw NotALevel(v)
    }
  }

  def evalTerm(term: Term, env: Env)(implicit eqStore: EqStore): Value = {
    try {
      term match {
        case tt: TypeTerm          => evalTypeTerm(tt, env)
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
      // Get all the free locals referenced in the body or the motive - we will use them as the key, just like VLam
      // We can treat scrutName as bound, since we are including it in StuckMatch and will unify it separately
      val bodyFree = m.cases
        .foldLeft(Set.empty[String]) { case (curNames, c) =>
          val nextNames = FreeNames.getFreeNames(c.body, bound = (c.argNames :+ m.scrutName).toSet)
          curNames.union(nextNames)
        }
      val motiveFree = FreeNames.getFreeNames(m.motive, Set(m.scrutName))
      val freeNames = bodyFree
        .union(motiveFree)
        .toVector
        .filter(n => withScrut.findLocal(n).isDefined)
        .sorted
      val captures = freeNames.map(n => withScrut.findLocal(n).get)
      LamId.LocalId(m.span.start, captures)
    }

    lazy val outType = evalTypeTerm(m.motive, withScrut)

    val (head, args) = scrut match {
      case VCtor(head, fields, _) => (head, fields)
      case b: Blocker             => return BlockedMatch(stuckMatchId, m, scrut, withScrut, outType, b.blockerId)
      case _                      => return StuckMatch(stuckMatchId, scrut, outType)
    }

    val ctorName = head.name
    val branch =
      m.cases.find(c => c.ctorName == ctorName).getOrElse(throw UnknownConstructor(ctorName, "", Some(m.span)))
    if (args.length != branch.argNames.length)
      throw ArityMismatch(branch.argNames.length, args.length, Some(branch.span))
    val newEnv = args.zip(branch.argNames).foldLeft(withScrut.newScope) { case (curEnv, (argV, argName)) =>
      curEnv.putLocal(argName, argV)
    }
    evalTerm(branch.body, newEnv)
  }

  def evalBody(body: Term.Body, env: Env)(implicit eqStore: EqStore): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      curEnv.putLocal(l.name, res)
    }
    evalTerm(body.res, newEnv)
  }

  def evalDecl(decl: Decl, env: Env): Env = {
    implicit val eqStore = EqStore.empty
    implicit val normalizers = NormalizerMap.empty

    decl match {
      case Decl.ConstDecl(unfoldStrategy, name, ty, body, _) =>
        val tyV = TypeChecker.getType(ty, env)
        val declConst = VConst(name, Symbol, tyV)

        // Allow recursive references by pre-binding a symbolic self during body checking
        val bodyV = TypeChecker.typecheck(body, env.putGlobal(name, declConst))

        TypeChecker.checkType(bodyV, tyV)

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

      case d: Decl.InductiveDecl => InductiveChecks.evalInductiveDecl(d, env)

    }

  }

  def run(p: Program): Option[Value] = {
    val baseEnv =
      Env.empty
        .putGlobal("Type", VSort(Level.zero))
        .putGlobal("Normalizer", NormalizerType)
        .putGlobal("Level", LevelTpe)
        .putGlobal("Level.zero", Level.zero)
        .putGlobal("Level.one", Level(Map.empty, 1))
        .putGlobal("Prop", PropTpe)

    val builtinFuncs = List[(String, TypeTerm, (NEL[Value], EqStore) => Value)](
      (
        "add_normalizer",
        parseHeader("(A: Type)(zero: A)(add: A -> A -> A): Normalizer"),
        (args, _) => Normalizers.add_normalizer(args.toVector)
      ),
      (
        "Level.succ",
        parseHeader("(l: Level): Level"),
        (args, eqStore) => Value.Level.succ(getLevel(args.head)(eqStore))
      ),
      (
        "Level.max",
        parseHeader("(l1: Level)(l2: Level): Level"),
        (args, eqStore) => Value.Level.max(args.map(l => getLevel(l)(eqStore)).toVector)
      )
    )

    val env2 = builtinFuncs.foldLeft(baseEnv) { case (curEnv, (name, tpe, lam)) =>
      val tpeV = evalTypeTerm(tpe, curEnv)(EqStore.empty)
      tpeV match {
        case pi: VPi =>
          curEnv.putGlobal(name, VLam(pi, LamId.Const(name), isStable = true, lam))
        case _ => curEnv
      }
    }

    val nextEnv = env2.putGlobal(
      "Sort",
      VLam(
        VPi(
          env2,
          NEL.one(Binder("l", CoreAst.Term.Ident("Level", Span(0, 0)), Span(0, 0))),
          (env, eqStore) => {
            val l = getLevel(env.findLocal("l").get)(eqStore)
            VSort(Level.succ(l))
          },
          None,
          BitSet.empty,
          LamId.Const("Sort"),
          VSort(Level.zero)
        ),
        LamId.Const("Sort"),
        true,
        (args, eqStore) => {
          val l = getLevel(args(0))(eqStore)
          VSort(l)
        }
      )
    )

    val env = p.decls.foldLeft(nextEnv) { case (env, decl) => evalDecl(decl, env) }
    p.body.map(b => TypeChecker.typecheck(b, env)(EqStore.empty, NormalizerMap.empty))
  }

  private def parseHeader(s: String): TypeTerm = {
    LanguageParser.parseFuncHeader(s) match {
      case Success(header, _, _) => Elaborator.getType(header)
      case err: Failure          => throw new RuntimeException(err.message)
    }
  }
}
