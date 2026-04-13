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
        val base = eqStore.subst.get(varId) match {
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
      case v0: Blocked if eqStore.subst.contains(v0.blockerId) =>
        v0 match {
          case VBlockedApp(h, args, tpe, _) =>
            val h0 = resolveInEqStore(h)
            h0 match {
              case lam: VLam =>
                val res = lam.run(NEL.mk(args), eqStore)
                resolveInEqStore(res)
              case b: Blocker =>
                // Head is not reducible; remain blocked on this blocker
                VBlockedApp(b, args, tpe, b.blockerId)
              case other =>
                // Now that the head is resolved and not blocked, perform the application
                resolveInEqStore(evalApply(other, NEL.mk(args)))
            }
          case vm: VBlockedThunk => resolveInEqStore(vm.thunk(eqStore))
        }

      case l: Level if l.atoms.keySet.intersect(eqStore.subst.keySet).nonEmpty => normalizeLevel(l)

      case _ => v0
    }
  }

  private def getEnvWithArgs(fnTpe: VPi, args: NEL[Value])(implicit eqStore: EqStore) =
    BinderOps.instantiate(fnTpe.binders, fnTpe.env, args, eqStore)

  def evalPi(pi: Term.Pi, env: Env)(implicit eqStore: EqStore): VPi = {
    val captureNames = FreeNames
      .getFreeNames(pi, Set.empty)
      .toVector
      .filter(n => env.findLocal(n).isDefined)
      .sorted
    val captureVals = captureNames.map(n => env.findLocal(n).get)
    val id = ValueId.LocalId(pi.span.start, captureVals)

    val (vars, bodyEnv, _) = BinderOps.assignFreshVars(pi.binders, env, eqStore)
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
    case s: Term.TSelect =>
      val base = evalTypeTerm(s.base, env)
      evalSelect(base, s.field, env, s.span.start)
    case pi: Term.Pi => evalPi(pi, env)
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
                  case _                                         => VBlockedApp(fn0, vArgs.toList, b.tpe, b.blockerId)
                }
              case _ => res
            }
          case h: VConst => VApp(h, vArgs.toVector, pi.codomain(envWithArgs, eqStore))
          case h: ConstructorHead =>
            val resultTy = pi.codomain(envWithArgs, eqStore)
            val fields = vArgs.toVector.drop(h.numParams)
            VCtor(h, fields, resultTy)
          case b: Blocker => VBlockedApp(b, vArgs.toList, pi.codomain(envWithArgs, eqStore), b.blockerId)
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
      case Some(funcName) => ValueId.Const(funcName)
      case None =>
        val captureNames =
          FreeNames.getFreeNames(l, Set.empty).toVector.filter(n => env.findLocal(n).isDefined).sorted
        val captureVals = captureNames.map(n => env.findLocal(n).get)
        ValueId.LocalId(l.span.start, captureVals)

    }
    lazy val self: VLam = VLam(
      vpi,
      id,
      l.isStable,
      (args, eqStore) => {
        val bodyEnv = getEnvWithArgs(vpi, args)(eqStore)
        val recurEnv =
          l.name match {
            case Some(name) => bodyEnv.putGlobal(name, self)
            case None       => bodyEnv
          }
        val res = evalTerm(l.body, recurEnv)(eqStore)
        res match {
          case u: UpdatableType =>
            val tpe = vpi.codomain(bodyEnv, eqStore)
            u.withTpe(tpe)
          case _ => res
        }
      }
    )
    self
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
        case Term.Select(base, field, span) => evalSelect(evalTerm(base, env), field, env, span.start)
        case tt: TypeTerm                   => evalTypeTerm(tt, env)
        case Term.App(fn, args, _)          => evalApplyTerm(fn, args, env)
        case l: Term.Lam                    => evalLam(l, env)
        case m: Term.Match                  => evalMatch(m, env)
        case b: Term.Body                   => evalBody(b, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

  // Inline selection on values (term and type positions share logic)
  private def computeSelectResultTypeFrom(vType: Value, field: String, env: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap = NormalizerMap.empty
  ): Value = {
    val vt0 = resolveInEqStore(vType)
    val (indName, meta, typeArgs) = vt0 match {
      case VConst(n, Inductive(m), _)              => (n, m, Vector.empty[Value])
      case VApp(VConst(n, Inductive(m), _), as, _) => (n, m, as)
      case other                                   => throw NotAType(other)
    }

    // Only valid structs support selection
    if (!meta.isStruct) throw NotAStruct(indName)
    val ctorName = meta.constructorNames.head

    env.find(ctorName).getOrElse(throw NotFound(ctorName)) match {
      case ConstructorHead(_, numParams, _, ctorTy, isStruct) =>
        if (!isStruct) throw NotAStruct(indName)
        ctorTy match {
          case pi: VPi =>
            // 1) Bind inductive params to the vType args in the constructor Pi env
            val paramArgs = typeArgs.take(numParams)

            val envWithParams: Env =
              if (numParams == 0) pi.env
              else BinderOps.instantiate(pi.binders.take(numParams), pi.env, Util.NEL.mk(paramArgs), eqStore)

            // 2) Build the telescope up to and including the requested field with params in scope
            val allFieldBinders = pi.binders.toList.drop(numParams)
            val fieldIdx = allFieldBinders.indexWhere(_.name == field)
            if (fieldIdx < 0) throw NotFound(field)

            val fieldTelescope = allFieldBinders.take(fieldIdx + 1)
            val (_, telEnv, _) = BinderOps.assignFreshVars(fieldTelescope.toVector, envWithParams, eqStore)

            // Find field in the telescope env and return its type
            telEnv.find(field).get.tpe
          case _ => throw NotFound(field)
        }
      case _ => throw NotFound(ctorName)
    }
  }

  def evalSelect(v: Value, field: String, env: Env, locationId: Int)(implicit eqStore: EqStore): Value = {
    val v0 = resolveInEqStore(v)
    v0 match {
      case VCtor(head, fields, _) =>
        if (!head.isStruct) throw NotAStruct(head.name)

        head.tpe match {
          case pi: VPi =>
            val fieldBinders = pi.binders.toList.drop(head.numParams)
            val idx = fieldBinders.indexWhere(_.name == field)
            if (idx >= 0 && idx < fields.length && fieldBinders(idx).name != "_") fields(idx)
            else throw NotFound(field)
          case _ => throw NotFound(field)
        }

      case b: Blocker =>
        val resultTy = computeSelectResultTypeFrom(v0.tpe, field, env)
        val id = ValueId.LocalId(locationId, Vector(v0))
        VBlockedThunk(eqStore => evalSelect(v, field, env, locationId)(eqStore), id, resultTy, b.blockerId)
      case _ =>
        val resultTy = computeSelectResultTypeFrom(v0.tpe, field, env)
        val head = VConst(s"select.$field", Symbol, KernelObject)
        VApp(head, Vector(v), resultTy)
    }
  }

  private def evalMatch(m: Match, env: Env)(implicit eqStore: EqStore): Value = {
    def computeMatchCaptures(): Vector[Value] = {
      FreeNames
        .getFreeNames(m, Set.empty)
        .toVector
        .filter(n => env.findLocal(n).isDefined)
        .sorted
        .map(n => env.findLocal(n).get)
    }

    val scrut = resolveInEqStore(evalTerm(m.scrut, env))
    val withScrut = env.newScope.putLocal(m.scrutName, scrut)

    def mkStuckMatch(): Value = {
      val outType = evalTypeTerm(m.motive, withScrut)
      val head = VConst(s"match#${m.span.start}", Symbol, KernelObject)
      VApp(head, computeMatchCaptures(), outType)
    }

    def mkBlockedMatch(b: Blocker): Value = {
      val lamId = ValueId.LocalId(m.span.start, computeMatchCaptures())
      val outType = evalTypeTerm(m.motive, withScrut)
      VBlockedThunk(eqStore => evalMatch(m, env)(eqStore), lamId, outType, b.blockerId)
    }

    val (head, args) = scrut match {
      case VCtor(head, fields, _) => (head, fields)
      case b: Blocker             => return mkBlockedMatch(b)
      case _                      => return mkStuckMatch()
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
      val withTpe = (res, l.ty) match {
        case (u: UpdatableType, Some(ty)) =>
          u.withTpe(evalTypeTerm(ty, curEnv))
        case _ => res
      }
      curEnv.putLocal(l.name, withTpe)
    }
    evalTerm(body.res, newEnv)
  }

  case class Worlds(checkEnv: Env, runEnv: Env)

  def evalDecl(decl: Decl, worlds: Worlds): Worlds = {
    implicit val eqStore = EqStore.empty
    implicit val normalizers = NormalizerMap.empty

    decl match {
      case Decl.ConstDecl(unfoldStrategy, name, ty, body, _) =>
        val tyV = TypeChecker.getType(ty, worlds.checkEnv)
        val declConst = VConst(name, Symbol, tyV)

        val bodyV = TypeChecker.typecheck(body, worlds.checkEnv)

        TypeChecker.checkType(bodyV, tyV)

        val checkValue: Value = unfoldStrategy match {
          case Some(_) => bodyV
          case None    => declConst
        }
        val nextCheckEnv = worlds.checkEnv.putGlobal(name, checkValue)

        val runtimeBodyV = Interpreter.evalTerm(body, worlds.runEnv)
        val nextRunEnv = worlds.runEnv.putGlobal(name, runtimeBodyV)

        Worlds(nextCheckEnv, nextRunEnv)

      case d: Decl.InductiveDecl => InductiveChecks.evalInductiveDecl(d, worlds)

    }

  }

  def run(p: Program): Option[Value] = {
    val baseEnv =
      Env.empty
        .putGlobal("Type", VSort(Level.zero))
        .putGlobal("Normalizer", NormalizerType)
        .putGlobal("Level", LevelTpe)
        .putGlobal("Level::zero", Level.zero)
        .putGlobal("Level::one", Level(Map.empty, 1))
        .putGlobal("Prop", PropTpe)

    val builtinFuncs = List[(String, TypeTerm, (NEL[Value], EqStore) => Value)](
      (
        "add_normalizer",
        parseHeader("(A: Type)(zero: A)(add: A -> A -> A): Normalizer"),
        (args, _) => Normalizers.add_normalizer(args.toVector)
      ),
      (
        "Level::succ",
        parseHeader("(l: Level): Level"),
        (args, eqStore) => Value.Level.succ(getLevel(args.head)(eqStore))
      ),
      (
        "Level::max",
        parseHeader("(l1: Level)(l2: Level): Level"),
        (args, eqStore) => Value.Level.max(args.map(l => getLevel(l)(eqStore)).toVector)
      )
    )

    val env2 = builtinFuncs.foldLeft(baseEnv) { case (curEnv, (name, tpe, lam)) =>
      val tpeV = evalTypeTerm(tpe, curEnv)(EqStore.empty)
      tpeV match {
        case pi: VPi =>
          curEnv.putGlobal(name, VLam(pi, ValueId.Const(name), isStable = true, lam))
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
          ValueId.Const("Sort"),
          VSort(Level.zero)
        ),
        ValueId.Const("Sort"),
        true,
        (args, eqStore) => {
          val l = getLevel(args(0))(eqStore)
          VSort(l)
        }
      )
    )

    val worlds = p.decls.foldLeft(Worlds(nextEnv, nextEnv)) { case (curWorlds, decl) => evalDecl(decl, curWorlds) }
    p.body.map { b =>
      TypeChecker.typecheck(b, worlds.checkEnv)(EqStore.empty, NormalizerMap.empty)
      Interpreter.evalTerm(b, worlds.runEnv)(EqStore.empty)
    }
  }

  private def parseHeader(s: String): TypeTerm = {
    LanguageParser.parseFuncHeader(s) match {
      case Success(header, _, _) => Elaborator.getType(header)
      case err: Failure          => throw new RuntimeException(err.message)
    }
  }
}
