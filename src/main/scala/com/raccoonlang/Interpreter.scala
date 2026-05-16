package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program}
import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.{BinderOps, ConstructorOps, TypePatternOps}

/**
 * Interpreter is responsible for evaluating ElabAst -> Value It also contains resolveInEqStore, which continues
 * evaluation of blocked Values once unification has solved the blocker.
 *
 * Interpreter invariant:
 *
 * Every public evaluator returns a value in EqStore-WHNF relative to the EqStore passed to that evaluator.
 *
 * EqStore-WHNF means:
 *   - the root is not a Var solved by eqStore
 *   - the root is not a blocked computation whose blocker is solved by eqStore
 *   - the root Level has been normalized with respect to solved level atoms
 *
 * This is a root/view invariant only. It does not recursively materialize nested fields, arguments, closure
 * environments, lambda captures, or result types.
 */
object Interpreter {
  private def normalizeLevel(l: Level)(implicit eqStore: EqStore): Level = {
    val pieces = Vector(Level.const(l.c)) ++
      l.atoms.toVector.map { case (atom, k) =>
        val base = eqStore.subst.get(atom) match {
          case Some(sol) =>
            eqStore.force(sol) match {
              case next: Level   => normalizeLevel(next)
              case Var(_, id, _) => Level.mk(id)
              case other         => throw NotALevel(other)
            }
          case None => Level.mk(atom)
        }
        Level.addOffset(base, k)
      }
    Level.max(pieces)
  }

  /**
   * Continues the reduction of v if v is blocked by a variable that's been solved in EqStore The default call (if v
   * cannot be further reduced) should be quite fast, so we can call it defensively (don't need to worry too much about
   * the performance impact of calling it too often).
   */
  private def resolve(v: Value)(implicit eqStore: EqStore): Value = {
    val v0 = eqStore.force(v)
    v0 match {
      case v0: Blocked if eqStore.subst.contains(v0.blockerId) =>
        v0 match {
          case VBlockedApp(h, args, tpe, _) =>
            val h0 = resolve(h)
            h0 match {
              case lam: VLam =>
                val res = runLam(lam, args)
                resolve(res)
              case b: Blocker =>
                VBlockedApp(b, args, tpe, b.blockerId)
              case other =>
                resolve(evalApply(other, args))
            }
          case vm: VBlockedThunk => resolve(forceThunk(vm))
        }

      case l: Level if l.atoms.keySet.intersect(eqStore.subst.keySet).nonEmpty => normalizeLevel(l)

      case _ => v0
    }
  }

  def resolveInEqStore(v: Value)(implicit eqStore: EqStore): ResolvedValue = ResolvedValue(resolve(v))

  private def getEnvWithArgs(fnTpe: VPi, baseEnv: RuntimeEnv, args: Vector[Value])(implicit
      eqStore: EqStore
  ): RuntimeEnv =
    BinderOps.instantiateFull(fnTpe.binders, baseEnv, args)

  def evalPi[E <: EnvLike[E]](pi: ETerm.Pi, env: E, vBinders: Vector[VBinder]): VPi = {
    val capturedIndexes = CapturedIndexes.getCapturedIndexes(pi, env)
    val captureVals = env.getLocalsByIndexes(capturedIndexes)
    val id = ValueId.LocalId(pi.span.nodeId, captureVals)
    val closedEnv = env.closeForEval(Some(capturedIndexes))

    val synDeps = DepSet.newBuilder
    captureVals.foreach { v =>
      synDeps.unionInPlace(v.synDeps)
    }

    VPi(
      closedEnv,
      vBinders,
      codomain = (env, eqStore) => evalTypeTerm(pi.out, env)(eqStore),
      synDeps.result(),
      id,
      pi.classifier
    )
  }

  private def evalPi[E <: EnvLike[E]](pi: ETerm.Pi, env: E): VPi =
    evalPi(pi, env, pi.binders.map(TypePatternOps.toVBinder))

  def evalTypeTerm[E <: EnvLike[E]](tt: ElabAst.TypeTerm, env: E)(implicit meta: EqStore): Value = tt match {
    case ref: ETerm.Ref => evalRef(ref, env)
    case ETerm.Select(base, field, resultTy, span) =>
      evalSelect(evalTerm(base, env), field, env, span.nodeId, evalTypeTerm(resultTy, env))
    case ETerm.App(fn, args, _) => evalApplyTerm(fn, args, env)
    case pi: ETerm.Pi           => evalPi(pi, env)
  }

  private def evalRef[E <: EnvLike[E]](ref: ETerm.Ref, env: E)(implicit eqStore: EqStore): Value = {
    val res = ref match {
      case ETerm.GlobalRef(name, _) => env(name)
      case ETerm.LocalRef(local, _) => env(local)
    }
    resolveInEqStore(res).caseOf {
      case h: ConstructorHead if h.totalArity == 0 => VCtor(h, Vector.empty, h.tpe)
      case _                                       => res
    }
  }

  def evalApply(fn: Value, vArgs: Vector[Value])(implicit eqStore: EqStore): Value = {
    require(vArgs.nonEmpty, "evalApply requires at least one argument")

    fn.tpe.caseOf {
      case pi: VPi =>
        val envWithArgs: RuntimeEnv = getEnvWithArgs(pi, pi.env, vArgs)
        val fn0 = resolve(fn)
        fn0 match {
          case lam @ VLam(_, _, isStable, _) =>
            val res = runLam(lam, vArgs)
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
            ConstructorOps.ConstructorShape.require(h).makeCtor(vArgs, resultTy)
          case b: Blocker => VBlockedApp(b, vArgs, pi.codomain(envWithArgs, eqStore), b.blockerId)
          case _          => throw CannotApplyNonFunction(fn)
        }
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }
  }

  private def evalApplyTerm[E <: EnvLike[E]](fn: ElabAst.Term, args: Vector[ElabAst.Term], env: E)(implicit
      eqStore: EqStore
  ): Value = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    if (vArgs.isEmpty) throw CannotApplyNonFunction(resolve(vf.tpe))
    evalApply(vf, vArgs)
  }

  def evalLam[E <: EnvLike[E]](l: ETerm.Lam, vpi: VPi, env: E): VLam = {
    val capturedIndexes = CapturedIndexes.getCapturedIndexes(l, env)
    val id = l.name match {
      case Some(funcName) => ValueId.Const(funcName)
      case None =>
        val captureVals = env.getLocalsByIndexes(capturedIndexes)
        ValueId.LocalId(l.span.nodeId, captureVals)

    }
    VLam(vpi, id, l.isStable, LamBody.Core(l, env.closeForEval(Some(capturedIndexes))))
  }

  def runLam(lam: VLam, args: Vector[Value])(implicit eqStore: EqStore): Value = {
    val res = lam.body match {
      case LamBody.Native(run) => run(args, eqStore)
      case LamBody.Core(term, coreEnv) =>
        val bodyEnv = getEnvWithArgs(lam.tpe, coreEnv, args)
        val recurEnv =
          term.name match {
            case Some(name) => bodyEnv.putGlobal(name, lam)
            case None       => bodyEnv
          }
        val res = evalTerm(term.body, recurEnv)
        res match {
          case u: UpdatableType =>
            val tpe = lam.tpe.codomain(bodyEnv, eqStore)
            u.withTpe(tpe)
          case _ => res
        }
    }
    resolve(res)
  }

  private def forceThunk(thunk: VBlockedThunk)(implicit eqStore: EqStore): Value =
    thunk.body match {
      case BlockedThunkBody.Select(base, field, env, locationId) =>
        evalSelect(base, field, env, locationId, thunk.tpe)
      case BlockedThunkBody.Match(term, env)                     => evalMatch(term, env)
    }

  private def evalLam[E <: EnvLike[E]](l: ETerm.Lam, env: E)(implicit eqStore: EqStore): VLam = {
    val vpi = evalPi(l.ty, env)
    evalLam(l, vpi, env)
  }

  def getLevel(v: Value)(implicit eqStore: EqStore): Level = {
    v.caseOf {
      case l: Level => l
      case v: Var   => Level.mk(v.id)
      case v        => throw NotALevel(v)
    }
  }

  def evalTerm[E <: EnvLike[E]](term: ElabAst.Term, env: E)(implicit eqStore: EqStore): Value = {
    try {
      term match {
        case ETerm.Select(base, field, resultTy, span) =>
          evalSelect(evalTerm(base, env), field, env, span.nodeId, evalTypeTerm(resultTy, env))
        case ETerm.App(fn, args, _)          => evalApplyTerm(fn, args, env)
        case tt: ElabAst.TypeTerm            => evalTypeTerm(tt, env)
        case l: ETerm.Lam                    => evalLam(l, env)
        case m: ETerm.Match                  => evalMatch(m, env)
        case b: ETerm.Body                   => evalBody(b, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

  def evalSelect[E <: EnvLike[E]](
      v: Value,
      field: String,
      env: E,
      locationId: AstNodeId,
      resultTy: => Value
  )(implicit
      eqStore: EqStore
  ): Value = {
    val v0 = resolve(v)
    v0 match {
      case VCtor(head, fields, _) =>
        if (!head.isStruct) throw NotAStruct(head.name)

        val fieldBinders = ConstructorOps.ConstructorShape.require(head).fieldBinders
        val idx = fieldBinders.indexWhere(_.name == field)
        if (idx >= 0 && idx < fields.length && fieldBinders(idx).name != "_") resolve(fields(idx))
        else throw NotFound(field)

      case b: Blocker =>
        val head = VConst(s"select.$field", Symbol, KernelObject)
        val id = ValueId.LocalId(AstNodeId(None, 0), Vector(head, v0))
        VBlockedThunk(
          BlockedThunkBody.Select(v, field, env.closeForEval(), locationId),
          id,
          resultTy,
          b.blockerId
        )
      case _ =>
        val head = VConst(s"select.$field", Symbol, KernelObject)
        VApp(head, Vector(v), resultTy)
    }
  }

  private def evalMatch[E <: EnvLike[E]](m: ETerm.Match, env: E)(implicit eqStore: EqStore): Value = {
    val (head, args) = evalTerm(m.scrut, env).use(scrut =>
      scrut.caseOf {
        case VCtor(head, fields, _) => (head, fields)
        case other                  =>
          // We are either blocked or stuck
          val capturedIndexes = CapturedIndexes.getCapturedIndexes(m, env)
          val matchCaptures: Vector[Value] = env.getLocalsByIndexes(capturedIndexes)
          val outType: Value = m.motive match {
            case Some(motive) => evalTypeTerm(motive, env)
            case None         => scrut.value.tpe
          }
          other match {
            case b: Blocker =>
              val lamId = ValueId.LocalId(m.span.nodeId, matchCaptures)
              val thunkBody = BlockedThunkBody.Match(m, env.closeForEval(Some(capturedIndexes)))
              return VBlockedThunk(thunkBody, lamId, outType, b.blockerId)
            case _ =>
              val head = VConst(s"match#${m.span.nodeId.stableName}", Symbol, KernelObject)
              return VApp(head, matchCaptures, outType)
          }
      }
    )

    val ctorName = head.name
    val branch =
      m.cases.find(c => c.ctorName == ctorName).getOrElse(throw UnknownConstructor(ctorName, "", Some(m.span)))
    if (args.length != branch.argRefs.length)
      throw ArityMismatch(branch.argRefs.length, args.length, Some(branch.span))
    val newEnv = args.zip(branch.argRefs).foldLeft(env) { case (curEnv, (argV, argRef)) =>
      argRef match {
        case Some(ref) => curEnv.putLocal(ref, argV)
        case None      => curEnv
      }
    }
    evalTerm(branch.body, newEnv)
  }

  def evalBody[E <: EnvLike[E]](body: ETerm.Body, env: E)(implicit eqStore: EqStore): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      val withTpe = (res, l.ty) match {
        case (u: UpdatableType, Some(ty)) =>
          u.withTpe(evalTypeTerm(ty, curEnv))
        case _ => res
      }
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.localRef.name, withTpe, eqStore)) else None
      curEnv.putLocal(l.localRef, withTpe, instanceKey, Some(ETerm.LocalRef(l.localRef, l.span)))
    }
    evalTerm(body.res, newEnv)
  }

  case class Worlds(checkEnv: TypecheckEnv, runEnv: TypecheckEnv)

  def evalDecl(decl: Decl, worlds: Worlds): Worlds = {
    implicit val eqStore = EqStore.empty
    implicit val normalizers = NormalizerMap.empty

    decl match {
      case Decl.ConstDecl(unfoldStrategy, name, ty, body, _, isInstance) =>
        val checkedTy = TypeChecker.getCheckedType(ty, worlds.checkEnv)
        val tyV = checkedTy.value
        val declConst = VConst(name, Symbol, tyV)

        val checkedBody = TypeChecker.check(body, worlds.checkEnv)
        val bodyV0 = checkedBody.value

        TypeChecker.checkType(bodyV0, tyV)
        val bodyV = Value.ascribe(bodyV0, tyV)

        val checkValue: Value = unfoldStrategy match {
          case Some(_) => bodyV
          case None    => declConst
        }
        val checkInstanceKey = if (isInstance) Some(InstanceSearch.instanceKey(name, checkValue, eqStore)) else None
        val nextCheckEnv = worlds.checkEnv.putGlobal(name, checkValue, checkInstanceKey)

        val runtimeTyV = Interpreter.evalTypeTerm(checkedTy.term, worlds.runEnv)
        val runtimeBodyV = Value.ascribe(Interpreter.evalTerm(checkedBody.term, worlds.runEnv), runtimeTyV)
        val runInstanceKey = if (isInstance) Some(InstanceSearch.instanceKey(name, runtimeBodyV, eqStore)) else None
        val nextRunEnv = worlds.runEnv.putGlobal(name, runtimeBodyV, runInstanceKey)

        Worlds(nextCheckEnv, nextRunEnv)

      case Decl.AxiomDecl(name, ty, _, isInstance) =>
        val checkedTy = TypeChecker.getCheckedType(ty, worlds.checkEnv)
        val tyV = checkedTy.value
        val checkValue = VConst(name, Symbol, tyV)
        val checkInstanceKey = if (isInstance) Some(InstanceSearch.instanceKey(name, checkValue, eqStore)) else None
        val nextCheckEnv = worlds.checkEnv.putGlobal(name, checkValue, checkInstanceKey)

        val runtimeTyV = Interpreter.evalTypeTerm(checkedTy.term, worlds.runEnv)
        val runtimeValue = VConst(name, Symbol, runtimeTyV)
        val runInstanceKey = if (isInstance) Some(InstanceSearch.instanceKey(name, runtimeValue, eqStore)) else None
        val nextRunEnv = worlds.runEnv.putGlobal(name, runtimeValue, runInstanceKey)

        Worlds(nextCheckEnv, nextRunEnv)

      case d: Decl.InductiveDecl => InductiveChecks.evalInductiveDecl(d, worlds)

    }

  }

  def run(p: Program): Option[Value] = {
    val baseEnv =
      TypecheckEnv.empty
        .putGlobal("Type", TypeTpe)
        .putGlobal("Normalizer", NormalizerType)
        .putGlobal("Level", LevelTpe)
        .putGlobal("Level.zero", Level.zero)
        .putGlobal("Level.one", Level.one)
        .putGlobal("Prop", PropTpe)

    val builtinFuncs = List[(String, CoreAst.TypeTerm, (Vector[Value], EqStore) => Value)](
      (
        "add_normalizer",
        parseHeader("(A: Type)(zero: A)(add: A -> A -> A): Normalizer"),
        (args, _) => Normalizers.add_normalizer(args)
      ),
      (
        "Level.succ",
        parseHeader("(l: Level): Level"),
        (args, eqStore) => Value.Level.succ(getLevel(args.head)(eqStore))
      ),
      (
        "Level.max",
        parseHeader("(l1: Level)(l2: Level): Level"),
        (args, eqStore) => Value.Level.max(args.map(l => getLevel(l)(eqStore)))
      )
    )

    val env2 = builtinFuncs.foldLeft(baseEnv) { case (curEnv, (name, tpe, lam)) =>
      val tpeV = TypeChecker.evalTypeTerm(tpe, curEnv)(EqStore.empty, NormalizerMap.empty)
      tpeV match {
        case pi: VPi =>
          curEnv.putGlobal(name, VLam(pi, ValueId.Const(name), isStable = true, LamBody.Native(lam)))
        case _ => curEnv
      }
    }

    val envWithSort = env2.putGlobal(
      "Sort",
      VLam(
        {
          val lRef = CoreAst.LocalRef(0, "l")
          val levelRef = ETerm.GlobalRef("Level", Span(0, 0))
          val levelPattern = ElabAst.TypePattern.Type(levelRef)
          VPi(
            env2.closeForEval(),
            Vector(
              VBinder(
                lRef,
                ElabAst.BinderType.TypePattern(levelPattern, levelPattern.span),
                levelRef,
                Vector.empty
              )
            ),
            (env, eqStore) => {
              val l = getLevel(env(lRef))(eqStore)
              VSort(Level.succ(l))
            },
            DepSet.empty,
            ValueId.Const("Sort"),
            TypeTpe
          )
        },
        ValueId.Const("Sort"),
        true,
        LamBody.Native((args, eqStore) => {
          val l = getLevel(args(0))(eqStore)
          VSort(l)
        })
      )
    )

    val nextEnv = Quotients.install(envWithSort)

    val worlds = p.decls.foldLeft(Worlds(nextEnv, nextEnv)) { case (curWorlds, decl) => evalDecl(decl, curWorlds) }
    p.body.map { b =>
      val checked = TypeChecker.check(b, worlds.checkEnv)(EqStore.empty, NormalizerMap.empty)
      Interpreter.evalTerm(checked.term, worlds.runEnv)(EqStore.empty)
    }
  }

  private def parseHeader(s: String): CoreAst.TypeTerm = {
    LanguageParser.parseFuncHeader(s) match {
      case Success(header, _, _) => Elaborator.getType(header)
      case err: Failure          => throw new RuntimeException(err.message)
    }
  }
}
