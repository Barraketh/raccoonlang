package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program}
import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * Interpreter evaluates ElabAst into ordinary WHNF Values in the Env[Value] it is given. EqStore-aware reduction is
 * isolated to resolveInEqStore and the materialization helpers in ValueOps.
 */
object Interpreter {
  private def normalizeLevel(l: Level, eqStore: EqStore): Level = {
    val pieces = Vector(Level.const(l.c)) ++
      l.atoms.toVector.map { case (atom, k) =>
        val base = eqStore.subst.get(atom) match {
          case Some(sol) =>
            eqStore.force(sol) match {
              case next: Level   => normalizeLevel(next, eqStore)
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
  def resolveInEqStore(v: Value, eqStore: EqStore): Value = {
    val v0 = eqStore.force(v)
    v0 match {
      case Blocked(blockerId) if eqStore.subst.contains(blockerId) =>
        v0 match {
          case VBlockedApp(h, args, tpe, _) =>
            val h0 = ValueOps.materialize(resolveInEqStore(h, eqStore), eqStore)
            val materializedArgs = args.map(arg => ValueOps.materialize(arg, eqStore))
            h0 match {
              case lam: VLam =>
                val res = runLam(lam, materializedArgs)
                resolveInEqStore(res, eqStore)
              case nextHead @ Blocker(nextBlockerId) =>
                VBlockedApp(nextHead, args, tpe, nextBlockerId)
              case other =>
                resolveInEqStore(evalApply(other, materializedArgs), eqStore)
            }
          case vm: NeutralThunk if vm.blockerId.nonEmpty => resolveInEqStore(forceThunk(vm, eqStore), eqStore)
          case _                                         => throw WTF(s"Blocked extractor matched unexpected value $v0")
        }

      case l: Level if l.atoms.keySet.intersect(eqStore.subst.keySet).nonEmpty => normalizeLevel(l, eqStore)

      case _ => v0
    }
  }

  private def getEnvWithArgs(fnTpe: VPi, baseEnv: Env[Value], args: Vector[Value]): Env[Value] =
    BinderOps.instantiateFull(fnTpe.binders, baseEnv, args)

  def evalPi(pi: ETerm.Pi, env: Env[Value], vBinders: Vector[VBinder]): VPi = {
    val capturedRefs = CapturedRefs.getCapturedRefs(pi, env)
    val closedEnv = env.closeForEval(capturedRefs)
    val captureVals = closedEnv.locals.values.toVector
    val id = ValueId.LocalId(pi.span.nodeId, captureVals)

    val synDeps = DepSet.newBuilder
    captureVals.foreach { v =>
      synDeps.unionInPlace(v.synDeps)
    }

    VPi(
      closedEnv,
      vBinders,
      codomain = env => evalTypeTerm(pi.out, env),
      synDeps.result(),
      id,
      pi.classifier,
      pi.numLevelParams
    )
  }

  private def evalPi(pi: ETerm.Pi, env: Env[Value]): VPi =
    evalPi(pi, env, pi.binders.map(BinderOps.toVBinder))

  def evalTypeTerm(tt: ElabAst.TypeTerm, env: Env[Value]): Value = tt match {
    case ref: ETerm.Ref         => evalRef(ref, env)
    case ETerm.App(fn, args, _) => evalApplyTerm(fn, args, env)
    case pi: ETerm.Pi           => evalPi(pi, env)
  }

  private def evalRef(ref: ETerm.Ref, env: Env[Value]): Value = {
    val res = ref match {
      case ETerm.GlobalRef(name, _) => env(name)
      case ETerm.LocalRef(local, _) => env(local)
    }
    res match {
      case h: ConstructorHead if h.totalArity == 0 => VCtor(h, Vector.empty, h.tpe)
      case _                                       => res
    }
  }

  def evalApply(fn: Value, vArgs: Vector[Value]): Value = {
    require(vArgs.nonEmpty, "evalApply requires at least one argument")

    fn.tpe match {
      case pi: VPi =>
        val envWithArgs = getEnvWithArgs(pi, pi.env, vArgs)
        fn match {
          case lam: VLam =>
            runLam(lam, vArgs)
          case h: VConst => VApp(h, vArgs, pi.codomain(envWithArgs))
          case h: ConstructorHead =>
            val resultTy = pi.codomain(envWithArgs)
            VCtor(h, Value.constructorStoredArgs(h, vArgs), resultTy)
          case blocker @ Blocker(blockerId) => VBlockedApp(blocker, vArgs, pi.codomain(envWithArgs), blockerId)
          case _                            => throw CannotApplyNonFunction(fn)
        }
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }
  }

  private def evalApplyTerm(fn: ElabAst.Term, args: Vector[ElabAst.Term], env: Env[Value]): Value = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    if (vArgs.isEmpty) throw CannotApplyNonFunction(vf.tpe)
    evalApply(vf, vArgs)
  }

  def evalLam(l: ETerm.Lam, vpi: VPi, env: Env[Value]): VLam = {
    val capturedRefs = CapturedRefs.getCapturedRefs(l, env)
    val closedEnv = env.closeForEval(capturedRefs)
    val id = l.name match {
      case Some(funcName) => ValueId.Const(funcName)
      case None =>
        ValueId.LocalId(l.span.nodeId, closedEnv.locals.values.toVector)

    }
    VLam(vpi, id, LamBody.Core(l, closedEnv))
  }

  def runLam(lam: VLam, args: Vector[Value]): Value = {
    lam.body match {
      case LamBody.Native(run, nativeEnv, _) => run(args, nativeEnv)
      case LamBody.Core(term, coreEnv) =>
        val bodyEnv = getEnvWithArgs(lam.tpe, coreEnv, args)

        // Update env with recursive reference
        val recurEnv = term.recursiveSelf match {
          case Some(ref) => bodyEnv.putLocal(ref, lam)
          case None      => bodyEnv
        }
        val res = evalTerm(term.body, recurEnv)
        res match {
          case u: UpdatableType =>
            val tpe = lam.tpe.codomain(bodyEnv)
            u.withTpe(tpe)
          case _ => res
        }
    }
  }

  private def forceThunk(thunk: NeutralThunk, eqStore: EqStore): Value =
    evalMatch(thunk.term, ValueOps.materializeEnv(thunk.env, eqStore))

  private def evalLam(l: ETerm.Lam, env: Env[Value]): VLam = {
    val vpi = evalPi(l.ty, env)
    evalLam(l, vpi, env)
  }

  def getLevel(v: Value): Level = {
    v match {
      case l: Level => l
      case v: Var   => Level.mk(v.id)
      case v        => throw NotALevel(v)
    }
  }

  def evalTerm(term: ElabAst.Term, env: Env[Value]): Value = {
    try {
      term match {
        case ETerm.App(fn, args, _) => evalApplyTerm(fn, args, env)
        case tt: ElabAst.TypeTerm   => evalTypeTerm(tt, env)
        case l: ETerm.Lam           => evalLam(l, env)
        case m: ETerm.Match         => evalMatch(m, env)
        case b: ETerm.Body          => evalBody(b, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw e.withSpan(term.span)
    }
  }

  private def evalMatch(m: ETerm.Match, env: Env[Value]): Value = {
    val scrut = evalTerm(m.scrut, env)
    val (head, args) = scrut match {
      case VCtor(head, storedArgs, _) => (head, Value.constructorPatternArgs(head, storedArgs))
      case other                      =>
        // We are either blocked or stuck
        val capturedRefs = CapturedRefs.getCapturedRefs(m, env)
        val closedEnv = env.closeForEval(capturedRefs)
        val matchCaptures = closedEnv.locals.values.toVector
        val outType: Value = m.motive match {
          case Some(motive) => evalTypeTerm(motive, env)
          case None         => scrut.tpe
        }
        val lamId = ValueId.LocalId(m.span.nodeId, matchCaptures)
        other match {
          case Blocker(blockerId) => return NeutralThunk(m, closedEnv, lamId, outType, Some(blockerId))
          case _                  => return NeutralThunk(m, closedEnv, lamId, outType, None)
        }
    }

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

  def evalBody(body: ETerm.Body, env: Env[Value]): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      val withTpe = (res, l.ty) match {
        case (u: UpdatableType, Some(ty)) =>
          u.withTpe(evalTypeTerm(ty, curEnv))
        case _ => res
      }
      curEnv.putLocal(l.localRef, withTpe)
    }
    evalTerm(body.res, newEnv)
  }

  case class Worlds(checkContext: TypingContext, runContext: TypingContext) {
    def checkEnv: Env[Value] = checkContext.env
    def runEnv: Env[Value] = runContext.env
  }

  def evalDecl(decl: Decl, worlds: Worlds): Worlds = {
    decl match {
      case Decl.ConstDecl(isOpaque, name, ty, body, span, isInstance, lazyGlobal) =>
        body match {
          case CoreAst.ConstBody.Builtin(_) =>
            if (isOpaque) throw WTF("Builtin declarations cannot be opaque", Some(span))
            if (isInstance) throw WTF("Builtin declarations cannot be instances", Some(span))
            def value(context: TypingContext): Value =
              Builtins.instantiate(name, TypeChecker.getType(ty, context), span)
            if (lazyGlobal)
              Worlds(
                worlds.checkContext.putLazyGlobal(name, () => value(worlds.checkContext)),
                worlds.runContext.putLazyGlobal(name, () => value(worlds.runContext))
              )
            else {
              Worlds(
                worlds.checkContext.putGlobal(name, value(worlds.checkContext), isInstance = isInstance),
                worlds.runContext.putGlobal(name, value(worlds.runContext), isInstance = isInstance)
              )
            }

          case CoreAst.ConstBody.TermBody(term) =>
            if (lazyGlobal && isInstance) throw WTF("Lazy global instances are not supported", Some(span))
            val checkContext = worlds.checkContext
            val runContext = worlds.runContext
            lazy val checked = TypeChecker.checkTerm(term, checkContext)
            lazy val checkedTy = TypeChecker.getType(ty, checkContext)
            lazy val checkValue = {
              TypeChecker.checkType(checked.value, checkedTy)
              val bodyV = Value.ascribe(checked.value, checkedTy)
              if (isOpaque) VConst(name, Symbol, checkedTy) else bodyV
            }
            lazy val runTy = TypeChecker.getType(ty, runContext)
            lazy val runtimeValue =
              if (isOpaque) VConst(name, Symbol, runTy)
              else Value.ascribe(evalTerm(checked.residual, runContext.env), runTy)
            if (lazyGlobal)
              Worlds(
                checkContext.putLazyGlobal(name, () => checkValue),
                runContext.putLazyGlobal(name, () => runtimeValue)
              )
            else {
              Worlds(
                checkContext.putGlobal(name, checkValue, isInstance = isInstance),
                runContext.putGlobal(name, runtimeValue, isInstance = isInstance)
              )
            }
        }

      case Decl.AxiomDecl(name, ty, _, isInstance) =>
        val tyV = TypeChecker.getType(ty, worlds.checkContext)
        val checkValue = VConst(name, Symbol, tyV)
        val nextCheckContext = worlds.checkContext.putGlobal(name, checkValue, isInstance = isInstance)

        val runtimeTyV = TypeChecker.getType(ty, worlds.runContext)
        val runtimeValue = VConst(name, Symbol, runtimeTyV)
        val nextRunContext = worlds.runContext.putGlobal(name, runtimeValue, isInstance = isInstance)

        Worlds(nextCheckContext, nextRunContext)

      case d: Decl.InductiveDecl => InductiveChecks.evalInductiveDecl(d, worlds)

    }

  }

  def run(p: Program, prelude: Prelude.Config = Prelude.default): Option[Value] = {
    val worlds =
      p.decls.foldLeft(initialWorlds(prelude)) { case (curWorlds, decl) => evalDecl(decl, curWorlds) }
    p.body.map { b =>
      val checked = TypeChecker.checkTerm(b, worlds.checkContext)
      evalTerm(checked.residual, worlds.runEnv)
    }
  }

  private[raccoonlang] def initialWorlds(prelude: Prelude.Config = Prelude.default): Worlds = {
    val baseEnv =
      Env
        .empty[Value]
        .putGlobal("Type", TypeTpe)
        .putGlobal("Level", LevelTpe)
        .putGlobal("Level.zero", Level.zero)
        .putGlobal("Level.one", Level.one)
        .putGlobal("Prop", PropTpe)

    val baseContext = TypingContext.envOnly(baseEnv)

    prelude.core.decls.foldLeft(Worlds(baseContext, baseContext)) { case (curWorlds, decl) =>
      evalDecl(decl, curWorlds)
    }
  }
}
