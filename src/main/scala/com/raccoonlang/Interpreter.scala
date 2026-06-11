package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program}
import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.{BinderOps, TypePatternOps}
import org.roaringbitmap.RoaringBitmap

/**
 * Interpreter evaluates ElabAst into ordinary WHNF Values in the Env it is given. EqStore-aware reduction is isolated
 * to resolveInEqStore and the materialization helpers in ValueOps.
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
          // A stable presentation spine: resume the stuck body computed at the original call site rather
          // than re-running binder instantiation, which would re-solve captures without the call site's env.
          case VApp(_, _, _, Some(_), Some(stuckBody)) =>
            resolveInEqStore(ValueOps.materialize(stuckBody, eqStore), eqStore)
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

  private def getEnvWithArgs(fnTpe: VPi, baseEnv: Env, args: Vector[Value], argEnv: Env): Env =
    BinderOps.instantiateFull(fnTpe.binders, baseEnv, args, argEnv)

  private def captureValues(env: Env, capturedIndexes: RoaringBitmap): Vector[Value] = {
    val values = Vector.newBuilder[Value]
    val it = capturedIndexes.getIntIterator
    while (it.hasNext) {
      val id = it.next()
      values += env(CoreAst.LocalRef(id, s"#$id"))
    }
    values.result()
  }

  def evalPi(pi: ETerm.Pi, env: Env, vBinders: Vector[VBinder]): VPi = {
    val capturedIndexes = CapturedIndexes.getCapturedIndexes(pi, env)
    val captureVals = captureValues(env, capturedIndexes)
    val id = ValueId.LocalId(pi.span.nodeId, captureVals)
    val closedEnv = RuntimeEnv.closeForEval(env, capturedIndexes)

    val synDeps = DepSet.newBuilder
    captureVals.foreach { v =>
      synDeps.unionInPlace(v.synDeps)
    }

    VPi(
      closedEnv,
      vBinders,
      codomain = env => evalTerm(pi.out, env),
      synDeps.result(),
      id,
      pi.classifier
    )
  }

  private def evalPi(pi: ETerm.Pi, env: Env): VPi =
    evalPi(pi, env, pi.binders.map(TypePatternOps.toVBinder))

  private def evalRef(ref: ETerm.Ref, env: Env): Value = {
    val res = ref match {
      case ETerm.GlobalRef(name, _) => env(name)
      case ETerm.LocalRef(local, _) => env(local)
    }
    res match {
      case h: ConstructorHead if h.totalArity == 0 => VCtor(h, Vector.empty, h.tpe)
      case _                                       => res
    }
  }

  private def evalApplyWithClosure(fn: Value, vArgs: Vector[Value], argEnv: Env): Value = {
    require(vArgs.nonEmpty, "evalApply requires at least one argument")

    fn.tpe match {
      case pi: VPi =>
        val envWithArgs = getEnvWithArgs(pi, pi.env, vArgs, argEnv)
        fn match {
          case lam @ VLam(_, _, isStable, _) =>
            val res = runLam(lam, vArgs, argEnv)
            (isStable, res) match {
              case (true, blocked @ Blocked(blockerId)) =>
                blocked match {
                  case VBlockedApp(VLam(_, _, true, _), _, _, _) => res
                  case _ => VApp(fn, vArgs, blocked.tpe, Some(blockerId), stuckBody = Some(blocked))
                }
              case (true, stuck: NeutralThunk) if stuck.blockerId.isEmpty =>
                lam.id match {
                  case ValueId.Const(name) => VApp(VConst(name, StuckDef, lam.tpe), vArgs, stuck.tpe)
                  case _                   => res
                }
              case _ => res
            }
          case h: VConst => VApp(h, vArgs, pi.codomain(envWithArgs))
          case h: ConstructorHead =>
            val resultTy = pi.codomain(envWithArgs)
            VCtor(h, vArgs.drop(h.numErased), resultTy)
          case blocker @ Blocker(blockerId) => VBlockedApp(blocker, vArgs, pi.codomain(envWithArgs), blockerId)
          case _                            => VApp(fn, vArgs, pi.codomain(envWithArgs))
        }
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }
  }

  def evalApply(fn: Value, vArgs: Vector[Value]): Value =
    fn.tpe match {
      case pi: VPi => evalApplyWithClosure(fn, vArgs, pi.env)
      case _       => throw CannotApplyNonFunction(fn.tpe)
    }

  def evalApply(fn: Value, vArgs: Vector[Value], env: Env): Value =
    fn.tpe match {
      case _: VPi => evalApplyWithClosure(fn, vArgs, env)
      case InductiveFamilyValue(family) if family.meta.isStruct =>
        val applyField = evalApply(env(s"${family.head.name}.apply"), Vector(fn), env)
        evalApply(applyField, vArgs, env)
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }

  private def evalApplyTerm(fn: ElabAst.Term, args: Vector[ElabAst.Term], env: Env): Value = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    if (vArgs.isEmpty) throw CannotApplyNonFunction(vf.tpe)
    evalApply(vf, vArgs, env)
  }

  def evalLam(l: ETerm.Lam, vpi: VPi, env: Env): VLam = {
    val capturedIndexes = CapturedIndexes.getCapturedIndexes(l, env)
    val id = l.name match {
      case Some(funcName) => ValueId.Const(funcName)
      case None =>
        val captureVals = captureValues(env, capturedIndexes)
        ValueId.LocalId(l.span.nodeId, captureVals)

    }
    VLam(vpi, id, l.isStable, LamBody.Core(l, RuntimeEnv.closeForEval(env, capturedIndexes)))
  }

  private def defaultLamArgEnv(lam: VLam): Env =
    lam.body match {
      case LamBody.Native(_, nativeEnv, _) => nativeEnv
      case LamBody.Core(_, coreEnv)        => coreEnv
    }

  def runLam(lam: VLam, args: Vector[Value]): Value =
    runLam(lam, args, defaultLamArgEnv(lam))

  def runLam(lam: VLam, args: Vector[Value], argEnv: Env): Value = {
    lam.body match {
      case LamBody.Native(run, nativeEnv, _) => run(args, nativeEnv)
      case LamBody.Core(term, coreEnv) =>
        val bodyEnv = getEnvWithArgs(lam.tpe, coreEnv, args, argEnv)

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

  private def evalLam(l: ETerm.Lam, env: Env): VLam = {
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

  def evalTerm(term: ElabAst.Term, env: Env): Value = {
    try {
      term match {
        case ETerm.App(fn, args, _) => evalApplyTerm(fn, args, env)
        case l: ETerm.Lam           => evalLam(l, env)
        case pi: ETerm.Pi           => evalPi(pi, env)
        case ref: ETerm.Ref         => evalRef(ref, env)
        case m: ETerm.Match         => evalMatch(m, env)
        case b: ETerm.Body          => evalBody(b, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }
  }

  private def evalMatch(m: ETerm.Match, env: Env): Value = {
    val scrut = evalTerm(m.scrut, env)
    val (head, args) = scrut match {
      case VCtor(head, fields, _) => (head, fields)
      case other                  =>
        // We are either blocked or stuck
        val capturedIndexes = CapturedIndexes.getCapturedIndexes(m, env)
        val matchCaptures: Vector[Value] = captureValues(env, capturedIndexes)
        val outType: Value = m.motive match {
          case Some(motive) => evalTerm(motive, env)
          case None         => scrut.tpe
        }
        val lamId = ValueId.LocalId(m.span.nodeId, matchCaptures)
        val closedEnv = RuntimeEnv.closeForEval(env, capturedIndexes)
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

  def evalBody(body: ETerm.Body, env: Env): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      val withTpe = (res, l.ty) match {
        case (u: UpdatableType, Some(ty)) =>
          u.withTpe(evalTerm(ty, curEnv))
        case _ => res
      }
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.localRef.name, withTpe)) else None
      curEnv.putLocal(l.localRef, withTpe, instanceKey)
    }
    evalTerm(body.res, newEnv)
  }

  case class Worlds(checkEnv: Env, runEnv: Env)

  private def putGlobal(env: Env, name: String, value: Value, isInstance: Boolean): Env =
    env.putGlobal(name, value, if (isInstance) Some(InstanceSearch.instanceKey(name, value)) else None)

  def evalDecl(decl: Decl, worlds: Worlds): Worlds = {
    decl match {
      case Decl.ConstDecl(unfoldStrategy, name, ty, body, span, isInstance, lazyGlobal) =>
        body match {
          case CoreAst.ConstBody.Builtin(_) =>
            if (unfoldStrategy.nonEmpty) throw WTF("Builtin declarations cannot be stable", Some(span))
            if (isInstance) throw WTF("Builtin declarations cannot be instances", Some(span))
            def value(env: Env): Value = Builtins.instantiate(name, TypeChecker.getType(ty, env), span)
            if (lazyGlobal)
              Worlds(
                worlds.checkEnv.putLazyGlobal(name, () => value(worlds.checkEnv)),
                worlds.runEnv.putLazyGlobal(name, () => value(worlds.runEnv))
              )
            else
              Worlds(
                putGlobal(worlds.checkEnv, name, value(worlds.checkEnv), isInstance),
                putGlobal(worlds.runEnv, name, value(worlds.runEnv), isInstance)
              )

          case CoreAst.ConstBody.TermBody(term) =>
            if (lazyGlobal && isInstance) throw WTF("Lazy global instances are not supported", Some(span))
            val checkEnv = worlds.checkEnv
            val runEnv = worlds.runEnv
            lazy val checked = TypeChecker.checkTerm(term, checkEnv)
            lazy val checkedTy = TypeChecker.getType(ty, checkEnv)
            lazy val checkValue = {
              TypeChecker.checkType(checked.value, checkedTy, checkEnv.normalizers)
              val bodyV = Value.ascribe(checked.value, checkedTy)
              unfoldStrategy match {
                case Some(_) => bodyV
                case None    => VConst(name, Symbol, checkedTy)
              }
            }
            lazy val runTy = TypeChecker.getType(ty, runEnv)
            lazy val runtimeValue =
              unfoldStrategy match {
                case Some(_) => Value.ascribe(evalTerm(checked.residual, runEnv), runTy)
                case None    => VConst(name, Symbol, runTy)
              }
            if (lazyGlobal)
              Worlds(checkEnv.putLazyGlobal(name, () => checkValue), runEnv.putLazyGlobal(name, () => runtimeValue))
            else
              Worlds(
                putGlobal(checkEnv, name, checkValue, isInstance),
                putGlobal(runEnv, name, runtimeValue, isInstance)
              )
        }

      case Decl.AxiomDecl(name, ty, _, isInstance) =>
        val tyV = TypeChecker.getType(ty, worlds.checkEnv)
        val checkValue = VConst(name, Symbol, tyV)
        val nextCheckEnv = putGlobal(worlds.checkEnv, name, checkValue, isInstance)

        val runtimeTyV = TypeChecker.getType(ty, worlds.runEnv)
        val runtimeValue = VConst(name, Symbol, runtimeTyV)
        val nextRunEnv = putGlobal(worlds.runEnv, name, runtimeValue, isInstance)

        Worlds(nextCheckEnv, nextRunEnv)

      case d: Decl.InductiveDecl => InductiveChecks.evalInductiveDecl(d, worlds)

    }

  }

  def run(p: Program, prelude: Prelude.Config = Prelude.default): Option[Value] = {
    val worlds =
      p.decls.foldLeft(initialWorlds(prelude)) { case (curWorlds, decl) => evalDecl(decl, curWorlds) }
    p.body.map { b =>
      val checked = TypeChecker.checkTerm(b, worlds.checkEnv)
      evalTerm(checked.residual, worlds.runEnv)
    }
  }

  private[raccoonlang] def initialWorlds(prelude: Prelude.Config = Prelude.default): Worlds = {
    val baseEnv =
      Env.empty
        .putGlobal("Type", TypeTpe)
        .putGlobal("Normalizer", NormalizerType)
        .putGlobal("Level", LevelTpe)
        .putGlobal("Level.zero", Level.zero)
        .putGlobal("Level.one", Level.one)
        .putGlobal("Prop", PropTpe)

    prelude.core.decls.foldLeft(Worlds(baseEnv, baseEnv)) { case (curWorlds, decl) =>
      evalDecl(decl, curWorlds)
    }
  }
}
