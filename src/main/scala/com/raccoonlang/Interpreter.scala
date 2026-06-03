package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program}
import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.{BinderOps, ConstructorOps, TypePatternOps}
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

  private def getEnvWithArgs(fnTpe: VPi, baseEnv: Env, args: Vector[Value]): Env =
    BinderOps.instantiateFull(fnTpe.binders, baseEnv, args)

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
      codomain = env => evalTypeTerm(pi.out, env),
      synDeps.result(),
      id,
      pi.classifier
    )
  }

  private def evalPi(pi: ETerm.Pi, env: Env): VPi =
    evalPi(pi, env, pi.binders.map(TypePatternOps.toVBinder))

  def evalTypeTerm(tt: ElabAst.TypeTerm, env: Env): Value = tt match {
    case ref: ETerm.Ref         => evalRef(ref, env)
    case ETerm.App(fn, args, _) => evalApplyTerm(fn, args, env)
    case pi: ETerm.Pi           => evalPi(pi, env)
  }

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

  def evalApply(fn: Value, vArgs: Vector[Value]): Value = {
    require(vArgs.nonEmpty, "evalApply requires at least one argument")

    fn.tpe match {
      case pi: VPi =>
        val envWithArgs = getEnvWithArgs(pi, pi.env, vArgs)
        fn match {
          case lam @ VLam(_, _, isStable, _) =>
            val res = runLam(lam, vArgs)
            (isStable, res) match {
              case (true, blocked @ Blocked(blockerId)) =>
                blocked match {
                  case VBlockedApp(VLam(_, _, true, _), _, _, _) => res
                  case _                                         => VBlockedApp(fn, vArgs, blocked.tpe, blockerId)
                }
              case (true, stuck: NeutralThunk) if stuck.blockerId.isEmpty =>
                lam.id match {
                  case ValueId.Const(name) => VApp(VConst(name, Symbol, lam.tpe), vArgs, stuck.tpe)
                  case _                   => res
                }
              case _ => res
            }
          case h: VConst => VApp(h, vArgs, pi.codomain(envWithArgs))
          case h: ConstructorHead =>
            val resultTy = pi.codomain(envWithArgs)
            ConstructorOps.ConstructorShape.require(h).makeCtor(vArgs, resultTy)
          case blocker @ Blocker(blockerId) => VBlockedApp(blocker, vArgs, pi.codomain(envWithArgs), blockerId)
          case _                            => throw CannotApplyNonFunction(fn)
        }
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }
  }

  private def evalApplyTerm(fn: ElabAst.Term, args: Vector[ElabAst.Term], env: Env): Value = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    if (vArgs.isEmpty) throw CannotApplyNonFunction(vf.tpe)
    evalApply(vf, vArgs)
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
        case tt: ElabAst.TypeTerm   => evalTypeTerm(tt, env)
        case l: ETerm.Lam           => evalLam(l, env)
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
      case ctor @ VCtor(head, _, _) => (head, ctor.fields)
      case other                    =>
        // We are either blocked or stuck
        val capturedIndexes = CapturedIndexes.getCapturedIndexes(m, env)
        val matchCaptures: Vector[Value] = captureValues(env, capturedIndexes)
        val outType: Value = m.motive match {
          case Some(motive) => evalTypeTerm(motive, env)
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
          u.withTpe(evalTypeTerm(ty, curEnv))
        case _ => res
      }
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.localRef.name, withTpe)) else None
      curEnv.putLocal(l.localRef, withTpe, instanceKey)
    }
    evalTerm(body.res, newEnv)
  }

  case class Worlds(checkEnv: Env, runEnv: Env)

  def evalDecl(decl: Decl, worlds: Worlds): Worlds = {
    decl match {
      case Decl.ConstDecl(unfoldStrategy, name, ty, body, span, isInstance) =>
        val tyV = TypeChecker.getType(ty, worlds.checkEnv)
        val runtimeTyV = TypeChecker.getType(ty, worlds.runEnv)

        val (checkValue, runtimeValue) = body match {
          case CoreAst.ConstBody.Builtin(_) =>
            if (unfoldStrategy.nonEmpty) throw WTF("Builtin declarations cannot be stable", Some(span))
            if (isInstance) throw WTF("Builtin declarations cannot be instances", Some(span))
            (Builtins.instantiate(name, tyV, span), Builtins.instantiate(name, runtimeTyV, span))

          case CoreAst.ConstBody.TermBody(term) =>
            val declConst = VConst(name, Symbol, tyV)
            val bodyV0 = TypeChecker.check(term, worlds.checkEnv)

            TypeChecker.checkType(bodyV0, tyV, worlds.checkEnv.normalizers)
            val bodyV = Value.ascribe(bodyV0, tyV)

            val checkValue: Value = unfoldStrategy match {
              case Some(_) => bodyV
              case None    => declConst
            }
            val runtimeBodyV = Value.ascribe(TypeChecker.check(term, worlds.runEnv), runtimeTyV)
            (checkValue, runtimeBodyV)
        }

        val checkInstanceKey = if (isInstance) Some(InstanceSearch.instanceKey(name, checkValue)) else None
        val nextCheckEnv = worlds.checkEnv.putGlobal(name, checkValue, checkInstanceKey)

        val runInstanceKey = if (isInstance) Some(InstanceSearch.instanceKey(name, runtimeValue)) else None
        val nextRunEnv = worlds.runEnv.putGlobal(name, runtimeValue, runInstanceKey)

        Worlds(nextCheckEnv, nextRunEnv)

      case Decl.AxiomDecl(name, ty, _, isInstance) =>
        val tyV = TypeChecker.getType(ty, worlds.checkEnv)
        val checkValue = VConst(name, Symbol, tyV)
        val checkInstanceKey = if (isInstance) Some(InstanceSearch.instanceKey(name, checkValue)) else None
        val nextCheckEnv = worlds.checkEnv.putGlobal(name, checkValue, checkInstanceKey)

        val runtimeTyV = TypeChecker.getType(ty, worlds.runEnv)
        val runtimeValue = VConst(name, Symbol, runtimeTyV)
        val runInstanceKey = if (isInstance) Some(InstanceSearch.instanceKey(name, runtimeValue)) else None
        val nextRunEnv = worlds.runEnv.putGlobal(name, runtimeValue, runInstanceKey)

        Worlds(nextCheckEnv, nextRunEnv)

      case d: Decl.InductiveDecl => InductiveChecks.evalInductiveDecl(d, worlds)

    }

  }

  def run(p: Program, prelude: Prelude.Config = Prelude.default): Option[Value] = {
    val worlds =
      p.decls.foldLeft(initialWorlds(prelude)) { case (curWorlds, decl) => evalDecl(decl, curWorlds) }
    p.body.map { b =>
      TypeChecker.check(b, worlds.checkEnv)
      TypeChecker.check(b, worlds.runEnv)
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
