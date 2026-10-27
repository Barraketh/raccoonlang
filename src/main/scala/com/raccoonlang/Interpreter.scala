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
   * Force links and resume blocked computations when a scheduling dependency has been solved. Materialization handles
   * transitive substitution of heads and arguments. Stop retrying when reduction returns the same blockers, even if a
   * solved dependency remains syntactically present in an opaque result.
   */
  def resolveInEqStore(v: Value, eqStore: EqStore): Value = {
    def retryUnlessStuckOn(next: Value, previousBlockers: DepSet): Value =
      next match {
        case Blocked(nextBlockers) if nextBlockers == previousBlockers => next
        case _                                                         => resolveInEqStore(next, eqStore)
      }

    val v0 = eqStore.force(v)
    v0 match {
      case Blocked(blockerIds) if blockerIds.intersects(eqStore.solvedIds) =>
        v0 match {
          case VBlockedApp(h, args, tpe, oldBlockers) =>
            val h0 = ValueOps.materialize(h, eqStore)
            val materializedArgs = args.map(arg => ValueOps.materialize(arg, eqStore))
            h0 match {
              case lam: VLam => retryUnlessStuckOn(runLam(lam, materializedArgs), oldBlockers)
              case nextHead @ ReductionBlockers(nextBlockers) =>
                val next = VBlockedApp(nextHead, materializedArgs, ValueOps.materialize(tpe, eqStore), nextBlockers)
                retryUnlessStuckOn(next, oldBlockers)
              case other =>
                resolveInEqStore(evalApply(other, materializedArgs), eqStore)
            }
          case vm: NeutralThunk if vm.blockerIds.nonEmpty => retryUnlessStuckOn(forceThunk(vm, eqStore), vm.blockerIds)
          case _ => throw WTF(s"Blocked extractor matched unexpected value $v0")
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
    val id = ValueId.LocalId(pi.nodeId, captureVals)
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
    case ETerm.NatLit(value, _) => NatNormalForm.literal(value)
    case pi: ETerm.Pi           => evalPi(pi, env)
  }

  private def evalRef(ref: ETerm.Ref, env: Env): Value = {
    val res = ref match {
      case ETerm.GlobalRef(name, _) => env(name)
      case ETerm.LocalRef(local, _) => env(local)
    }
    res match {
      case h: ConstructorHead if h.totalArity == 0 => ConstructorValue(h, Vector.empty, h.tpe)
      case _                                       => res
    }
  }

  def evalApply(fn: Value, vArgs: Vector[Value]): Value = {
    require(vArgs.nonEmpty, "evalApply requires at least one argument")

    fn.tpe match {
      case pi: VPi =>
        val envWithArgs = getEnvWithArgs(pi, pi.env, vArgs)
        fn match {
          case lam @ VLam(_, _, _) => runLam(lam, vArgs)
          case h: VConst           => VApp(h, vArgs, pi.codomain(envWithArgs))
          case h: ConstructorHead =>
            val resultTy = pi.codomain(envWithArgs)
            val fields = vArgs.drop(h.numErased)
            ConstructorValue(h, fields, resultTy)
          case blocker @ ReductionBlockers(blockerIds) =>
            VBlockedApp(blocker, vArgs, pi.codomain(envWithArgs), blockerIds)
          case _ => throw CannotApplyNonFunction(fn)
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
        ValueId.LocalId(l.nodeId, captureVals)

    }
    VLam(vpi, id, LamBody.Core(l, RuntimeEnv.closeForEval(env, capturedIndexes)))
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
        evalTerm(term.body, recurEnv)
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

  private[raccoonlang] def stuckMatch(
      m: ETerm.Match,
      scrut: Value,
      env: Env,
      outType: Value
  ): Value = {
    val capturedIndexes = CapturedIndexes.getCapturedIndexes(m, env)
    val matchCaptures = captureValues(env, capturedIndexes)
    val lamId = ValueId.LocalId(m.nodeId, matchCaptures)
    val closedEnv = RuntimeEnv.closeForEval(env, capturedIndexes)
    val blockers = ReductionBlockers.of(scrut)
    NeutralThunk(m, closedEnv, lamId, outType, blockers)
  }

  private def evalMatch(m: ETerm.Match, env: Env): Value = {
    val scrut = evalTerm(m.scrut, env)
    val (head, args) = scrut match {
      case ConstructorValue(head, fields) => (head, fields)
      case _                              =>
        // We are either blocked or stuck
        val outType: Value = m.motive match {
          case Some(motive) => evalTypeTerm(motive, env)
          case None         => scrut.tpe
        }
        return stuckMatch(m, scrut, env, outType)
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
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.localRef.name, res)) else None
      curEnv.putLocal(l.localRef, res, instanceKey)
    }
    evalTerm(body.res, newEnv)
  }

  private def putGlobal(env: Env, name: String, value: Value, isInstance: Boolean): Env =
    env.putGlobal(name, value, if (isInstance) Some(InstanceSearch.instanceKey(name, value)) else None)

  def evalDecl(decl: Decl, env: Env): Env = {
    decl match {
      case Decl.ConstDecl(name, ty, body, span, isInstance, lazyGlobal) =>
        body match {
          case CoreAst.ConstBody.Builtin(_) =>
            if (isInstance) throw WTF("Builtin declarations cannot be instances", Some(span))
            def value(env: Env): Value = Builtins.instantiate(name, TypeChecker.getType(ty, env), span)
            if (lazyGlobal) {
              env.putLazyGlobal(name, () => value(env))
            } else {
              putGlobal(env, name, value(env), isInstance)
            }

          case CoreAst.ConstBody.TermBody(term) =>
            if (lazyGlobal && isInstance) throw WTF("Lazy global instances are not supported", Some(span))

            lazy val checkedTy =
              try {
                val checked = TypeChecker.checkTypeTerm(ty, env)
                TypeChecker.assertType(checked.value)
                checked
              } catch {
                case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, ty.span)
              }
            lazy val checked = TypeChecker.checkTermAgainst(term, env, checkedTy)

            if (lazyGlobal) env.putLazyGlobal(name, () => checked.value)
            else putGlobal(env, name, checked.value, isInstance)
        }

      case Decl.AxiomDecl(name, ty, _, isInstance) =>
        val tyV = TypeChecker.getType(ty, env)
        val checkValue = VConst(name, Symbol, tyV)
        putGlobal(env, name, checkValue, isInstance)

      case d: Decl.InductiveDecl => InductiveChecks.evalInductiveDecl(d, env)

    }

  }

  def run(p: Program, prelude: Prelude.Config = Prelude.default): Option[Value] = {
    val env =
      p.decls.foldLeft(initialEnv(prelude)) { case (curWorlds, decl) => evalDecl(decl, curWorlds) }
    p.body.map { b =>
      TypeChecker.checkTerm(b, env).value
    }
  }

  /** Values the elaborator also knows by name; the kernel's declarations are evaluated on top of these. */
  private[raccoonlang] def primitiveEnv: Env =
    Env.empty
      .putGlobal("Type", TypeTpe)
      .putGlobal("Level", LevelTpe)
      .putGlobal("Level.zero", Level.zero)
      .putGlobal("Level.one", Level.one)
      .putGlobal("Prop", PropTpe)

  private[raccoonlang] def initialEnv(prelude: Prelude.Config = Prelude.default): Env =
    prelude.core.decls.foldLeft(Kernel.env) { case (curEnv, decl) =>
      evalDecl(decl, curEnv)
    }
}
