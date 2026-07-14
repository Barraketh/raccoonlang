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

  /**
   * Runtime arguments carry the checker's ascription discipline (checkApplyChecked's verification
   * pass): each arg is retyped at its instantiated binder type, so type-directed work inside the
   * body — implicit reconstruction above all — reads the binder-declared type, never the
   * argument's construction-site type. The two are always defEq (sorts are not cumulative) but
   * need not be structurally identical, and projection is structural: this keeps run-world
   * projection reading exactly the shapes the checker read. Binder types are evaluated against
   * the Pi's own closure — their syntax is valid there, not in the body env the values are later
   * bound into.
   */
  private def ascribeArgs(fnTpe: VPi, args: Vector[Value]): Vector[Value] = {
    if (fnTpe.binders.length != args.length) throw ArityMismatch(fnTpe.binders.length, args.length)
    var tyEnv = fnTpe.env
    fnTpe.binders.zip(args).map { case (binder, value) =>
      val ascribed = value match {
        // Only neutrals carry a rewritable type annotation; skip the binder-type evaluation
        // for values (sorts, levels) whose ascription is the identity.
        case _: UpdatableType => Value.ascribe(value, evalTypeTerm(binder.ty, tyEnv))
        case _                => value
      }
      tyEnv = tyEnv.putLocal(binder.localRef, ascribed)
      ascribed
    }
  }

  private def getEnvWithArgs(fnTpe: VPi, baseEnv: Env[Value], args: Vector[Value]): Env[Value] =
    BinderOps.instantiateFull(fnTpe.binders, baseEnv, ascribeArgs(fnTpe, args))

  /**
   * The universe of a Pi, derived from the env it closed over: max of the binder types' universes
   * and the codomain's universe, with the impredicative collapse to Prop for Prop-valued codomains.
   * This replicates what the checker validates at Pi formation, but per instance — a residual Pi
   * re-evaluated with concrete levels gets the concrete universe, not the declaration-time one.
   */
  private def piClassifier(binders: Vector[VBinder], baseEnv: Env[Value], out: ElabAst.TypeTerm): VSort = {
    val freshEnv = BinderOps.freshen(binders, baseEnv)
    val outV = evalTypeTerm(out, freshEnv)
    // Impredicative collapse first: Prop-valued codomains need no domain universe walk.
    if (TypeChecker.isPropValuedType(outV)) PropTpe
    else {
      val VSort(outLevel) = TypeChecker.getUniverse(outV)
      val domLevels = binders.map { binder =>
        val VSort(level) = TypeChecker.getUniverse(freshEnv(binder.localRef).tpe)
        level
      }
      VSort(Level.max(domLevels :+ outLevel))
    }
  }

  def evalPi(pi: ETerm.Pi, env: Env[Value], vBinders: Vector[VBinder]): VPi = {
    val capturedRefs = CapturedRefs.getCapturedRefs(pi, env)
    val closedEnv = env.closeForEval(capturedRefs)
    val captureVals = closedEnv.locals.values.toVector
    val id = ValueId.LocalId(pi.nodeId, captureVals)

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
      classifier0 = () => piClassifier(vBinders, closedEnv, pi.out)
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
      case h: ConstructorHead if h.totalArity == 0 => Value.collapseIfProof(VCtor(h, Vector.empty, h.tpe))
      case _                                       => res
    }
  }

  def evalApply(fn: Value, vArgs: Vector[Value]): Value = {
    require(vArgs.nonEmpty, "evalApply requires at least one argument")

    fn.tpe match {
      case pi: VPi =>
        // Lazy: the VLam branch delegates env construction to runLam.
        lazy val envWithArgs = getEnvWithArgs(pi, pi.env, vArgs)
        fn match {
          case lam: VLam =>
            runLam(lam, vArgs)
          case p: VProof =>
            // By impredicativity, a Pi with a propositional codomain is itself a proposition, so a
            // proof-valued function is a collapsed proof: its application is a proof of the
            // instantiated codomain, with no body to run (proof-collapse.md §5).
            VProof(pi.codomain(envWithArgs), evalApply(p.witness, vArgs))
          case h: VConst => Value.collapseIfProof(VApp(h, vArgs, pi.codomain(envWithArgs)))
          case h: ConstructorHead =>
            val resultTy = pi.codomain(envWithArgs)
            Value.collapseIfProof(VCtor(h, Value.constructorStoredArgs(h, vArgs), resultTy))
          case blocker @ Blocker(blockerId) =>
            Value.collapseIfProof(VBlockedApp(blocker, vArgs, pi.codomain(envWithArgs), blockerId))
          case _ => throw CannotApplyNonFunction(fn)
        }
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }
  }

  private def evalApplyTerm(fn: ElabAst.Term, args: Vector[ElabAst.Term], env: Env[Value]): Value = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    if (vArgs.isEmpty) throw CannotApplyNonFunction(vf.tpe)
    evalApply(vf, reconstructImplicits(vf, vArgs, fn.span))
  }

  private def valueName(v: Value): String =
    v match {
      case VConst(name, _, _)                 => name
      case VLam(_, ValueId.Const(name), _)    => name
      case head: ConstructorHead              => head.name
      case _                                  => "function"
    }

  /**
   * Two-arity dispatch for checked application syntax: quoted residuals (match motives, derive
   * results) carry full value spines, while source applications carry only the explicit args —
   * the implicit ones are re-derived here by running their projection specs against the provided
   * args, exactly as application checking did (Projection.project is the shared implementation).
   */
  private def reconstructImplicits(fn: Value, vArgs: Vector[Value], span: Span): Vector[Value] =
    fn.tpe match {
      case pi: VPi if pi.binders.exists(_.isImplicit) && vArgs.length != pi.binders.length =>
        val numExplicit = pi.binders.count(!_.isImplicit)
        if (vArgs.length != numExplicit) throw ArityMismatch(numExplicit, vArgs.length, Some(span))
        var provided = 0
        pi.binders.map { binder =>
          if (!binder.isImplicit) {
            val arg = vArgs(provided)
            provided += 1
            arg
          } else {
            val spec = binder.projection.getOrElse(
              throw WTF(s"Implicit binder ${binder.name} of ${valueName(fn)} has no projection spec", Some(span))
            )
            telescope.Projection.project(spec, vArgs) match {
              case Right(value) => value
              case Left(reason) => throw ImplicitReconstructionFailed(binder.name, valueName(fn), reason, Some(span))
            }
          }
        }
      case _ => vArgs
    }

  def evalLam(l: ETerm.Lam, vpi: VPi, env: Env[Value]): Value = {
    val capturedRefs = CapturedRefs.getCapturedRefs(l, env)
    val closedEnv = env.closeForEval(capturedRefs)
    val id = l.name match {
      case Some(funcName) => ValueId.Const(funcName)
      case None =>
        ValueId.LocalId(l.nodeId, closedEnv.locals.values.toVector)

    }
    // A lambda whose Pi is classified in Prop is a proof of that implication and collapses.
    Value.collapseIfProof(VLam(vpi, id, LamBody.Core(l, closedEnv)))
  }

  def runLam(lam: VLam, args: Vector[Value]): Value = {
    lam.body match {
      case LamBody.Native(run, nativeEnv, _) => run(args, nativeEnv)
      case LamBody.Core(term, coreEnv) =>
        val ascribedArgs = ascribeArgs(lam.tpe, args)
        val bodyEnv = BinderOps.instantiateFull(lam.tpe.binders, coreEnv, ascribedArgs)

        // Update env with recursive reference
        val recurEnv = term.recursiveSelf match {
          case Some(ref) => bodyEnv.putLocal(ref, lam)
          case None      => bodyEnv
        }
        val res = evalTerm(term.body, recurEnv)
        res match {
          case u: UpdatableType =>
            // The codomain closure is applied over the Pi's OWN env, not the body env: ascription
            // can install a ref-compatible Pi whose closure differs from the lambda's captures
            // (VLam.withTpe), and codomain syntax is only evaluable in its own closure.
            val tpe = lam.tpe.codomain(BinderOps.instantiateFull(lam.tpe.binders, lam.tpe.env, ascribedArgs))
            Value.ascribe(u, tpe)
          case _ => res
        }
    }
  }

  private def forceThunk(thunk: NeutralThunk, eqStore: EqStore): Value =
    evalMatch(thunk.term, ValueOps.materializeEnv(thunk.env, eqStore))

  private def evalLam(l: ETerm.Lam, env: Env[Value]): Value = {
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
      case proof: VProof              => return evalProofMatch(m, proof, env)
      case other                      =>
        // We are either blocked or stuck
        val blockerId = other match {
          case Blocker(id) => Some(id)
          case _           => None
        }
        return Value.collapseIfProof(stuckMatchThunk(m, env, matchOutType(m, scrut, env), blockerId))
    }

    val ctorName = head.name
    val branch =
      m.cases.find(c => c.ctorName == ctorName).getOrElse(throw UnknownConstructor(ctorName, "", Some(m.span)))
    evalBranch(branch, args, env)
  }

  private def matchOutType(m: ETerm.Match, scrut: Value, env: Env[Value]): Value =
    m.motive match {
      case Some(motive) => evalTypeTerm(motive, env)
      case None         => scrut.tpe
    }

  private def stuckMatchThunk(m: ETerm.Match, env: Env[Value], outType: Value, blockerId: Option[VarId]): NeutralThunk = {
    val closedEnv = env.closeForEval(CapturedRefs.getCapturedRefs(m, env))
    NeutralThunk(m, closedEnv, ValueId.LocalId(m.nodeId, closedEnv.locals.values.toVector), outType, blockerId)
  }

  private def evalBranch(branch: ElabAst.Case, args: Vector[Value], env: Env[Value]): Value = {
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

  /**
   * Elimination of a collapsed proof (docs/proof-collapse.md §5). Proofs store no fields, so the
   * three shapes are handled without reading structure:
   *   - Prop motive: every checked branch proves the same proposition, so the match itself
   *     witnesses `VProof(motive)` immediately — no branch selection, no thunk.
   *   - Subsingleton large elimination (a single case): reduce only when the scrutinee type's
   *     indices are definitionally diagonal — the analogue of "Eq.rec reduces only on refl".
   *     Reducing on non-diagonal indices would produce a value at the wrong type; this must never
   *     be relaxed.
   *   - Empty elimination, or a stuck/non-diagonal subsingleton: an unblockable NeutralThunk
   *     (proofs never block-and-resume), matching axiom-stuck behavior.
   */
  private def evalProofMatch(m: ETerm.Match, scrut: VProof, env: Env[Value]): Value = {
    val outType = matchOutType(m, scrut, env)
    // Proofs never block-and-resume: the thunk is unblockable.
    def thunk: NeutralThunk = stuckMatchThunk(m, env, outType, None)

    if (Value.isPropositionType(outType)) VProof(outType, thunk)
    else if (m.cases.length == 1) reduceSubsingletonMatch(m.cases.head, scrut, env).getOrElse(thunk)
    else thunk
  }

  /**
   * Large elimination of a proof: the match checker admitted this match only if every non-proof
   * field of the single reachable constructor is forced by the scrutinee type's indices
   * (MatchChecker.allowLargeElimination). Re-derive that forced-field mapping at the actual
   * scrutinee type by Invert-unifying the constructor's result type against it: unification
   * succeeding with every non-proof field solved is exactly "the indices are definitionally
   * diagonal", and the solutions are the field values. Anything less leaves the match stuck.
   */
  private def reduceSubsingletonMatch(branch: ElabAst.Case, scrut: VProof, env: Env[Value]): Option[Value] = {
    val head = env(branch.ctorName) match {
      case h: ConstructorHead => h
      case other              => throw WTF(s"Case head ${branch.ctorName} is not a constructor: $other", Some(branch.span))
    }

    val (freshArgs, resultTy) = BinderOps.freshCtorArgsAndResult(head)

    // Only the constructor's own fresh unknowns are refinable: Invert-mode links are consequences
    // of the type equation, so any solution is index-derived, never invented.
    val refinable = DepSet.unionAll(freshArgs.map(_.synDeps): _*)

    ValueEquivalence.tryUnify(
      resultTy,
      scrut.tpe,
      EqStore.empty.allow(refinable),
      ValueEquivalence.UnifyMode.Invert
    ) match {
      case Left(_) => None
      case Right(store) =>
        val patternArgs = Value.constructorPatternArgs(head, Value.constructorStoredArgs(head, freshArgs))
        val bound = patternArgs.map(arg => ValueOps.materialize(arg, store))
        val unsolved = refinable -- store.solvedIds
        // Proof-typed fields are their own witnesses (their types must still be fully forced,
        // which their synDeps track); any other leftover unknown means the match is stuck.
        if (bound.exists(arg => arg.synDeps.intersects(unsolved))) None
        else Some(evalBranch(branch, bound, env))
    }
  }

  def evalBody(body: ETerm.Body, env: Env[Value]): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      val ascribed = l.ty match {
        case Some(ty) => Value.ascribe(res, evalTypeTerm(ty, curEnv))
        case None     => res
      }
      curEnv.putLocal(l.localRef, ascribed)
    }
    evalTerm(body.res, newEnv)
  }

  case class Worlds(checkContext: TypingContext, runContext: TypingContext) {
    def checkEnv: Env[Value] = checkContext.env
    def runEnv: Env[Value] = runContext.env
  }

  // Publication collapse (proof-collapse.md §4): a global of propositional type is a proof; the
  // constant itself is the witness, so proofs quote back as a reference to their global name.
  private def publishedValue(name: String, value: Value, ty: Value): Value =
    if (Value.isPropositionType(ty)) VProof(ty, VConst(name, Symbol, ty))
    else value

  def evalDecl(decl: Decl, worlds: Worlds): Worlds = {
    decl match {
      case Decl.ConstDecl(isOpaque, name, ty, body, span, isInstance, lazyGlobal) =>
        body match {
          case CoreAst.ConstBody.Builtin(_) =>
            if (isOpaque) throw WTF("Builtin declarations cannot be opaque", Some(span))
            if (isInstance) throw WTF("Builtin declarations cannot be instances", Some(span))
            def value(context: TypingContext): Value = {
              val tyV = TypeChecker.getType(ty, context)
              publishedValue(name, Builtins.instantiate(name, tyV, span), tyV)
            }
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
              publishedValue(name, if (isOpaque) VConst(name, Symbol, checkedTy) else bodyV, checkedTy)
            }
            lazy val runTy = TypeChecker.getType(ty, runContext)
            lazy val runtimeValue = {
              val bodyV =
                if (isOpaque) VConst(name, Symbol, runTy)
                else Value.ascribe(evalTerm(checked.residual, runContext.env), runTy)
              publishedValue(name, bodyV, runTy)
            }
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
        val checkValue = publishedValue(name, VConst(name, Symbol, tyV), tyV)
        val nextCheckContext = worlds.checkContext.putGlobal(name, checkValue, isInstance = isInstance)

        val runtimeTyV = TypeChecker.getType(ty, worlds.runContext)
        val runtimeValue = publishedValue(name, VConst(name, Symbol, runtimeTyV), runtimeTyV)
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
