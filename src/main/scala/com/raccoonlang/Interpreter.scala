package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program}
import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * Interpreter evaluates ElabAst into ordinary WHNF Values in the Env it is given. EqStore-aware reduction is isolated
 * to resolveInEqStore and the materialization helpers in ValueOps.
 */
object Interpreter {
  private def normalizeLevel(l: Level, eqStore: EqStore): Level = {
    val pieces = Vector.newBuilder[Level]
    if (l.c > 0 || l.terms.isEmpty) pieces += Level.const(l.c)
    l.terms.foreach { case (atom, k) =>
      val base = atom match {
        case Level.ParamAtom(id) =>
          eqStore.subst.get(id) match {
            case Some(sol) =>
              eqStore.force(sol) match {
                case next: Level       => normalizeLevel(next, eqStore)
                case Var(_, nextId, _) => Level.mk(nextId)
                case other             => throw NotALevel(other)
              }
            case None => Level.mk(id)
          }
        case Level.IMaxAtom(lhs, rhs) =>
          Level.imax(normalizeLevel(lhs, eqStore), normalizeLevel(rhs, eqStore))
      }
      pieces += Level.addOffset(base, k)
    }
    Level.max(pieces.result())
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

      case l: Level if l.synDeps.intersects(eqStore.solvedIds) => normalizeLevel(l, eqStore)

      case _ => v0
    }
  }

  /**
   * Runtime arguments carry the checker's ascription discipline (checkApplyChecked's verification pass): each arg is
   * retyped at its instantiated binder type, so type-directed work inside the body — implicit reconstruction above all
   * — reads the binder-declared type, never the argument's construction-site type. The two are always defEq (sorts are
   * not cumulative) but need not be structurally identical, and projection is structural: this keeps run-world
   * projection reading exactly the shapes the checker read. Binder types are evaluated against the Pi's own closure —
   * their syntax is valid there, not in the body env the values are later bound into.
   */
  private def ascribeArgs(fnTpe: VPi, args: Vector[Value]): Vector[Value] = {
    if (fnTpe.binders.length != args.length) throw ArityMismatch(fnTpe.binders.length, args.length)
    var tyEnv = fnTpe.env
    fnTpe.binders.zip(args).map { case (binder, value) =>
      val ascribed = value match {
        // Only neutrals carry a rewritable type annotation; skip the binder-type evaluation
        // for values (sorts, levels) whose ascription is the identity.
        case _: UpdatableType => Value.ascribe(value, evalTerm(binder.ty, tyEnv))
        case _                => value
      }
      tyEnv = tyEnv.putLocal(binder.localRef, ascribed)
      ascribed
    }
  }

  private def getEnvWithArgs(fnTpe: VPi, baseEnv: Env, args: Vector[Value]): Env =
    BinderOps.instantiateFull(fnTpe.binders, baseEnv, ascribeArgs(fnTpe, args))

  /**
   * The universe of a Pi, derived from the env it closed over: the binder types' universes are right-folded with imax
   * over the codomain's universe. IMax reduces to Prop for a Prop-valued codomain and to ordinary max for a definitely
   * positive codomain. Computing it per instance means a residual Pi re-evaluated with concrete levels gets the
   * concrete universe, not the declaration-time one.
   */
  private def piClassifier(binders: Vector[ElabAst.Binder], baseEnv: Env, out: ElabAst.Term): VSort = {
    val freshEnv = BinderOps.freshen(binders, baseEnv)
    val outV = evalTerm(out, freshEnv)
    val VSort(outLevel) = TypeChecker.getUniverse(outV)
    if (outLevel == Level.zero) PropTpe
    else {
      val domLevels = binders.map { binder =>
        val VSort(level) = TypeChecker.getUniverse(freshEnv(binder.localRef).tpe)
        level
      }
      val classifier =
        if (Level.isNeverZero(outLevel)) Level.max(domLevels :+ outLevel)
        else domLevels.foldRight(outLevel)(Level.imax)
      VSort(classifier)
    }
  }

  def evalPi(pi: ETerm.Pi, env: Env): VPi = {
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
      pi.binders,
      codomain = env => evalTerm(pi.out, env),
      synDeps.result(),
      id,
      classifier0 = () => piClassifier(pi.binders, closedEnv, pi.out)
    )
  }

  private def evalRef(ref: ETerm.Ref, env: Env): Value = {
    val res = ref match {
      case ETerm.GlobalRef(name, _) => env(name)
      case ETerm.LocalRef(local, _) => env(local)
    }
    res match {
      case h: ConstructorHead if h.totalArity == 0 =>
        Value.canonicalizeProof(Packed.foldCtor(h, Vector.empty, h.tpe).getOrElse(VCtor(h, Vector.empty, h.tpe)))
      case _ => res
    }
  }

  def evalApply(fn: Value, vArgs: Vector[Value]): Value = {
    require(vArgs.nonEmpty, "evalApply requires at least one argument")

    fn match {
      // Stuck-projection heads (StructEta) reduce structurally and bypass Pi dispatch: their
      // recorded type is never consulted, and a resolved base is projected or re-stuck directly.
      case VConst(_, StructField(idx), _) =>
        if (vArgs.length != 1) throw ArityMismatch(1, vArgs.length)
        return StructEta.project(vArgs.head, idx)
      case _ =>
    }

    fn.tpe match {
      case pi: VPi =>
        // Lazy: the VLam branch delegates env construction to runLam.
        lazy val envWithArgs = getEnvWithArgs(pi, pi.env, vArgs)
        fn match {
          case lam: VLam =>
            Packed.runOp(lam, vArgs, () => pi.codomain(envWithArgs)).getOrElse(runLam(lam, vArgs))
          case h: VConst =>
            StructEta.expandIfStruct(Value.canonicalizeProof(VApp(h, vArgs, pi.codomain(envWithArgs))))
          case h: ConstructorHead =>
            val resultTy = pi.codomain(envWithArgs)
            val storedArgs = Value.constructorStoredArgs(h, vArgs)
            Value.canonicalizeProof(Packed.foldCtor(h, storedArgs, resultTy).getOrElse(VCtor(h, storedArgs, resultTy)))
          case blocker @ Blocker(blockerId) =>
            StructEta.expandIfStruct(
              Value.canonicalizeProof(VBlockedApp(blocker, vArgs, pi.codomain(envWithArgs), blockerId))
            )
          case _ => throw CannotApplyNonFunction(fn)
        }
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }
  }

  private def evalApplyTerm(fn: ElabAst.Term, args: Vector[ElabAst.Term], env: Env): Value = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    if (vArgs.isEmpty) throw CannotApplyNonFunction(vf.tpe)
    evalApply(vf, reconstructImplicits(vf, vArgs, fn.span))
  }

  private def valueName(v: Value): String =
    v match {
      case VConst(name, _, _)              => name
      case VLam(_, ValueId.Const(name), _) => name
      case head: ConstructorHead           => head.name
      case _                               => "function"
    }

  /**
   * Checked application syntax — source-checked and quoted alike — carries only the explicit args; the implicit ones
   * are re-derived here by running their projection specs against the provided args, exactly as application checking
   * did (Projection.project is the shared implementation).
   */
  private def reconstructImplicits(fn: Value, vArgs: Vector[Value], span: Span): Vector[Value] =
    fn.tpe match {
      case pi: VPi if pi.binders.exists(_.isImplicit) =>
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

  def evalLam(l: ETerm.Lam, vpi: VPi, env: Env): Value = {
    // The body has already checked (including termination). Do not even build a closure for a
    // proof-valued lambda: its canonical eta-lambda depends only on the checked Pi, and the source
    // body would be discarded immediately.
    if (vpi.isPropValued) Value.canonicalizeProof(VProof(vpi))
    else {
      val capturedRefs = CapturedRefs.getCapturedRefs(l, env)
      val closedEnv = env.closeForEval(capturedRefs)
      val id = l.name match {
        case Some(funcName) => ValueId.Const(funcName)
        case None           => ValueId.LocalId(l.nodeId, closedEnv.locals.values.toVector)
      }
      Value.canonicalizeProof(VLam(vpi, id, LamBody.Core(l, closedEnv)))
    }
  }

  def runLam(lam: VLam, args: Vector[Value]): Value = {
    lam.body match {
      case LamBody.Native(run, nativeEnv, _) => run(args, nativeEnv)
      case LamBody.ProofEta =>
        val ascribedArgs = ascribeArgs(lam.tpe, args)
        val piEnv = BinderOps.instantiateFull(lam.tpe.binders, lam.tpe.env, ascribedArgs)
        Value.canonicalizeProof(VProof(lam.tpe.codomain(piEnv)))
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

  private def evalLam(l: ETerm.Lam, env: Env): Value = {
    val vpi = evalPi(l.ty, env)
    evalLam(l, vpi, env)
  }

  def getLevel(v: Value): Level =
    Level.fromValue(v).getOrElse(throw NotALevel(v))

  def evalTerm(term: ElabAst.Term, env: Env): Value = {
    try {
      term match {
        case ETerm.NatLit(value, _) => Packed.evalNatLit(value, env)
        case ETerm.Proof(tpe, _)    => Value.canonicalizeProof(VProof(evalTerm(tpe, env)))
        case ref: ETerm.Ref         => evalRef(ref, env)
        case ETerm.App(fn, args, _) => evalApplyTerm(fn, args, env)
        case pi: ETerm.Pi           => evalPi(pi, env)
        case l: ETerm.Lam           => evalLam(l, env)
        case m: ETerm.Match         => evalMatch(m, env)
        case b: ETerm.Body          => evalBody(b, env)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw e.withSpan(term.span)
    }
  }

  private def evalMatch(m: ETerm.Match, env: Env): Value = {
    val scrut = evalTerm(m.scrut, env)
    val (ctorName, args) = scrut match {
      case VCtor(head, storedArgs, _) => (head.name, storedArgs)
      case p: VPacked                 => p.codec.decodeHead(p)
      case proof: VProof              => return evalProofMatch(m, proof, env)
      case other                      =>
        // We are either blocked or stuck
        val blockerId = other match {
          case Blocker(id) => Some(id)
          case _           => None
        }
        return StructEta.expandIfStruct(
          Value.canonicalizeProof(stuckMatchThunk(m, env, matchOutType(m, scrut, env), blockerId))
        )
    }

    val branch =
      m.cases.find(c => c.ctorName == ctorName).getOrElse(throw UnknownConstructor(ctorName, "", Some(m.span)))
    evalBranch(branch, args, env)
  }

  private def matchOutType(m: ETerm.Match, scrut: Value, env: Env): Value =
    m.motive match {
      case Some(motive) => evalTerm(motive, env)
      case None         => scrut.tpe
    }

  private def stuckMatchThunk(m: ETerm.Match, env: Env, outType: Value, blockerId: Option[VarId]): NeutralThunk = {
    val closedEnv = env.closeForEval(CapturedRefs.getCapturedRefs(m, env))
    NeutralThunk(m, closedEnv, ValueId.LocalId(m.nodeId, closedEnv.locals.values.toVector), outType, blockerId)
  }

  private def evalBranch(branch: ElabAst.Case, args: Vector[Value], env: Env): Value = {
    if (args.length != branch.argRefs.length)
      throw ArityMismatch(branch.argRefs.length, args.length, Some(branch.span))
    val newEnv = args.zip(branch.argRefs).foldLeft(env) { case (curEnv, (argV, argRef)) =>
      argRef match {
        case Some(ref) => curEnv.putLocal(ref, Value.canonicalizeProof(argV))
        case None      => curEnv
      }
    }
    evalTerm(branch.body, newEnv)
  }

  /**
   * Elimination of an erased proof (docs/proof-collapse.md). A Prop-valued result can erase immediately. A data-valued
   * result is stuck: reconstructible propositions have already canonicalized to `VCtor` and use the ordinary path.
   */
  private def evalProofMatch(m: ETerm.Match, scrut: VProof, env: Env): Value = {
    val outType = matchOutType(m, scrut, env)
    if (Value.isPropositionType(outType)) Value.canonicalizeProof(VProof(outType))
    else StructEta.expandIfStruct(stuckMatchThunk(m, env, outType, None))
  }

  def evalBody(body: ETerm.Body, env: Env): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      val ascribed = l.ty match {
        case Some(ty) => Value.ascribe(res, evalTerm(ty, curEnv))
        case None     => res
      }
      curEnv.putLocal(l.localRef, ascribed)
    }
    evalTerm(body.res, newEnv)
  }

  // Proof publication (proof-collapse.md): exact type alone chooses a reconstructed constructor,
  // a proof eta-lambda, or `VProof`; transparency and the value's origin are irrelevant.
  // Its data-level dual: a symbolic global (opaque def, axiom) of struct type publishes in
  // constructor form, its fields the stuck projections of the constant (StructEta).
  private def publishedValue(name: String, value: Value, ty: Value): Value =
    if (Value.isPropositionType(ty)) Value.canonicalizeProof(value)
    else StructEta.expandIfStruct(value)

  // A declaration is checked exactly once; the value the checker produced IS the published value.
  // There is no separate run world: once a definition has made it into the env, it is trusted.
  def evalDecl(decl: Decl, env: Env): Env = evalDecl(decl, env, allowReservedNativeDefinitions = false)

  private def evalDecl(decl: Decl, env: Env, allowReservedNativeDefinitions: Boolean): Env = {
    if (!allowReservedNativeDefinitions) {
      val publishedNames = decl match {
        case Decl.ConstDecl(_, name, _, _, _, _) => Vector(name)
        case Decl.AxiomDecl(name, _, _)          => Vector(name)
        case d: Decl.InductiveDecl               => d.header.name +: d.ctors.map(_.canonicalName)
      }
      publishedNames.find(Packed.reservedNames).foreach { name =>
        throw ReservedKernelName(name, Some(decl.span))
      }
    }
    decl match {
      case Decl.ConstDecl(isOpaque, name, ty, body, span, lazyGlobal) =>
        body match {
          case CoreAst.ConstBody.Builtin(_) =>
            if (isOpaque) throw WTF("Builtin declarations cannot be opaque", Some(span))
            def value: Value = {
              val tyV = TypeChecker.getType(ty, env)
              publishedValue(name, Builtins.instantiate(name, tyV, span), tyV)
            }
            if (lazyGlobal) env.putLazyGlobal(name, () => value)
            else env.putGlobal(name, value)

          case CoreAst.ConstBody.TermBody(term) =>
            lazy val value = {
              val checkedTy = TypeChecker.getType(ty, env)
              // Bidirectional: bare-body defs get the same subsumption (eta-adaptation of
              // polymorphic functions) as let bindings.
              val checked = TypeChecker.checkTerm(term, checkedTy, env)
              val bodyV = Value.ascribe(checked.value, checkedTy)
              publishedValue(name, if (isOpaque) VConst(name, Symbol, checkedTy) else bodyV, checkedTy)
            }
            if (lazyGlobal) env.putLazyGlobal(name, () => value)
            else env.putGlobal(name, value)
        }

      case Decl.AxiomDecl(name, ty, _) =>
        val tyV = TypeChecker.getType(ty, env)
        env.putGlobal(name, publishedValue(name, VConst(name, Symbol, tyV), tyV))

      case d: Decl.InductiveDecl => InductiveChecks.evalInductiveDecl(d, env)
    }
  }

  def run(p: Program, prelude: Prelude.Config = Prelude.default): Option[Value] = {
    val env =
      p.decls.foldLeft(prelude.checkedEnv) { case (curEnv, decl) => evalDecl(decl, curEnv) }
    p.body.map { b =>
      TypeChecker.checkTerm(b, env).value
    }
  }

  private[raccoonlang] def buildPreludeEnv(core: Program, allowReservedNativeDefinitions: Boolean): Env = {
    val baseEnv =
      Env.empty
        .putGlobal("Type", TypeTpe)
        .putGlobal("Level", LevelTpe)
        .putGlobal("Level.zero", Level.zero)
        .putGlobal("Level.one", Level.one)
        .putGlobal("Prop", PropTpe)

    val built = core.decls.foldLeft(baseEnv) { case (curEnv, decl) =>
      evalDecl(decl, curEnv, allowReservedNativeDefinitions)
    }
    if (allowReservedNativeDefinitions) Packed.validateNatFamily(built)
    built
  }
}
