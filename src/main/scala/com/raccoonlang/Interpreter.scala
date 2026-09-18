package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program}
import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * Interpreter evaluates CoreAst into ordinary WHNF Values in the Env it is given. EqStore-aware reduction is isolated
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
   * Continues the reduction of v if any dependency that blocks it has been solved in EqStore. The default call (if v
   * cannot be further reduced) is a fast empty/intersection check, so callers may use it defensively.
   */
  private[raccoonlang] def resolveInEqStore(v: Value, eqStore: EqStore): Value = {
    val v0 = eqStore.force(v)
    v0 match {
      case Blocked(blockedOn) if blockedOn.intersects(eqStore.solvedIds) =>
        v0 match {
          case VBlockedApp(h, args, tpe, _) =>
            val h0 = ValueOps.materialize(resolveInEqStore(h, eqStore), eqStore)
            val materializedArgs = args.map(arg => ValueOps.materialize(arg, eqStore))
            h0 match {
              case lam: VLam =>
                val res = runLam(lam, materializedArgs)
                resolveInEqStore(res, eqStore)
              case nextHead @ Blocker(nextBlockedOn) =>
                VBlockedApp(nextHead, args, tpe, nextBlockedOn)
              case other =>
                resolveInEqStore(evalApply(other, materializedArgs), eqStore)
            }
          case vm: NeutralThunk => resolveInEqStore(forceThunk(vm, eqStore), eqStore)
          case _                => throw WTF(s"Blocked extractor matched unexpected value $v0")
        }

      case l: Level if l.synDeps.intersects(eqStore.solvedIds) => normalizeLevel(l, eqStore)

      case _ => v0
    }
  }

  /**
   * Arguments are bound exactly as supplied: a value's type annotation is what it was created with, and no site
   * rewrites it. Binder types are evaluated against the Pi's own closure — their syntax is valid there, not in the body
   * env the values are later bound into.
   */
  private def getEnvWithArgs(fnTpe: VPi, baseEnv: Env, args: Vector[Value]): Env =
    BinderOps.instantiateFull(fnTpe.binders, baseEnv, args)

  /**
   * The universe of a Pi, derived from the env it closed over: the binder types' universes are right-folded with imax
   * over the codomain's universe. IMax reduces to Prop for a Prop-valued codomain and to ordinary max for a definitely
   * positive codomain. Computing it per instance means a residual Pi re-evaluated with concrete levels gets the
   * concrete universe, not the declaration-time one.
   */
  private[raccoonlang] def piClassifierFromChecked(
      binders: Vector[CoreAst.Binder],
      freshEnv: Env,
      outV: Value
  ): VSort = {
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

  /** Cache only proposition classifications that cannot change when level parameters are instantiated. */
  private[raccoonlang] def stablePiPropClassification(outV: Value): Option[Boolean] = {
    val VSort(outLevel) = TypeChecker.getUniverse(outV)
    if (outLevel == Level.zero) Some(true)
    else if (Level.isNeverZero(outLevel)) Some(false)
    else None
  }

  private def piClassifier(binders: Vector[CoreAst.Binder], baseEnv: Env, out: CoreAst.Term): VSort = {
    val freshEnv = BinderOps.freshen(binders, baseEnv)
    piClassifierFromChecked(binders, freshEnv, evalTerm(out, freshEnv))
  }

  private[raccoonlang] def evalPi(pi: CTerm.Pi, env: Env): VPi = {
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
      classifier0 = () => piClassifier(pi.binders, closedEnv, pi.out),
      knownPropValued = pi.knownPropValued
    )
  }

  private def evalRef(ref: CTerm.Ref, env: Env): Value = {
    val res = ref match {
      case CTerm.GlobalRef(name, _) => env(name)
      case CTerm.LocalRef(local, _) => env(local)
    }
    res match {
      case h: ConstructorHead if h.totalArity == 0 =>
        Value.canonicalizeProof(Packed.foldCtor(h, Vector.empty, h.tpe).getOrElse(VCtor(h, Vector.empty, h.tpe)))
      case _ => res
    }
  }

  private[raccoonlang] def evalApply(fn: Value, vArgs: Vector[Value]): Value = {
    fn.tpe match {
      case pi: VPi =>
        // Grouping is part of a function type's identity, so an application supplies exactly this
        // Pi's own binders. A nested group is reached by a second application, which arrives here
        // as its own call. Keep this boundary checked because native lambdas bypass Core evaluation.
        if (vArgs.length != pi.binders.length)
          throw ArityMismatch(pi.binders.length, vArgs.length)
        // Lazy: the VLam branch delegates env construction to runLam.
        lazy val envWithArgs = getEnvWithArgs(pi, pi.env, vArgs)
        fn match {
          case lam: VLam =>
            runLam(lam, vArgs)
          case h: ConstructorHead =>
            val resultTy = pi.codomain(envWithArgs)
            val storedArgs = Value.constructorStoredArgs(h, vArgs)
            Value.canonicalizeProof(Packed.foldCtor(h, storedArgs, resultTy).getOrElse(VCtor(h, storedArgs, resultTy)))
          // Every non-reducing head builds one new application layer over itself. An existing
          // neutral stays the head rather than being flattened into the new spine: flattening
          // would destroy positional-projection arity. A blocked head propagates its blockers,
          // and any other head is unblocked.
          case head @ (_: VConst | _: VApp | _: NeutralThunk | _: Var) =>
            val blockedOn = Blocker.unapply(head).getOrElse(DepSet.empty)
            Value.canonicalizeProof(VApp(head, vArgs, pi.codomain(envWithArgs), blockedOn))
          case _ => throw CannotApplyNonFunction(fn)
        }
      case _ => throw CannotApplyNonFunction(fn.tpe)
    }
  }

  private def evalApplyTerm(fn: CoreAst.Term, args: Vector[CoreAst.Term], env: Env): Value = {
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
   * Checked application syntax carries only the explicit args; the implicit ones are re-derived here by running their
   * projection specs against the provided args, exactly as application checking did (Projection.project is the shared
   * implementation).
   */
  private def reconstructImplicits(fn: Value, vArgs: Vector[Value], span: Span): Vector[Value] =
    fn.tpe match {
      case pi: VPi if pi.binders.exists(_.isImplicit) =>
        if (vArgs.length != pi.numExplicit) throw ArityMismatch(pi.numExplicit, vArgs.length, Some(span))
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

  private[raccoonlang] def evalLam(l: CTerm.Lam, vpi: VPi, env: Env): Value = {
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

  private[raccoonlang] def runLam(lam: VLam, args: Vector[Value]): Value = {
    // Arguments are bound as supplied. A lambda's Pi is the one it was created with, so its binders
    // are exactly the ones its body expects.
    lazy val piEnv = BinderOps.instantiateFull(lam.tpe.binders, lam.tpe.env, args)

    lam.body match {
      case LamBody.Native(run, nativeEnv, _) => run(args, nativeEnv)
      case LamBody.ProofEta =>
        Value.canonicalizeProof(VProof(lam.tpe.codomain(piEnv)))
      case LamBody.Core(term, coreEnv) =>
        val bodyEnv = BinderOps.instantiateFull(lam.tpe.binders, coreEnv, args)

        val recurEnv = term.recursivePeers.foldLeft(bodyEnv) { case (current, (ref, name)) =>
          // A singleton's self reference is this very lambda (possibly a materialized copy), never a
          // same-named global; group peers resolve through the group's lazy bindings.
          val peer =
            if (term.recursivePeers.length == 1 && term.name.contains(name)) lam
            else
              coreEnv.globals.get(name).map(_.value(coreEnv)).getOrElse {
                throw WTF(s"Checked recursive peer $name is absent from its group", Some(term.span))
              }
          current.putLocal(ref, peer)
        }
        evalTerm(term.body, recurEnv)
    }
  }

  private def forceThunk(thunk: NeutralThunk, eqStore: EqStore): Value =
    evalMatch(thunk.term, ValueOps.materializeEnv(thunk.env, eqStore))

  private def evalLam(l: CTerm.Lam, env: Env): Value = {
    val vpi = evalPi(l.ty, env)
    evalLam(l, vpi, env)
  }

  private[raccoonlang] def getLevel(v: Value): Level =
    Level.fromValue(v).getOrElse(throw NotALevel(v))

  private[raccoonlang] def evalTerm(term: CoreAst.Term, env: Env): Value = {
    try {
      term match {
        case CTerm.NatLit(value, _)   => Packed.evalNatLit(value, env)
        case CTerm.StrLit(scalars, _) => Packed.evalStrLit(scalars, env)
        case ref: CTerm.Ref           => evalRef(ref, env)
        case CTerm.App(fn, args, _)   => evalApplyTerm(fn, args, env)
        case pi: CTerm.Pi             => evalPi(pi, env)
        case l: CTerm.Lam             => evalLam(l, env)
        case m: CTerm.Match           => evalMatch(m, env)
        case b: CTerm.Body            => evalBody(b, env)
        // Named field syntax is resolved to a selector application by checkSelect, so a Select can
        // only reach evaluation if something published unchecked syntax.
        case CTerm.Select(_, field, span) =>
          throw WTF(s"Unresolved field selection .$field reached evaluation", Some(span))
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw e.withSpan(term.span)
    }
  }

  private def evalMatch(m: CTerm.Match, env: Env): Value = {
    val scrut = evalTerm(m.scrut, env)
    val (ctorName, args) = scrut match {
      case ConstructorForm(name, storedArgs) => (name, storedArgs)
      case proof: VProof                     => return evalProofMatch(m, proof, env)
      case other                             =>
        // Structure eta (rule 1): a neutral at an eta-eligible struct type has an eta view, so the
        // single branch fires against its virtual fields instead of sticking. The canonical
        // projection terms this builds are matches whose body is a bare pattern variable, and
        // `fieldProjection` builds their thunks without evaluating them, so the rule cannot cycle.
        StructEta.fields(other) match {
          case Some(etaFields) =>
            val branch = m.cases match {
              case Vector(single) => single
              case _              => throw WTF(s"Eta-eligible struct match has ${m.cases.length} cases", Some(m.span))
            }
            return evalBranch(branch, etaFields, env)
          case None =>
        }
        // We are either blocked or stuck
        val headBlockers = other match {
          case Blocker(blockedOn) => blockedOn
          case _                  => DepSet.empty
        }
        val blockedOn = headBlockers ++ typeCollapseDeps(other.tpe)
        return Value.canonicalizeProof(stuckMatchThunk(m, env, matchOutType(m, scrut, env), blockedOn))
    }

    val branch =
      m.cases.find(c => c.ctorName == ctorName).getOrElse(throw UnknownConstructor(ctorName, "", Some(m.span)))
    evalBranch(branch, args, env)
  }

  private def matchOutType(m: CTerm.Match, scrut: Value, env: Env): Value =
    m.motive match {
      case Some(motive) => evalTerm(motive, env)
      case None         => scrut.tpe
    }

  private[raccoonlang] def typeCollapseDeps(tpe: Value): DepSet = {
    val classifierLevel = TypeChecker.getUniverse(tpe).level
    if (Level.isNeverZero(classifierLevel)) DepSet.empty else classifierLevel.synDeps
  }

  private def stuckMatchThunk(m: CTerm.Match, env: Env, outType: Value, blockedOn: DepSet): NeutralThunk = {
    val closedEnv = env.closeForEval(CapturedRefs.getCapturedRefs(m, env))
    NeutralThunk(m, closedEnv, ValueId.LocalId(m.nodeId, closedEnv.locals.values.toVector), outType, blockedOn)
  }

  private[raccoonlang] def evalBranch(branch: CoreAst.Case, args: Vector[Value], env: Env): Value = {
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
   * Elimination of an erased proof (docs/kernel.md#proofs-and-elimination). A Prop-valued result can erase immediately.
   * A data-valued result is stuck: reconstructible propositions have already canonicalized to `VCtor` and use the
   * ordinary path.
   */
  private def evalProofMatch(m: CTerm.Match, scrut: VProof, env: Env): Value = {
    val outType = matchOutType(m, scrut, env)
    if (Value.isPropositionType(outType)) Value.canonicalizeProof(VProof(outType))
    else stuckMatchThunk(m, env, outType, scrut.tpe.synDeps)
  }

  private[raccoonlang] def evalBody(body: CTerm.Body, env: Env): Value = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      curEnv.putLocal(l.localRef, evalTerm(l.value, curEnv))
    }
    evalTerm(body.res, newEnv)
  }

  // Proof publication (docs/kernel.md#proofs-and-elimination): exact type alone chooses a reconstructed constructor,
  // a proof eta-lambda, or `VProof`; transparency and the value's origin are irrelevant. Data has
  // no such policy: an opaque def or axiom of struct type publishes as the plain symbol, and
  // structure eta reaches it through the rules rather than through its representation.
  private def publishedValue(value: Value, ty: Value): Value =
    if (Value.isPropositionType(ty)) Value.canonicalizeProof(value)
    else value

  // A declaration is checked exactly once; the value the checker produced IS the published value.
  // There is no separate run world: once a definition has made it into the env, it is trusted.
  private[raccoonlang] def evalDecl(decl: Decl, env: Env): Env = evalDecl(decl, env, trusted = false)

  /**
   * `trusted` is the one bootstrap privilege: a prelude may declare builtin bodies and the native Nat operations. A
   * program cannot, so nothing it declares can acquire kernel semantics it did not write.
   */
  private[raccoonlang] def evalDecl(decl: Decl, env: Env, trusted: Boolean): Env =
    decl match {
      case Decl.ConstDecl(isOpaque, name, ty, body, span) =>
        body match {
          case CoreAst.ConstBody.Builtin(_) =>
            if (isOpaque) throw WTF("Builtin declarations cannot be opaque", Some(span))
            if (!trusted) throw ReservedKernelName(name, Some(span))
            val tyV = TypeChecker.getType(ty, env)
            env.putGlobal(name, publishedValue(Builtins.instantiate(name, tyV, span), tyV))

          case CoreAst.ConstBody.TermBody(term) =>
            val checkedTy = TypeChecker.getType(ty, env)
            // Bidirectional: bare-body defs get the same subsumption (eta-adaptation of
            // polymorphic functions) as let bindings. The declared type is also syntax valid here —
            // a decl's type mentions no locals — so a motive-less `match` body can residualize it.
            val checked =
              TypeChecker.checkTerm(term, TypeChecker.Expected(checkedTy, Some(ty)), env)
            val value = if (isOpaque) VConst(name, Symbol, checkedTy) else checked.value
            val published =
              if (trusted && Packed.opNames(name)) Packed.nativeOp(name, value, env)
              else publishedValue(value, checkedTy)
            env.putGlobal(name, published)
        }

      case Decl.AxiomDecl(name, ty, _) =>
        val tyV = TypeChecker.getType(ty, env)
        env.putGlobal(name, publishedValue(VConst(name, Symbol, tyV), tyV))

      case d: Decl.InductiveDecl =>
        InductiveChecks.evalInductiveBlock(Decl.InductiveBlock(Vector(d), d.span), env)

      case b: Decl.InductiveBlock => InductiveChecks.evalInductiveBlock(b, env)

      case b: Decl.RecursiveDefBlock =>
        b.definitions.foreach { definition =>
          if (env.globals.contains(definition.name)) throw AlreadyDefined(definition.name)
          if (definition.name == "_") throw WTF("Wildcards not allowed in global names", Some(definition.span))
        }
        val checked = TypeChecker.checkRecursiveDefBlock(b, env)
        env.putRecursiveGroup(
          checked.map(_.name),
          groupEnv =>
            checked.map { definition =>
              evalLam(definition.residual, definition.vpi, groupEnv) match {
                case lambda: VLam => lambda
                case other        => throw WTF(s"Checked recursive definition ${definition.name} produced $other")
              }
            }
        )
    }

  /** Execute a checked program. Checking and declaration publication have already happened. */
  def run(program: Execution.CheckedProgram): Option[Value] = program.result

  /** Compatibility entry point for implementation code and same-package kernel tests. */
  private[raccoonlang] def run(p: Program, prelude: Prelude.Config = Prelude.default): Option[Value] =
    TypeChecker.checkRaw(p, prelude)

  private[raccoonlang] val preludeInitialEnv: Env =
    Env.empty
      .putGlobal("Type", TypeTpe)
      .putGlobal("Level", LevelTpe)
      .putGlobal("Level.zero", Level.zero)
      .putGlobal("Level.one", Level.one)
      .putGlobal("Prop", PropTpe)

  private[raccoonlang] def addPreludeDecl(env: Env, decl: Decl): Env = evalDecl(decl, env, trusted = true)

  /**
   * Install the native literal layouts of a completed prelude. A prelude that declares `Nat` or `String` must present
   * the exact checked source layout, so a malformed representation is rejected rather than silently left without
   * literals. Validation failure rejects the candidate without mutating the environment the declarations were streamed
   * into.
   */
  private[raccoonlang] def finishPrelude(env: Env): Env = {
    val withNat =
      if (env.nativeLiterals.natLayout.isEmpty && env.globals.contains(NatCodec.familyName))
        env.installNatLayout(Packed.validateNatFamily(env))
      else env
    if (withNat.nativeLiterals.stringLayout.isEmpty && withNat.globals.contains("String"))
      withNat.installStringLayout(Packed.validateStringLayout(withNat))
    else withNat
  }

  private[raccoonlang] def buildPreludeEnv(core: Program): Env =
    finishPrelude(core.decls.foldLeft(preludeInitialEnv)(addPreludeDecl))
}
