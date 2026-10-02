package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program}
import com.raccoonlang.CoreAst.{Term => CTerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.annotation.tailrec

/**
 * Interpreter evaluates CoreAst into ordinary WHNF Values in the Env it is given. EqStore-aware reduction is isolated
 * to resolveInEqStore and the materialization helpers in ValueOps.
 */
object Interpreter {
  private def normalizeLevel(l: Level, eqStore: EqStore): Level = {
    val pieces = Vector.newBuilder[Level]
    if (l.c > 0 || l.terms.isEmpty) pieces += Level.const(l.c)
    l.terms.foreach { case (atom, k) =>
      val base = eqStore.subst.get(atom) match {
        case Some(sol) =>
          eqStore.force(sol) match {
            case next: Level => normalizeLevel(next, eqStore)
            case other       => wtf(s"Level variable $atom solved to the non-level $other")
          }
        case None => Level.mk(atom)
      }
      pieces += Level.addOffset(base, k)
    }
    Level.max(pieces.result())
  }

  /** The solution of a solved kind or lifetime variable, which refinement links only to a normal form of its own. */
  private def solvedParameter(id: VarId, eqStore: EqStore): Option[Value] = eqStore.subst.get(id).map(eqStore.force)

  private def normalizeKind(k: Kind, eqStore: EqStore): Kind = {
    val pieces = Vector.newBuilder[Kind]
    k.vars.foreach { id =>
      pieces += (solvedParameter(id, eqStore) match {
        case Some(next: Kind) => normalizeKind(next, eqStore)
        case Some(other)      => wtf(s"Kind variable $id solved to the non-kind $other")
        case None             => Kind.variable(id)
      })
    }
    if (k.isLin) Kind.lin else Kind.join(pieces.result())
  }

  private def normalizeLifetime(l: Lifetime, eqStore: EqStore): Lifetime = {
    val pieces = Vector.newBuilder[Lifetime]
    l.vars.foreach { id =>
      pieces += (solvedParameter(id, eqStore) match {
        case Some(next: Lifetime) => normalizeLifetime(next, eqStore)
        case Some(other)          => wtf(s"Lifetime variable $id solved to the non-lifetime $other")
        case None                 => Lifetime.variable(id)
      })
    }
    Lifetime.union(pieces.result())
  }

  /**
   * Continues the reduction of v if any dependency that blocks it has been solved in EqStore. The default call (if v
   * cannot be further reduced) is a fast empty/intersection check, so callers may use it defensively.
   */
  private[raccoonlang] def resolveInEqStore(v: Value, eqStore: EqStore): Value = {
    val v0 = eqStore.force(v)
    val needsResolution =
      v0 match {
        case Blocked(blockedOn) => blockedOn.intersects(eqStore.solvedIds)
        case l: Level           => l.synDeps.intersects(eqStore.solvedIds)
        case k: Kind            => k.synDeps.intersects(eqStore.solvedIds)
        case l: Lifetime        => l.synDeps.intersects(eqStore.solvedIds)
        case _                  => false
      }
    if (needsResolution) resolveInEqStore(v0, ValueOps.newMaterializer(eqStore)) else v0
  }

  /** Internal recursive resolver; one materialization session follows all reductions and forced thunks. */
  private[raccoonlang] def resolveInEqStore(v: Value, materializer: ValueOps.Materializer): Value = {
    val eqStore = materializer.eqStore
    val v0 = eqStore.force(v)
    v0 match {
      case Blocked(blockedOn) if blockedOn.intersects(eqStore.solvedIds) =>
        v0 match {
          // Reapplied to its arguments as stored, which forces no evidence, as applying does not. Its evidence is
          // deferred afresh at the head it now has, so that the head and the other arguments still determine it.
          case app: VApp =>
            val h0 = materializer.materialize(resolveInEqStore(app.head, materializer))
            val materializedArgs =
              evidenceDeferredAt(h0, app.storedArgs).map(materializer.materializeArgument)
            h0 match {
              case lam: VLam =>
                val res = runLam(lam, materializedArgs)
                resolveInEqStore(res, materializer)
              case nextHead @ Blocker(nextBlockedOn) =>
                VBlockedApp(nextHead, materializedArgs, materializer.materialize(app.tpe), nextBlockedOn)
              case other =>
                resolveInEqStore(evalApply(other, materializedArgs), materializer)
            }
          case vm: NeutralThunk => resolveInEqStore(forceThunk(vm, materializer), materializer)
          case _                => wtf(s"Blocked extractor matched unexpected value $v0")
        }

      case l: Level if l.synDeps.intersects(eqStore.solvedIds)    => normalizeLevel(l, eqStore)
      case k: Kind if k.synDeps.intersects(eqStore.solvedIds)     => normalizeKind(k, eqStore)
      case l: Lifetime if l.synDeps.intersects(eqStore.solvedIds) => normalizeLifetime(l, eqStore)

      case _ => v0
    }
  }

  /**
   * Arguments are bound exactly as supplied: a value's type annotation is what it was created with, and no site
   * rewrites it. Binder types are evaluated against the Pi's own closure — their syntax is valid there, not in the body
   * env the values are later bound into.
   */
  private def getEnvWithArgs(fnTpe: VPi, baseEnv: Env, args: Vector[Value]): Env =
    BinderOps.instantiateFullRuntime(fnTpe.binders, fnTpe.runtimeSlotLayout, baseEnv, args)

  /**
   * A Pi into Prop is impredicative and unrestricted; a data Pi takes the maximum of its domain and codomain levels.
   * Proposition domains contribute zero. Scope joins the closure, mentioned captures, domains and codomain, less the
   * lifetimes supplied by this binder group. A level binder makes the Pi Large.
   */
  private[raccoonlang] def piClassifierFromChecked(
      binders: Vector[CoreAst.Binder],
      freshEnv: Env,
      outV: Value,
      closureKind: Kind,
      closureScope: Lifetime,
      mentionedScope: Lifetime
  ): Classifier = {
    val freshValues = binders.map(binder => freshEnv(binder.localRef))
    if (Sorts.isProposition(outV) && !closureKind.isUnr)
      fail(KindExceeded("Proposition-valued function", Kind.unr, ContainedPart.Field("codomain", outV), closureKind))
    if (freshValues.exists(_.tpe eq LevelTpe)) Large
    else {
      val outSort = TypeChecker.getUniverse(outV)
      val domSorts = freshValues.flatMap { fresh =>
        fresh.tpe match {
          case _: ParameterTpe => None
          case tpe             => Some(TypeChecker.getUniverse(tpe))
        }
      }
      // A lifetime binder enters as its own variable, which the caller supplies.
      val ownLifetimes = freshValues.collect { case lifetime: Lifetime => lifetime.vars }.foldLeft(DepSet.empty)(_ ++ _)
      val scope =
        Lifetime.less(
          Lifetime.union(closureScope +: mentionedScope +: domSorts.map(_.scope) :+ outSort.scope),
          ownLifetimes
        )
      if (Sorts.isProp(outSort)) Sorts.prop(scope)
      else Sorts.sort(Level.max(domSorts.map(_.level) :+ outSort.level), closureKind, scope)
    }
  }

  private def piClassifier(
      binders: Vector[CoreAst.Binder],
      baseEnv: Env,
      out: CoreAst.Term,
      closureKind: Kind,
      closureScope: Lifetime,
      mentionedScope: Lifetime
  ): Classifier = {
    val freshEnv = BinderOps.freshen(binders, baseEnv)
    piClassifierFromChecked(binders, freshEnv, evalTerm(out, freshEnv), closureKind, closureScope, mentionedScope)
  }

  /**
   * A checked closure field, where its function type stands: a written one is its expression's value, and a lambda's
   * derived one is what its captures derive there (spec §8).
   */
  private def evalClosureField[P <: Value](field: CoreAst.ClosureField, part: Sorts.Field[P], env: Env): P =
    field match {
      case CoreAst.ClosureField.Written(term)     => part.normalForm(evalTerm(term, env))
      case CoreAst.ClosureField.Derived(captures) => derivedField(part, captures, env)
      case CoreAst.ClosureField.Omitted           => wtf("An omitted closure field reached evaluation before checking")
    }

  /**
   * An axiom's head. One whose type, past all its binder groups, is a sort is a type former, whose arguments projection
   * reads; it names each lifetime parameter in its declared scope, as a family does (spec §5.1).
   */
  private def axiomHead(name: String, tpe: Value): ConstType = {
    @tailrec
    def telescope(parameters: Vector[(CoreAst.Binder, Value)], tpe: Value): ConstType =
      tpe match {
        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          telescope(parameters ++ pi.binders.map(binder => binder -> freshEnv(binder.localRef)), pi.codomain(freshEnv))
        case sort: VSort =>
          Sorts.requireNamesLifetimeParameters(s"Axiom $name", sort.scope, parameters)
          TypeFormer
        case _ => Symbol
      }
    telescope(Vector.empty, tpe)
  }

  private[raccoonlang] def evalPi(pi: CTerm.Pi, env: Env): VPi = {
    val capturedRefs = CapturedRefs.getCapturedRefs(pi, env)
    val closedEnv = env.closeForEval(capturedRefs)
    val captureVals = closedEnv.locals.values.toVector
    val id = ValueId.LocalId(pi.id, captureVals)
    val closureKind = evalClosureField(pi.closure.kind, Sorts.KindField, env)
    val closureScope = evalClosureField(pi.closure.scope, Sorts.ScopeField, env)
    // The Pi's own binders are not in `env`, so these are the locals bound outside it that its code mentions.
    val mentionedScope = derivedField(Sorts.ScopeField, (pi.codeRefs intersect env.localRefs).toVector, env)

    val synDeps = DepSet.newBuilder
    captureVals.foreach { v =>
      synDeps.unionInPlace(v.synDeps)
    }
    synDeps.unionInPlace(closureKind.synDeps)
    synDeps.unionInPlace(closureScope.synDeps)
    synDeps.unionInPlace(mentionedScope.synDeps)

    val codomain = new CheckedPiCodomain(pi.binders, pi.codomainIndependent) {
      override def apply(env: Env): Value = evalTerm(pi.out, env)
    }

    VPi(
      closedEnv,
      pi.binders,
      codomain,
      closureKind,
      closureScope,
      mentionedScope,
      synDeps.result(),
      id,
      classifier0 = () => piClassifier(pi.binders, closedEnv, pi.out, closureKind, closureScope, mentionedScope),
      isPropValued = pi.knownPropValued.getOrElse {
        val fresh = BinderOps.freshen(pi.binders, closedEnv)
        Sorts.isProposition(evalTerm(pi.out, fresh))
      }
    )
  }

  /** A local a lambda captures, which contributes to its closure what `Sorts.Field.ofCapture` reads off its value. */
  private[raccoonlang] final case class Capture(ref: CoreAst.LocalRef, value: Value)

  /**
   * The locals a lambda captures (spec §4.3): those bound outside it, in `env`, that its body mentions, in terms and in
   * types written in the body. The binder types and result are not the body, and implicit arguments are never written,
   * so neither contributes. The residual lists them, in ref id order. A capture is read forced, as a closure's
   * environment holds it: a destructured evidence field may be bound unforced.
   */
  private[raccoonlang] def lambdaCaptures(l: CTerm.Lam, env: Env): Vector[Capture] =
    l.bodyRefs.toVector
      .sortBy(_.id)
      .flatMap(ref => env.localValueOption(ref).map(value => Capture(ref, Value.forced(value))))

  /**
   * A lambda's derived closure field (spec §4.3): the join of what its captures contribute to it, read in `env`, where
   * the lambda stands. Checking and evaluation both derive it here from the residual's captures, and sorts commute with
   * substitution, so evaluation agrees with what checking derived.
   */
  private def derivedField[P <: Value](field: Sorts.Field[P], captures: Vector[CoreAst.LocalRef], env: Env): P =
    field.join(captures.map { ref =>
      field.ofCapture(
        Value.forced(env.localValueOption(ref).getOrElse(wtf(s"The derived closure's capture ${ref.name} is unbound")))
      )
    })

  private def evalRef(ref: CTerm.Ref, env: Env): Value = {
    val res = ref match {
      case CTerm.GlobalRef(name, _) => env(name)
      case CTerm.LocalRef(local, _) => env(local)
    }
    res match {
      case h: ConstructorHead if h.totalArity == 0 =>
        Packed.construct(h, Vector.empty, h.tpe)
      case _ => res
    }
  }

  /**
   * Apply `fn` to an argument for each binder of its group. A lambda binds them as given, and any other head stores
   * them as given in the application it builds, deferred evidence included (`DeferredEvidence`): applying forces none.
   */
  private[raccoonlang] def evalApply(fn: Value, vArgs: Vector[Value]): Value = evalSteps(applyStep(fn, vArgs))

  /**
   * Apply a validated native String.append result through the same checked constructor application path as source. The
   * closed layout is the capability for the one narrow delayed-key result case.
   */
  private[raccoonlang] def evalValidatedStringAppend(layout: SourceStringLayout, chars: VPacked): Value = {
    require(chars.codec eq layout.charListCodec, "Validated String.append result has a different CharList codec")
    evalSteps(applyStep(layout.stringMk, Vector(chars), layout))
  }

  private def applyStep(
      fn: Value,
      vArgs: Vector[Value],
      delayedStringAppend: SourceStringLayout = null
  ): Step = {
    fn.tpe match {
      case pi: VPi =>
        // Grouping is part of a function type's identity, so an application supplies exactly this
        // Pi's own binders. A nested group is reached by a second application, which arrives here
        // as its own call. Keep this boundary checked because native lambdas bypass Core evaluation.
        if (vArgs.length != pi.binders.length)
          fail(ArityMismatch(pi.binders.length, vArgs.length, ArityMismatch.Arguments))
        // Lazy: the VLam branch delegates env construction to lamStep.
        lazy val envWithArgs = getEnvWithArgs(pi, pi.env, vArgs)
        fn match {
          case lam: VLam =>
            lamStep(lam, vArgs)
          case h: ConstructorHead =>
            val resultTy = pi.constructorResultType(envWithArgs)
            val storedArgs = Value.constructorStoredArgs(h, vArgs)
            if (delayedStringAppend eq null) Step.Done(Packed.construct(h, storedArgs, resultTy))
            else {
              if (!(h eq delayedStringAppend.stringMk))
                wtf("A delayed String.append key capability reached a different constructor")
              Step.Done(VApp.deferredStringAppendResult(delayedStringAppend, storedArgs, resultTy))
            }
          // Every non-reducing head builds one new application layer over itself. An existing
          // neutral stays the head rather than being flattened into the new spine: flattening
          // would destroy positional-projection arity. A blocked head propagates its blockers,
          // and any other head is unblocked.
          case head @ (_: VConst | _: VApp | _: NeutralThunk | _: Var) =>
            val blockedOn = Blocker.unapply(head).getOrElse(DepSet.empty)
            Step.Done(Value.canonicalizeProof(VApp(head, vArgs, pi.codomain(envWithArgs), blockedOn)))
          case _ => fail(CannotApplyNonFunction(fn))
        }
      case _ => fail(CannotApplyNonFunction(fn.tpe))
    }
  }

  /** An application's arguments are evaluated first, since evaluation is strict; the callee's body is its tail. */
  private def applyTermStep(fn: CoreAst.Term, args: Vector[CoreAst.Term], env: Env): Step = {
    val vf = evalTerm(fn, env)
    applyStep(vf, residualArguments(vf, args.map(a => evalTerm(a, env))))
  }

  private def valueName(v: Value): String =
    v match {
      case VConst(name, _, _)              => name
      case VLam(_, ValueId.Const(name), _) => name
      case head: ConstructorHead           => head.name
      case _                               => "function"
    }

  /**
   * Checked application syntax carries only the explicit args. The implicit ones are re-derived here by running their
   * projection specs against the provided args, exactly as application checking did (Projection.project is the shared
   * implementation). Each evidence one is an erased proof of its binder's proposition, deferred (`DeferredEvidence`):
   * checking discharged or checked it once, and running the application evaluates the proposition only if the callee
   * looks at the proof (PROOF_BY_EVALUATION §1.6). The proposition is its binder type evaluated where every binder
   * before it is bound, as checking evaluated it.
   */
  private def residualArguments(fn: Value, vArgs: Vector[Value]): Vector[Value] =
    fn.tpe match {
      case pi: VPi if pi.numExplicit != pi.binders.length =>
        // A binder type is evaluated before the application inside it has been checked, so both of
        // these are reachable from a program and stay ordinary errors, located by whichever term the
        // checker was working on.
        if (vArgs.length != pi.numExplicit) fail(ArityMismatch(pi.numExplicit, vArgs.length, ArityMismatch.Arguments))
        var provided = 0
        var index = 0
        val earlier = Vector.newBuilder[Value]
        while (index < pi.binders.length) {
          val binder = pi.binders(index)
          earlier += (binder.mode match {
            case BinderMode.Explicit =>
              val arg = vArgs(provided)
              provided += 1
              arg
            case BinderMode.Implicit =>
              // Pi formation compiles a spec for every binder that stays implicit; one without is a
              // broken invariant, not a program's fault.
              val spec = binder.projection.getOrElse(
                wtf(s"Implicit binder ${binder.name} of ${valueName(fn)} has no projection spec")
              )
              telescope.Projection.project(spec, vArgs) match {
                case Right(value) => value
                case Left(reason) => fail(ImplicitReconstructionFailed(binder.name, valueName(fn), reason))
              }
            case BinderMode.Evidence => deferredEvidence(pi, earlier.result())
          })
          index += 1
        }
        earlier.result()
      case _ => vArgs
    }

  /** Deferred evidence for the binder of `pi` after the arguments `earlier`: its type, evaluated with them bound. */
  private def deferredEvidence(pi: VPi, earlier: Vector[Value]): DeferredEvidence = {
    val before = pi.binders.take(earlier.length)
    new DeferredEvidence(() =>
      evalTerm(
        pi.binders(earlier.length).ty,
        BinderOps.instantiateFullRuntime(before, pi.runtimeSlotPrefixLayouts(earlier.length), pi.env, earlier)
      )
    )
  }

  /**
   * `args` for `fn`, each at one of its evidence binders replaced by deferred evidence of that binder's proposition.
   */
  private def evidenceDeferredAt(fn: Value, args: Vector[Value]): Vector[Value] =
    fn.tpe match {
      case pi: VPi if pi.numEvidence > 0 =>
        if (pi.binders.length != args.length)
          wtf(s"An application of ${pi.binders.length} binders stores ${args.length} arguments")
        val earlier = Vector.newBuilder[Value]
        var index = 0
        while (index < pi.binders.length) {
          earlier +=
            (if (pi.binders(index).mode == BinderMode.Evidence) deferredEvidence(pi, earlier.result()) else args(index))
          index += 1
        }
        earlier.result()
      case _ => args
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
        case None           => ValueId.LocalId(l.id, closedEnv.locals.values.toVector)
      }
      Value.canonicalizeProof(VLam(vpi, id, LamBody.Core(l, closedEnv)))
    }
  }

  private[raccoonlang] def runLam(lam: VLam, args: Vector[Value]): Value = evalSteps(lamStep(lam, args))

  /** A native or proof eta-lambda's result, or a core lambda's body, its tail, in the env binding its arguments. */
  private def lamStep(lam: VLam, args: Vector[Value]): Step = {
    // Arguments are bound as supplied. A lambda's Pi is the one it was created with, so its binders
    // are exactly the ones its body expects.
    lazy val piEnv =
      BinderOps.instantiateFullRuntime(lam.tpe.binders, lam.tpe.runtimeSlotLayout, lam.tpe.env, args)

    lam.body match {
      // A native body reads only the arguments it names, none of them evidence: a native operation's binders are
      // validated explicit, a builtin's are never evidence (BuiltinEvidence), and a raw recursive stub reads its
      // metric's, which is never a proof.
      case LamBody.Native(run, nativeEnv, _) => Step.Done(run(args, nativeEnv))
      case LamBody.ProofEta                  => Step.Done(Value.canonicalizeProof(VProof(lam.tpe.codomain(piEnv))))
      case LamBody.Core(term, coreEnv) =>
        val bodyEnv = BinderOps.instantiateFullRuntime(lam.tpe.binders, lam.tpe.runtimeSlotLayout, coreEnv, args)

        var recurEnv = bodyEnv
        val peerValues = Vector.newBuilder[Value]
        var index = 0
        while (index < term.recursivePeers.length) {
          val (ref, name) = term.recursivePeers(index)
          // A singleton's self reference is this very lambda (possibly a materialized copy), never a
          // same-named global; group peers resolve through the group's lazy bindings.
          val peer =
            if (term.recursivePeers.length == 1 && term.name.contains(name)) lam
            else
              coreEnv.globals
                .get(name)
                .map(_.value(coreEnv))
                .getOrElse(wtf(s"Checked recursive peer $name is absent from its group"))
          peerValues += peer
          index += 1
        }
        if (term.recursivePeers.nonEmpty)
          recurEnv = recurEnv.bindRuntimeLocals(term.recursivePeerSlotLayout, peerValues.result())
        Step.Tail(term.body, recurEnv)
    }
  }

  private def forceThunk(thunk: NeutralThunk, materializer: ValueOps.Materializer): Value =
    evalSteps(matchStep(thunk.term, materializer.materializeEnv(thunk.env)))

  private def evalLam(l: CTerm.Lam, env: Env): Value = evalLam(l, evalPi(l.ty, env), env)

  /** The value that is a sort parameter's type, which a variable of it and an expression of it have. */
  private[raccoonlang] def parameterType(parameter: CoreAst.Parameter): ParameterTpe =
    parameter match {
      case CoreAst.Parameter.Level    => LevelTpe
      case CoreAst.Parameter.Kind     => KindTpe
      case CoreAst.Parameter.Lifetime => LifetimeTpe
    }

  // A checked sort parameter expression denotes a normal form: checking admits nothing else at its position.
  private[raccoonlang] def getLevel(v: Value): Level =
    v match {
      case l: Level => l
      case other    => wtf(s"Checked level expression evaluated to the non-level $other")
    }

  private[raccoonlang] def getKind(v: Value): Kind =
    v match {
      case k: Kind => k
      case other   => wtf(s"Checked kind expression evaluated to the non-kind $other")
    }

  private[raccoonlang] def getLifetime(v: Value): Lifetime =
    v match {
      case l: Lifetime => l
      case other       => wtf(s"Checked lifetime expression evaluated to the non-lifetime $other")
    }

  private[raccoonlang] def evalFormOp(form: CoreAst.Form, args: Vector[Value]): Value =
    form match {
      case CoreAst.Form.LevelZero     => Level.zero
      case CoreAst.Form.LevelOne      => Level.one
      case CoreAst.Form.LevelSucc     => Level.succ(getLevel(args(0)))
      case CoreAst.Form.LevelMax      => Level.max(args.map(getLevel))
      case CoreAst.Form.KindUnr       => Kind.unr
      case CoreAst.Form.KindLin       => Kind.lin
      case CoreAst.Form.KindJoin      => Kind.join(args.map(getKind))
      case CoreAst.Form.LifetimeEmpty => Lifetime.empty
      case CoreAst.Form.LifetimeUnion => Lifetime.union(args.map(getLifetime))
    }

  /**
   * One step of evaluation (docs/kernel.md#evaluation-depth): a term's value, or the term in tail position whose value
   * is its value, with the env to evaluate that term in.
   */
  private sealed trait Step
  private object Step {
    final case class Done(value: Value) extends Step
    final case class Tail(term: CoreAst.Term, env: Env) extends Step
  }

  /**
   * Evaluation attaches no location: reduction runs inside callee bodies the user did not write, so a failure here
   * belongs to the term the checker was working on.
   */
  private[raccoonlang] def evalTerm(term: CoreAst.Term, env: Env): Value = evalSteps(step(term, env))

  /** Takes steps until one is a value, in a loop, so a tail position costs no host stack. */
  @tailrec
  private def evalSteps(next: Step): Value =
    next match {
      case Step.Done(value)     => value
      case Step.Tail(term, env) => evalSteps(step(term, env))
    }

  /**
   * The tail positions are a block's result, a match's chosen branch, a scope's body, and a core lambda's body at an
   * application.
   */
  private def step(term: CoreAst.Term, env: Env): Step =
    term match {
      case CTerm.NatLit(value, _)    => Step.Done(Packed.evalNatLit(value, env))
      case CTerm.StrLit(scalars, _)  => Step.Done(Packed.evalStrLit(scalars, env))
      case ref: CTerm.Ref            => Step.Done(evalRef(ref, env))
      case CTerm.App(fn, args, _, _) => applyTermStep(fn, args, env)
      case pi: CTerm.Pi              => Step.Done(evalPi(pi, env))
      case l: CTerm.Lam              => Step.Done(evalLam(l, env))
      case m: CTerm.Match            => matchStep(m, env)
      case b: CTerm.Body =>
        var bodyEnv = env
        var index = 0
        while (index < b.lets.length) {
          val binding = b.lets(index)
          bodyEnv = bindRuntimeLet(binding.pattern, evalTerm(binding.value, bodyEnv), bodyEnv)
          index += 1
        }
        Step.Tail(b.res, bodyEnv)
      // The interpreter binds a scope's variable to its atom and makes none of its checks (spec §8).
      case scope: CTerm.Scope   => Step.Tail(scope.body, env.putLocal(scope.ref, Atoms.of(scope)))
      case CTerm.Prop(scope, _) => Step.Done(Sorts.prop(getLifetime(evalTerm(scope, env))))
      case CTerm.Sort(level, kind, scope, _) =>
        Step.Done(
          Sorts.sort(getLevel(evalTerm(level, env)), getKind(evalTerm(kind, env)), getLifetime(evalTerm(scope, env)))
        )
      case CTerm.FormOp(form, args, _) => Step.Done(evalFormOp(form, args.map(evalTerm(_, env))))
      // Named field syntax is resolved to a selector application by checkSelect, so a Select can
      // only reach evaluation if something published unchecked syntax.
      case CTerm.Select(_, field, _) =>
        wtf(s"Unresolved field selection .$field reached evaluation")
    }

  private def matchStep(m: CTerm.Match, env: Env): Step = {
    // Checking expands a wildcard into the cases it stands for, so only a checked match reaches evaluation.
    m.wildcard.foreach(w => wtf(s"An unexpanded wildcard case at ${w.span} reached evaluation"))
    evalTerm(m.scrut, env) match {
      // The fields are bound as stored, so matching forces no evidence field; a branch forces one where it reads it.
      // Exhaustiveness is settled by MatchChecker: a constructor-form scrutinee always has a branch.
      case scrut @ ConstructorForm.Stored(ctorName, args) =>
        val branch = m.cases
          .find(c => c.ctorName == ctorName)
          .getOrElse(wtf(s"Checked match has no branch for constructor $ctorName"))
        Step.Tail(branch.body, branchEnv(m, branch, scrut, args, env))
      case proof: VProof => Step.Done(evalProofMatch(m, proof, env))
      case other         =>
        // Structure eta (rule 1): a neutral at an eta-eligible struct type has an eta view, so the
        // single branch fires against its virtual fields instead of sticking. The canonical
        // projection terms this builds are matches whose body is a bare pattern variable, and
        // `fieldProjection` builds their thunks without evaluating them, so the rule cannot cycle.
        StructEta.fields(other) match {
          case Some(etaFields) =>
            val branch = m.cases match {
              case Vector(single) => single
              case _              => wtf(s"Eta-eligible struct match has ${m.cases.length} cases")
            }
            Step.Tail(branch.body, branchEnv(m, branch, other, etaFields, env))
          // We are either blocked or stuck
          case None =>
            val blockedOn = other match {
              case Blocker(blockedOn) => blockedOn
              case _                  => DepSet.empty
            }
            Step.Done(Value.canonicalizeProof(stuckMatchThunk(m, env, evalTerm(m.motive, env), blockedOn)))
        }
    }
  }

  private[raccoonlang] def stuckMatchThunk(
      m: CTerm.Match,
      env: Env,
      outType: Value,
      blockedOn: DepSet
  ): NeutralThunk = {
    val closedEnv = env.closeForEval(CapturedRefs.getCapturedRefs(m, env))
    NeutralThunk(m, closedEnv, ValueId.LocalId(m.id, closedEnv.locals.values.toVector), outType, blockedOn)
  }

  private[raccoonlang] def evalBranch(
      m: CTerm.Match,
      branch: CoreAst.Case,
      scrut: Value,
      args: Vector[Value],
      env: Env
  ): Value =
    evalTerm(branch.body, branchEnv(m, branch, scrut, args, env))

  /**
   * The env a branch of `m` runs in when its scrutinee is `scrut`: its pattern's locals bound to the scrutinee's
   * fields, and the match's equation, if it names one, to deferred evidence of the case's equation, which is the
   * canonical proof of it when forced (docs/implemented/MATCH_EQUATION.md).
   */
  private def branchEnv(m: CTerm.Match, branch: CoreAst.Case, scrut: Value, args: Vector[Value], env: Env): Env = {
    // Every caller supplies a scrutinee's stored fields to a branch MatchChecker already matched
    // against that constructor's arity.
    val layout = branch.runtimeSlotLayout
    if (args.length != layout.size)
      wtf(s"Checked branch for ${branch.ctorName} binds ${layout.size} fields, got ${args.length}")
    val fieldsEnv = bindRuntimeFields(args, env, layout)
    m.equation.fold(fieldsEnv) { equation =>
      val equality =
        env.equality.fold(reason => wtf(s"A checked match equation reached an env where $reason"), identity)
      val ctor = env(branch.ctorName) match {
        case head: ConstructorHead => head
        case other                 => wtf(s"Checked case ${branch.ctorName} names $other, not a constructor")
      }
      val evidence = new DeferredEvidence(() => MatchEquation.proposition(equality, scrut, ctor, args))
      fieldsEnv.putLocal(equation.ref, evidence)
    }
  }

  /** A pattern's locals bound to a constructor's fields, each in the canonical form for its exact type. */
  private def bindRuntimeFields(
      fields: Vector[Value],
      env: Env,
      layout: RuntimeSlotLayout
  ): Env = {
    if (layout.size != fields.length) wtf("Pattern slot layout has inconsistent arity")
    env.bindRuntimeLocals(layout, fields)
  }

  /**
   * A `let` 's locals bound to its value, transparently: the one local to the value, or a destructuring's locals to the
   * fields of the value's eta view (PAIRS_AND_PRELUDE §3.5, §3.8), `StructEta.destructuredFields`. The checker binds
   * them here too, once it has admitted the destructuring, so a destructuring never blocks.
   */
  private[raccoonlang] def bindLet(pattern: CoreAst.LetPattern, value: Value, env: Env): Env =
    pattern match {
      case CoreAst.LetPattern.Local(ref) => env.putLocal(ref, value)
      case CoreAst.LetPattern.Fields(vars, _) =>
        val fields =
          StructEta.destructuredFields(value).getOrElse(wtf(s"A checked destructuring's value $value has no fields"))
        if (fields.length != vars.length)
          wtf(s"A checked destructuring binds ${vars.length} fields of $value, which has ${fields.length}")
        env.bindLocals(vars, fields)(_.ref)
    }

  /** Runtime-only counterpart: checker environments continue to bind lets into their persistent local map. */
  private def bindRuntimeLet(pattern: CoreAst.LetPattern, value: Value, env: Env): Env =
    pattern match {
      case CoreAst.LetPattern.Local(ref) => env.putLocal(ref, value)
      case fieldsPattern: CoreAst.LetPattern.Fields =>
        val fields =
          StructEta.destructuredFields(value).getOrElse(wtf(s"A checked destructuring's value $value has no fields"))
        if (fields.length != fieldsPattern.vars.length)
          wtf(
            s"A checked destructuring binds ${fieldsPattern.vars.length} fields of $value, which has ${fields.length}"
          )
        bindRuntimeFields(
          fields,
          env,
          fieldsPattern.runtimeSlotLayout
        )
    }

  /**
   * Elimination of an erased proof (docs/kernel.md#proofs-and-elimination). A Prop-valued result can erase immediately.
   * A data-valued result is stuck: reconstructible propositions have already canonicalized to `VCtor` and use the
   * ordinary path.
   */
  private def evalProofMatch(m: CTerm.Match, scrut: VProof, env: Env): Value = {
    val outType = evalTerm(m.motive, env)
    if (Sorts.isProposition(outType)) Value.canonicalizeProof(VProof(outType))
    else stuckMatchThunk(m, env, outType, scrut.tpe.synDeps)
  }

  // Proof publication (docs/kernel.md#proofs-and-elimination): exact type alone chooses a reconstructed constructor,
  // a proof eta-lambda, or `VProof`; the value's origin is irrelevant. Data has no such policy: an axiom of struct type
  // publishes as the plain symbol, and structure eta reaches it through the rules rather than through its
  // representation.
  private def publishedValue(value: Value, ty: Value): Value =
    if (Sorts.isProposition(ty)) Value.canonicalizeProof(value)
    else value

  // A declaration is checked exactly once; the value the checker produced IS the published value.
  // There is no separate run world: once a definition has made it into the env, it is trusted.
  private[raccoonlang] def evalDecl(decl: Decl, env: Env): Env = evalDecl(decl, env, trusted = false)

  /**
   * The per-declaration boundary: locates what happens between a declaration's terms (name collisions, block layout,
   * bootstrap privilege) and appends the outermost context frame. It is where a host stack overflow in the
   * declaration's checking becomes `EvaluationTooDeep`, located at the whole declaration (PROOF_BY_EVALUATION §2.5): no
   * boundary inside a declaration catches one.
   *
   * `trusted` is the one bootstrap privilege: a prelude may declare builtin bodies, the native Nat operations and
   * axioms (spec §7.3). A program cannot, so nothing it declares can acquire kernel semantics it did not write, nor
   * assume a value no checked body built.
   */
  private[raccoonlang] def evalDecl(decl: Decl, env: Env, trusted: Boolean): Env =
    framed(Frame.InDefinition(decl.label)) {
      at(decl.span) {
        try
          decl match {
            case Decl.ConstDecl(name, ty, body, sealedBy, _) =>
              val installed = body match {
                case CoreAst.ConstBody.Builtin(_) =>
                  if (!trusted) fail(ReservedKernelName(name))
                  val tyV = TypeChecker.checkDeclType(ty, env).value
                  // A builtin's native body reads its arguments as values, and an evidence argument is an erased proof
                  // that nothing forces for it, so its own binder group has none.
                  tyV match {
                    case pi: VPi =>
                      pi.binders.find(_.mode == BinderMode.Evidence).foreach { binder =>
                        at(binder.span)(fail(BuiltinEvidence(name, binder.name)))
                      }
                    case _ =>
                  }
                  env.putGlobal(name, publishedValue(Builtins.instantiate(name, tyV), tyV))

                case CoreAst.ConstBody.TermBody(term) =>
                  val checkedTy = TypeChecker.checkDeclType(ty, env).value
                  // A global is never tracked, so none may be linear (spec §3.2).
                  if (Linearity.isLinear(checkedTy)) at(ty.span)(fail(LinearGlobal(Some(name), checkedTy)))
                  val checked = TypeChecker.checkTerm(term, checkedTy, env)
                  val published =
                    if (trusted && Packed.opNames(name)) Packed.nativeOp(name, checked.value, env)
                    else publishedValue(checked.value, checkedTy)
                  env.putGlobal(name, published)
              }
              // A sealed family's selectors are kept to its module, as its constructors are (spec §7.1).
              sealedBy.fold(installed)(installed.sealMember(name, _))

            case Decl.AxiomDecl(name, ty, _) =>
              if (!trusted) fail(UntrustedAxiom(name))
              val tyV = TypeChecker.checkDeclType(ty, env).value
              env.putGlobal(name, publishedValue(VConst(name, axiomHead(name, tyV), tyV), tyV))

            case d: Decl.InductiveDecl =>
              InductiveChecks.evalInductiveBlock(Decl.InductiveBlock(Vector(d), d.span), env)

            case b: Decl.InductiveBlock => InductiveChecks.evalInductiveBlock(b, env)

            case b: Decl.RecursiveDefBlock =>
              b.definitions.foreach { definition =>
                // One member of a group: more precise than the group's own span.
                at(definition.span) {
                  if (env.globals.contains(definition.name)) fail(AlreadyDefined(definition.name))
                  if (definition.name == "_") wtf("Wildcards not allowed in global names")
                }
              }
              val checked = TypeChecker.checkRecursiveDefBlock(b, env)
              env.putRecursiveGroup(
                checked.map(_.name),
                groupEnv =>
                  checked.map { definition =>
                    evalLam(definition.residual, definition.vpi, groupEnv) match {
                      case lambda: VLam => lambda
                      case other        => wtf(s"Checked recursive definition ${definition.name} produced $other")
                    }
                  }
              )
          }
        catch { case _: StackOverflowError => fail(EvaluationTooDeep) }
      }
    }

  /** Execute a checked program. Checking and declaration publication have already happened. */
  def run(program: Execution.CheckedProgram): Option[Value] = program.result

  /** Compatibility entry point for implementation code and same-package kernel tests. */
  private[raccoonlang] def run(p: Program, prelude: Prelude.Config = Prelude.default): Option[Value] =
    TypeChecker.checkRaw(p, prelude)

  private[raccoonlang] val preludeInitialEnv: Env =
    CoreAst.Parameter.all.foldLeft(Env.empty)((env, parameter) =>
      env.putGlobal(parameter.name, parameterType(parameter))
    )

  private[raccoonlang] def addPreludeDecl(env: Env, decl: Decl): Env = evalDecl(decl, env, trusted = true)

  /**
   * Install the native literal layouts and the equality family of a completed prelude. A prelude that declares `Nat` or
   * `String` must present the exact checked source layout, so a malformed representation is rejected rather than
   * silently left without literals. Validation failure rejects the candidate without mutating the environment the
   * declarations were streamed into. An `Eq` that is not the equality family leaves only named match equations
   * unavailable, with the reason (MatchEquation).
   */
  private[raccoonlang] def finishPrelude(env: Env): Env = {
    val withNat =
      if (env.nativeLiterals.natLayout.isEmpty && env.globals.contains(NatCodec.familyName))
        env.installNatLayout(Packed.validateNatFamily(env))
      else env
    val withString =
      if (withNat.nativeLiterals.stringLayout.isEmpty && withNat.globals.contains("String"))
        withNat.installStringLayout(Packed.validateStringLayout(withNat))
      else withNat
    val withStringAppend = Packed.attachStringAppend(withString)
    withStringAppend.installEquality(MatchEquation.validate(withStringAppend))
  }

  private[raccoonlang] def buildPreludeEnv(core: Program): Env =
    finishPrelude(core.decls.foldLeft(preludeInitialEnv)(addPreludeDecl))
}
