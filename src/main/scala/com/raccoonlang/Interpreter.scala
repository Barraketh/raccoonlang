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
                case other             => wtf(s"Level variable $id solved to the non-level $other")
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
    BinderOps.instantiateFull(fnTpe.binders, baseEnv, args)

  /**
   * The sort of a Pi, derived from the env it closed over (spec §2.4). Its level right-folds the binder types' levels
   * with imax over the codomain's, which reduces to Prop for a Prop-valued codomain and to ordinary max for a
   * definitely positive one. Its kind is its closure kind alone. Its scope unites its closure scope, what its values
   * hold, with the binder types' scopes and the codomain's, less the lifetimes the group itself binds, since the caller
   * supplies them. A kind or lifetime binder contributes no level and no scope. Computing it per instance means a
   * residual Pi re-evaluated with concrete parameters gets the concrete sort, not the declaration-time one. A Pi that
   * binds a level is `Large`: the level changes the universe of everything after it, so no sort contains the Pi.
   *
   * A closure kind other than `Kind.unr` at a level that may be zero is `LinearProp` (spec §2.3); substitution keeps a
   * level that is never zero, so only checking can reach it.
   */
  private[raccoonlang] def piClassifierFromChecked(
      binders: Vector[CoreAst.Binder],
      freshEnv: Env,
      outV: Value,
      closureKind: Kind,
      closureScope: Lifetime
  ): Classifier = {
    val freshValues = binders.map(binder => freshEnv(binder.localRef))
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
      val scope = Lifetime.less(Lifetime.union(closureScope +: domSorts.map(_.scope) :+ outSort.scope), ownLifetimes)
      val outLevel = outSort.level
      val level =
        if (Sorts.isProp(outSort)) outLevel
        else if (Level.isNeverZero(outLevel)) Level.max(domSorts.map(_.level) :+ outLevel)
        else domSorts.map(_.level).foldRight(outLevel)(Level.imax)
      if (!Sorts.admitsKind(level, closureKind)) fail(LinearProp(closureKind, level))
      Sorts.sort(level, closureKind, scope)
    }
  }

  /** Cache only proposition classifications that cannot change when level parameters are instantiated. */
  private[raccoonlang] def stablePiPropClassification(outV: Value): Option[Boolean] = {
    val outSort = TypeChecker.getUniverse(outV)
    if (Sorts.isProp(outSort)) Some(true)
    else if (Level.isNeverZero(outSort.level)) Some(false)
    else None
  }

  private def piClassifier(
      binders: Vector[CoreAst.Binder],
      baseEnv: Env,
      out: CoreAst.Term,
      closureKind: Kind,
      closureScope: Lifetime
  ): Classifier = {
    val freshEnv = BinderOps.freshen(binders, baseEnv)
    piClassifierFromChecked(binders, freshEnv, evalTerm(out, freshEnv), closureKind, closureScope)
  }

  /** A checked closure field's expression. A lambda's derived one is filled in by the checker before evaluation. */
  private def closureTerm(field: CoreAst.ClosureField): CoreAst.Term =
    field.term match {
      case Some(term) => term
      case None       => wtf("A derived closure field reached evaluation before checking derived it")
    }

  private[raccoonlang] def evalPi(pi: CTerm.Pi, env: Env): VPi = {
    val capturedRefs = CapturedRefs.getCapturedRefs(pi, env)
    val closedEnv = env.closeForEval(capturedRefs)
    val captureVals = closedEnv.locals.values.toVector
    val id = ValueId.LocalId(pi.nodeId, captureVals)
    val closureKind = getKind(evalTerm(closureTerm(pi.closure.kind), closedEnv))
    val closureScope = getLifetime(evalTerm(closureTerm(pi.closure.scope), closedEnv))

    val synDeps = DepSet.newBuilder
    captureVals.foreach { v =>
      synDeps.unionInPlace(v.synDeps)
    }
    synDeps.unionInPlace(closureKind.synDeps)
    synDeps.unionInPlace(closureScope.synDeps)

    VPi(
      closedEnv,
      pi.binders,
      codomain = env => evalTerm(pi.out, env),
      closureKind,
      closureScope,
      synDeps.result(),
      id,
      classifier0 = () => piClassifier(pi.binders, closedEnv, pi.out, closureKind, closureScope),
      knownPropValued = pi.knownPropValued
    )
  }

  /** A local a lambda captures, and the sort of its type, which is what it contributes to the lambda's closure. */
  private[raccoonlang] final case class Capture(ref: CoreAst.LocalRef, value: Value, sort: VSort)

  /**
   * The locals a lambda captures (spec §4.3): those bound outside it, in `env`, that its body mentions. The binder
   * types and result are not the body, and implicit arguments are never written, so neither contributes. A variable of
   * a sort parameter is not a value and contributes nothing. Neither does a recursive definition's reference to itself,
   * the one local whose type may be large: it names a global, which a lambda does not capture (spec §3.3).
   */
  private[raccoonlang] def lambdaCaptures(l: CTerm.Lam, env: Env): Vector[Capture] =
    if (env.locals.isEmpty) Vector.empty
    else
      env.locals.iterator
        .filter { case (ref, _) => l.bodyRefs(ref) }
        .flatMap { case (ref, value) =>
          value.tpe.tpe match {
            case sort: VSort           => Some(Capture(ref, value, sort))
            case Large | SortParameter => None
            case other                 => wtf(s"Captured local ${ref.name} has the type ${value.tpe} : $other")
          }
        }
        .toVector

  /** The closure a lambda's captures derive (spec §4.3): the join of their kinds and the union of their scopes. */
  private[raccoonlang] def derivedClosure(captures: Vector[Capture]): (Kind, Lifetime) =
    (Kind.join(captures.map(_.sort.kind)), Lifetime.union(captures.map(_.sort.scope)))

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
          fail(ArityMismatch(pi.binders.length, vArgs.length))
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
          case _ => fail(CannotApplyNonFunction(fn))
        }
      case _ => fail(CannotApplyNonFunction(fn.tpe))
    }
  }

  private def evalApplyTerm(fn: CoreAst.Term, args: Vector[CoreAst.Term], env: Env): Value = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    if (vArgs.isEmpty) fail(CannotApplyNonFunction(vf.tpe))
    evalApply(vf, reconstructImplicits(vf, vArgs))
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
  private def reconstructImplicits(fn: Value, vArgs: Vector[Value]): Vector[Value] =
    fn.tpe match {
      case pi: VPi if pi.binders.exists(_.isImplicit) =>
        // A binder type is evaluated before the application inside it has been checked, so both of
        // these are reachable from a program and stay ordinary errors, located by whichever term the
        // checker was working on.
        if (vArgs.length != pi.numExplicit) fail(ArityMismatch(pi.numExplicit, vArgs.length))
        var provided = 0
        pi.binders.map { binder =>
          if (!binder.isImplicit) {
            val arg = vArgs(provided)
            provided += 1
            arg
          } else {
            // Pi formation compiles a spec for every binder that stays implicit; one without is a
            // broken invariant, not a program's fault.
            val spec = binder.projection.getOrElse(
              wtf(s"Implicit binder ${binder.name} of ${valueName(fn)} has no projection spec")
            )
            telescope.Projection.project(spec, vArgs) match {
              case Right(value) => value
              case Left(reason) => fail(ImplicitReconstructionFailed(binder.name, valueName(fn), reason))
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
              coreEnv.globals
                .get(name)
                .map(_.value(coreEnv))
                .getOrElse(wtf(s"Checked recursive peer $name is absent from its group"))
          current.putLocal(ref, peer)
        }
        evalTerm(term.body, recurEnv)
    }
  }

  private def forceThunk(thunk: NeutralThunk, eqStore: EqStore): Value =
    evalMatch(thunk.term, ValueOps.materializeEnv(thunk.env, eqStore))

  private def evalLam(l: CTerm.Lam, env: Env): Value = {
    val vpi = evalPi(l.ty, env)
    if (ValueEquivalence.keyAssertionsEnabled) assertDerivedClosure(l, vpi, env)
    evalLam(l, vpi, env)
  }

  /**
   * Check/run coherence of a derived closure (spec §8): the expression the checker derived, re-evaluated where the
   * lambda now stands, equals what the lambda's captures derive there. Sorts commute with substitution, so it must.
   */
  private def assertDerivedClosure(l: CTerm.Lam, vpi: VPi, env: Env): Unit = {
    def derived(field: CoreAst.ClosureField): Boolean =
      field match {
        case _: CoreAst.ClosureField.Derived => true
        case _: CoreAst.ClosureField.Written => false
      }
    val kindDerived = derived(l.ty.closure.kind)
    val scopeDerived = derived(l.ty.closure.scope)
    if (kindDerived || scopeDerived) {
      val (kind, scope) = derivedClosure(lambdaCaptures(l, env))
      if ((kindDerived && kind != vpi.closureKind) || (scopeDerived && scope != vpi.closureScope))
        wtf(
          s"The derived closure of $vpi is ${vpi.closureKind}, ${vpi.closureScope}; its captures derive $kind, $scope"
        )
    }
  }

  /** The value that is a sort parameter's type, which a variable of it and an expression of it have. */
  private[raccoonlang] def parameterType(parameter: CoreAst.Parameter): ParameterTpe =
    parameter match {
      case CoreAst.Parameter.Level    => LevelTpe
      case CoreAst.Parameter.Kind     => KindTpe
      case CoreAst.Parameter.Lifetime => LifetimeTpe
    }

  // A checked sort parameter expression denotes a normal form: checking admits nothing else at its position.
  private[raccoonlang] def getLevel(v: Value): Level =
    Level.fromValue(v).getOrElse(wtf(s"Checked level expression evaluated to the non-level $v"))

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

  private[raccoonlang] def evalSort(level: Value, kind: Value, scope: Value): VSort =
    Sorts.sort(getLevel(level), getKind(kind), getLifetime(scope))

  private[raccoonlang] def evalFormOp(form: CoreAst.Form, args: Vector[Value]): Value =
    form match {
      case CoreAst.Form.LevelZero     => Level.zero
      case CoreAst.Form.LevelOne      => Level.one
      case CoreAst.Form.LevelSucc     => Level.succ(getLevel(args(0)))
      case CoreAst.Form.LevelMax      => Level.max(args.map(getLevel))
      case CoreAst.Form.LevelIMax     => Level.imax(getLevel(args(0)), getLevel(args(1)))
      case CoreAst.Form.KindUnr       => Kind.unr
      case CoreAst.Form.KindLin       => Kind.lin
      case CoreAst.Form.KindJoin      => Kind.join(args.map(getKind))
      case CoreAst.Form.LifetimeEmpty => Lifetime.empty
      case CoreAst.Form.LifetimeUnion => Lifetime.union(args.map(getLifetime))
    }

  /**
   * Evaluation attaches no location: reduction runs inside callee bodies the user did not write, so a failure here
   * belongs to the term the checker was working on.
   */
  private[raccoonlang] def evalTerm(term: CoreAst.Term, env: Env): Value =
    term match {
      case CTerm.NatLit(value, _)   => Packed.evalNatLit(value, env)
      case CTerm.StrLit(scalars, _) => Packed.evalStrLit(scalars, env)
      case ref: CTerm.Ref           => evalRef(ref, env)
      case CTerm.App(fn, args, _)   => evalApplyTerm(fn, args, env)
      case pi: CTerm.Pi             => evalPi(pi, env)
      case l: CTerm.Lam             => evalLam(l, env)
      case m: CTerm.Match           => evalMatch(m, env)
      case b: CTerm.Body            => evalBody(b, env)
      // The interpreter binds a scope's variable to its atom and makes none of its checks (spec §8).
      case scope: CTerm.Scope => evalTerm(scope.body, env.putLocal(scope.ref, Atoms.of(scope)))
      case CTerm.Sort(level, kind, scope, _) =>
        evalSort(evalTerm(level, env), evalTerm(kind, env), evalTerm(scope, env))
      case CTerm.FormOp(form, args, _) => evalFormOp(form, args.map(evalTerm(_, env)))
      // Named field syntax is resolved to a selector application by checkSelect, so a Select can
      // only reach evaluation if something published unchecked syntax.
      case CTerm.Select(_, field, _) =>
        wtf(s"Unresolved field selection .$field reached evaluation")
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
              case _              => wtf(s"Eta-eligible struct match has ${m.cases.length} cases")
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
        return Value.canonicalizeProof(stuckMatchThunk(m, env, evalTerm(m.motive, env), blockedOn))
    }

    // Exhaustiveness is settled by MatchChecker: a constructor-form scrutinee always has a branch.
    val branch =
      m.cases.find(c => c.ctorName == ctorName).getOrElse(wtf(s"Checked match has no branch for constructor $ctorName"))
    evalBranch(branch, args, env)
  }

  private[raccoonlang] def typeCollapseDeps(tpe: Value): DepSet = {
    val classifierLevel = TypeChecker.getUniverse(tpe).level
    if (Level.isNeverZero(classifierLevel)) DepSet.empty else classifierLevel.synDeps
  }

  private[raccoonlang] def stuckMatchThunk(
      m: CTerm.Match,
      env: Env,
      outType: Value,
      blockedOn: DepSet
  ): NeutralThunk = {
    val closedEnv = env.closeForEval(CapturedRefs.getCapturedRefs(m, env))
    NeutralThunk(m, closedEnv, ValueId.LocalId(m.nodeId, closedEnv.locals.values.toVector), outType, blockedOn)
  }

  private[raccoonlang] def evalBranch(branch: CoreAst.Case, args: Vector[Value], env: Env): Value = {
    // Every caller supplies a scrutinee's stored fields to a branch MatchChecker already matched
    // against that constructor's arity.
    if (args.length != branch.argRefs.length)
      wtf(s"Checked branch for ${branch.ctorName} binds ${branch.argRefs.length} fields, got ${args.length}")
    val newEnv = args.zip(branch.argRefs).foldLeft(env) { case (curEnv, (argV, ref)) =>
      curEnv.putLocal(ref, Value.canonicalizeProof(argV))
    }
    evalTerm(branch.body, newEnv)
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
    if (Sorts.isProposition(ty)) Value.canonicalizeProof(value)
    else value

  // A declaration is checked exactly once; the value the checker produced IS the published value.
  // There is no separate run world: once a definition has made it into the env, it is trusted.
  private[raccoonlang] def evalDecl(decl: Decl, env: Env): Env = evalDecl(decl, env, trusted = false)

  /**
   * The per-declaration boundary: locates what happens between a declaration's terms (name collisions, block layout,
   * bootstrap privilege) and appends the outermost context frame.
   *
   * `trusted` is the one bootstrap privilege: a prelude may declare builtin bodies and the native Nat operations. A
   * program cannot, so nothing it declares can acquire kernel semantics it did not write.
   */
  private[raccoonlang] def evalDecl(decl: Decl, env: Env, trusted: Boolean): Env =
    framed(Frame.InDefinition(decl.label)) {
      at(decl.span) {
        decl match {
          case Decl.ConstDecl(isOpaque, name, ty, body, selectorOf, _) =>
            val installed = body match {
              case CoreAst.ConstBody.Builtin(_) =>
                if (isOpaque) wtf("Builtin declarations cannot be opaque")
                if (!trusted) fail(ReservedKernelName(name))
                val tyV = TypeChecker.checkDeclType(ty, env).value
                env.putGlobal(name, publishedValue(Builtins.instantiate(name, tyV), tyV))

              case CoreAst.ConstBody.TermBody(term) =>
                val checkedTy = TypeChecker.checkDeclType(ty, env).value
                // A global is never tracked, so none may be linear (spec §3.2).
                if (Linearity.isLinear(checkedTy)) at(ty.span)(fail(LinearGlobal(name, checkedTy)))
                val checked = TypeChecker.checkTerm(term, checkedTy, env)
                val value = if (isOpaque) VConst(name, Symbol, checkedTy) else checked.value
                val published =
                  if (trusted && Packed.opNames(name)) Packed.nativeOp(name, value, env)
                  else publishedValue(value, checkedTy)
                env.putGlobal(name, published)
            }
            // A sealed family's selectors are kept to its module, as its constructors are (spec §7.1).
            selectorOf.fold(installed) { family =>
              env(family) match {
                case VConst(_, Inductive(meta), _) => meta.seal.fold(installed)(installed.sealMember(name, _))
                case other                         => wtf(s"Selector $name belongs to $other, which is no family")
              }
            }

          case Decl.AxiomDecl(name, ty, _) =>
            val tyV = TypeChecker.checkDeclType(ty, env).value
            env.putGlobal(name, publishedValue(VConst(name, Symbol, tyV), tyV))

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
