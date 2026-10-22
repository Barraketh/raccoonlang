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

  /** The solution of a solved kind variable, which refinement links only to a normal form of its own. */
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
          case prefix: VNatPrefix =>
            Packed.natPrefix(
              materializer.materialize(prefix.base),
              prefix.offset,
              materializer.materialize(prefix.tpe)
            )
          case vm: NeutralThunk => resolveInEqStore(forceThunk(vm, materializer), materializer)
          case _                => wtf(s"Blocked extractor matched unexpected value $v0")
        }

      case l: Level if l.synDeps.intersects(eqStore.solvedIds) => normalizeLevel(l, eqStore)
      case k: Kind if k.synDeps.intersects(eqStore.solvedIds)  => normalizeKind(k, eqStore)
      case _                                                   => v0
    }
  }

  /**
   * Arguments are bound exactly as supplied: a value's type annotation is what it was created with, and no site
   * rewrites it. Binder types are evaluated against the Pi's own closure — their syntax is valid there, not in the body
   * env the values are later bound into.
   */
  /**
   * A Pi into Prop is impredicative and unrestricted; a data Pi takes the maximum of its domain and codomain levels.
   * Proposition domains contribute zero. A level binder makes the Pi Large.
   */
  private[raccoonlang] def piClassifierFromChecked(
      binders: Vector[CoreAst.Binder],
      freshEnv: Env,
      outV: Value,
      closureKind: Kind
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
      if (Sorts.isProp(outSort)) Sorts.Prop
      else Sorts.sort(Level.max(domSorts.map(_.level) :+ outSort.level), closureKind)
    }
  }

  private def piClassifier(
      binders: Vector[CoreAst.Binder],
      baseEnv: Env,
      out: CoreAst.Term,
      closureKind: Kind
  ): Classifier = {
    val freshEnv = BinderOps.freshen(binders, baseEnv)
    piClassifierFromChecked(binders, freshEnv, evalTerm(out, freshEnv), closureKind)
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

  /** An axiom ending in a sort is a type former, whose arguments projection reads. */
  private def axiomHead(tpe: Value): ConstType = {
    @tailrec
    def telescope(tpe: Value): ConstType =
      tpe match {
        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          telescope(pi.codomain(freshEnv))
        case _: VSort => TypeFormer
        case _        => Symbol
      }
    telescope(tpe)
  }

  private[raccoonlang] def evalPi(pi: CTerm.Pi, env: Env): VPi = {
    val capturedRefs = CapturedRefs.getCapturedRefs(pi, env)
    val closedEnv = env.closeForEval(capturedRefs)
    val captureVals = closedEnv.locals.values.toVector
    val id = ValueId.LocalId(pi.id, captureVals)
    val closureKind = evalClosureField(pi.closure.kind, Sorts.KindField, env)

    val synDeps = DepSet.newBuilder
    captureVals.foreach { v =>
      synDeps.unionInPlace(v.synDeps)
    }
    synDeps.unionInPlace(closureKind.synDeps)

    val codomain =
      new CheckedPiCodomain(pi.binders, pi.codomainIndependent, Some(pi.codomainBinderIndices), closedEnv) {
        override def apply(env: Env): Value = evalTerm(pi.out, env)
      }

    VPi(
      closedEnv,
      pi.binders,
      codomain,
      closureKind,
      synDeps.result(),
      id,
      classifier0 = () => piClassifier(pi.binders, closedEnv, pi.out, closureKind),
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

  private[raccoonlang] def evalApply(fn: Value, vArgs: Vector[Value]): Value =
    CoreEvaluator.evalApply(fn, vArgs)

  private[raccoonlang] def evalValidatedStringAppend(layout: SourceStringLayout, chars: VPacked): Value = {
    require(chars.codec eq layout.charListCodec, "Validated String.append result has a different CharList codec")
    CoreEvaluator.evalValidatedStringAppend(layout, chars)
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
  private[raccoonlang] def residualArguments(fn: Value, vArgs: Vector[Value]): Vector[Value] =
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

  private[raccoonlang] def runLam(lam: VLam, args: Vector[Value]): Value =
    CoreEvaluator.evalApply(lam, args)

  private[raccoonlang] def runLamWithRecursivePeers(
      lam: VLam,
      args: Vector[Value],
      peers: Vector[Value]
  ): Value =
    CoreEvaluator.evalApplyWithRecursivePeers(lam, args, peers)

  private def forceThunk(thunk: NeutralThunk, materializer: ValueOps.Materializer): Value =
    evalTerm(thunk.term, materializer.materializeEnv(thunk.env))

  /** The value that is a sort parameter's type, which a variable of it and an expression of it have. */
  private[raccoonlang] def parameterType(parameter: CoreAst.Parameter): ParameterTpe =
    parameter match {
      case CoreAst.Parameter.Level => LevelTpe
      case CoreAst.Parameter.Kind  => KindTpe
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

  private[raccoonlang] def evalFormOp(form: CoreAst.Form, args: Vector[Value]): Value =
    form match {
      case CoreAst.Form.LevelZero => Level.zero
      case CoreAst.Form.LevelOne  => Level.one
      case CoreAst.Form.LevelSucc => Level.succ(getLevel(args(0)))
      case CoreAst.Form.LevelMax  => Level.max(args.map(getLevel))
      case CoreAst.Form.KindUnr   => Kind.unr
      case CoreAst.Form.KindLin   => Kind.lin
      case CoreAst.Form.KindJoin  => Kind.join(args.map(getKind))
    }

  /** Evaluation attaches no source location: reduction can run inside a callee body. */
  private[raccoonlang] def evalTerm(term: CoreAst.Term, env: Env): Value = CoreEvaluator.evalTerm(term, env)

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
  private[raccoonlang] def branchEnv(
      m: CTerm.Match,
      branch: CoreAst.Case,
      scrut: Value,
      args: Vector[Value],
      env: Env
  ): Env = {
    // Every caller supplies a scrutinee's stored fields to a branch MatchChecker already matched
    // against that constructor's arity.
    val layout = branch.runtimeSlotLayout
    if (args.length != layout.size)
      wtf(s"Checked branch for ${branch.ctorName} binds ${layout.size} fields, got ${args.length}")
    val fieldsEnv = bindRuntimeFields(args, env, layout)
    m.equation.fold(fieldsEnv)(equation =>
      fieldsEnv.putLocal(equation.ref, matchEquationEvidence(branch.ctorName, scrut, args, env))
    )
  }

  /** The equation is validated where the match stands and remains lazy when bound to a branch. */
  private[raccoonlang] def matchEquationEvidence(
      ctorName: String,
      scrut: Value,
      args: Vector[Value],
      env: Env
  ): DeferredEvidence = {
    val equality = env.equality.fold(reason => wtf(s"A checked match equation reached an env where $reason"), identity)
    val ctor = env(ctorName) match {
      case head: ConstructorHead => head
      case other                 => wtf(s"Checked case $ctorName names $other, not a constructor")
    }
    new DeferredEvidence(() => MatchEquation.proposition(equality, scrut, ctor, args))
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
  private[raccoonlang] def bindRuntimeLet(pattern: CoreAst.LetPattern, value: Value, env: Env): Env =
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
  private[raccoonlang] def evalProofMatch(m: CTerm.Match, scrut: VProof, env: Env): Value = {
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
                  val builtinValue =
                    if (name == NativeBufferBuiltins.Name) NativeBufferBuiltins.instantiate(name, tyV, env)
                    else Builtins.instantiate(name, tyV)
                  env.putGlobal(name, publishedValue(builtinValue, tyV))

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
              env.putGlobal(name, publishedValue(VConst(name, axiomHead(tyV), tyV), tyV))

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
