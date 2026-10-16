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
    l.terms.foreach { case (id, k) =>
      val base = eqStore.subst.get(id) match {
        case Some(sol) =>
          eqStore.force(sol) match {
            case next: Level => normalizeLevel(next, eqStore)
            case other       => wtf(s"Level variable $id solved to the non-level $other")
          }
        case None => Level.mk(id)
      }
      pieces += Level.addOffset(base, k)
    }
    Level.max(pieces.result())
  }

  /**
   * Continues the reduction of v if any dependency that blocks it has been solved in EqStore. The default call (if v
   * cannot be further reduced) is a fast empty/intersection check, so callers may use it defensively.
   */
  private[raccoonlang] def resolveInEqStore(v: Value, eqStore: EqStore): Value =
    resolveInEqStore(v, ValueOps.newMaterializer(eqStore))

  /** The overload used inside one materialization root, so shared values and environments share its memo tables. */
  private[raccoonlang] def resolveInEqStore(v: Value, materializer: ValueOps.Materializer): Value = {
    val eqStore = materializer.eqStore
    val v0 = eqStore.force(v)
    v0 match {
      case Blocked(blockedOn) if blockedOn.intersects(eqStore.solvedIds) =>
        v0 match {
          case VBlockedApp(h, args, tpe, _) =>
            val h0 = materializer.materialize(materializer.resolve(h))
            val materializedArgs = args.map(materializer.materialize)
            h0 match {
              case lam: VLam =>
                val res = runLam(lam, materializedArgs)
                materializer.resolve(res)
              case nextHead @ Blocker(nextBlockedOn) =>
                VBlockedApp(nextHead, materializedArgs, tpe, nextBlockedOn)
              case other =>
                materializer.resolve(evalApply(other, materializedArgs))
            }
          case vm: NeutralThunk => materializer.resolve(forceThunk(vm, materializer))
          case _                => wtf(s"Blocked extractor matched unexpected value $v0")
        }

      case l: Level if l.synDeps.intersects(eqStore.solvedIds) => normalizeLevel(l, eqStore)

      case _ => v0
    }
  }

  /** Combine the levels of a data-valued function type; a telescope binding a level is classified as Large. */
  private[raccoonlang] def piClassifierFromChecked(
      binders: Vector[CoreAst.Binder],
      freshEnv: Env,
      outV: Value
  ): Classifier = {
    val freshValues = binders.map(binder => freshEnv(binder.localRef))
    if (freshValues.exists(_.tpe eq LevelTpe)) Large
    else {
      val outSort = TypeChecker.getUniverse(outV)
      if (Sorts.isProp(outSort)) Sorts.Prop
      else {
        val domainLevels = freshValues.map { fresh =>
          val domainSort = TypeChecker.getUniverse(fresh.tpe)
          if (Sorts.isProp(domainSort)) Level.zero else domainSort.level
        }
        Sorts.sort(Level.max(domainLevels :+ outSort.level))
      }
    }
  }

  private[raccoonlang] def evalPi(pi: CTerm.Pi, env: Env): VPi = {
    val capturedRefs = CapturedRefs.getCapturedRefs(pi, env)
    val closedEnv = env.closeForEval(capturedRefs)
    val captureVals = closedEnv.locals.values.toVector
    val id = ValueId.LocalId(pi.id, captureVals)

    val synDeps = DepSet.newBuilder
    captureVals.foreach { v =>
      synDeps.unionInPlace(v.synDeps)
    }

    lazy val freshEnv = BinderOps.freshen(pi.binders, closedEnv)
    lazy val outV = evalTerm(pi.out, freshEnv)
    lazy val classifier = piClassifierFromChecked(pi.binders, freshEnv, outV)
    val isPropValued = pi.knownPropValued.getOrElse(Sorts.isProposition(outV))

    VPi(
      closedEnv,
      pi.binders,
      codomain = env => evalTerm(pi.out, env),
      synDeps.result(),
      id,
      classifier0 = () => classifier,
      isPropValued = isPropValued
    )
  }

  private def evalRef(ref: CTerm.Ref, env: Env): Value = {
    val res = ref match {
      case CTerm.GlobalRef(name, _) => env(name)
      case CTerm.LocalRef(local, _) => env(local)
    }
    res match {
      case h: ConstructorHead if h.totalArity == 0 =>
        Value.canonicalizeProof(VCtor(h, Vector.empty, h.tpe))
      case _ => res
    }
  }

  private[raccoonlang] def evalApply(fn: Value, vArgs: Vector[Value]): Value = evalSteps(applyStep(fn, vArgs))

  private def applyStep(fn: Value, vArgs: Vector[Value]): Step = {
    fn.tpe match {
      case pi: VPi =>
        // Grouping is part of a function type's identity, so an application supplies exactly this
        // Pi's own binders. A nested group is reached by a second application, which arrives here
        // as its own call. Keep this boundary checked because native lambdas bypass Core evaluation.
        if (vArgs.length != pi.binders.length)
          fail(ArityMismatch(pi.binders.length, vArgs.length, ArityMismatch.Arguments))
        // Lazy: the VLam branch delegates env construction to runLam.
        lazy val envWithArgs = BinderOps.instantiateFull(pi.binders, pi.env, vArgs)
        fn match {
          case lam: VLam =>
            lamStep(lam, vArgs)
          case h: ConstructorHead =>
            val resultTy = pi.codomain(envWithArgs)
            val storedArgs = Value.constructorStoredArgs(h, vArgs)
            Step.Done(Value.canonicalizeProof(VCtor(h, storedArgs, resultTy)))
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

  private def evalApplyTerm(fn: CoreAst.Term, args: Vector[CoreAst.Term], env: Env): Step = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    if (vArgs.isEmpty) fail(CannotApplyNonFunction(vf.tpe))
    applyStep(vf, reconstructImplicits(vf, vArgs))
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
        if (vArgs.length != pi.numExplicit)
          fail(ArityMismatch(pi.numExplicit, vArgs.length, ArityMismatch.Arguments))
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
        case None           => ValueId.LocalId(l.id, closedEnv.locals.values.toVector)
      }
      Value.canonicalizeProof(VLam(vpi, id, LamBody.Core(l, closedEnv)))
    }
  }

  private[raccoonlang] def runLam(lam: VLam, args: Vector[Value]): Value = {
    evalSteps(lamStep(lam, args))
  }

  private def lamStep(lam: VLam, args: Vector[Value]): Step = {
    // Arguments are bound as supplied. A lambda's Pi is the one it was created with, so its binders
    // are exactly the ones its body expects.
    lazy val piEnv = BinderOps.instantiateFull(lam.tpe.binders, lam.tpe.env, args)

    lam.body match {
      case LamBody.Native(run, nativeEnv, _) => Step.Done(run(args, nativeEnv))
      case LamBody.ProofEta =>
        Step.Done(Value.canonicalizeProof(VProof(lam.tpe.codomain(piEnv))))
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
                .map(_.value)
                .getOrElse(wtf(s"Checked recursive peer $name is absent from its group"))
          current.putLocal(ref, peer)
        }
        Step.Tail(term.body, recurEnv)
    }
  }

  private def forceThunk(thunk: NeutralThunk, materializer: ValueOps.Materializer): Value =
    evalMatch(thunk.term, materializer.materializeEnv(thunk.env))

  private def evalLam(l: CTerm.Lam, env: Env): Value = evalLam(l, evalPi(l.ty, env), env)

  // A checked level expression denotes a normal form: checking admits nothing else at its position.
  private[raccoonlang] def getLevel(v: Value): Level =
    v match {
      case l: Level => l
      case other    => wtf(s"Checked level expression evaluated to the non-level $other")
    }

  private[raccoonlang] def evalFormOp(form: CoreAst.LevelForm, args: Vector[Value]): Value =
    form match {
      case CoreAst.LevelForm.LevelZero => Level.zero
      case CoreAst.LevelForm.LevelOne  => Level.one
      case CoreAst.LevelForm.LevelSucc => Level.succ(getLevel(args(0)))
      case CoreAst.LevelForm.LevelMax  => Level.max(args.map(getLevel))
    }

  /**
   * Evaluation attaches no location: reduction runs inside callee bodies the user did not write, so a failure here
   * belongs to the term the checker was working on.
   */
  private sealed trait Step
  private object Step {
    final case class Done(value: Value) extends Step
    final case class Tail(term: CoreAst.Term, env: Env) extends Step
  }

  private[raccoonlang] def evalTerm(term: CoreAst.Term, env: Env): Value = evalSteps(step(term, env))

  @tailrec
  private def evalSteps(next: Step): Value =
    next match {
      case Step.Done(value)     => value
      case Step.Tail(term, env) => evalSteps(step(term, env))
    }

  /** A block's result and a selected match branch are tail positions of their enclosing term. */
  private def step(term: CoreAst.Term, env: Env): Step =
    term match {
      case ref: CTerm.Ref         => Step.Done(evalRef(ref, env))
      case CTerm.App(fn, args, _) => evalApplyTerm(fn, args, env)
      case pi: CTerm.Pi           => Step.Done(evalPi(pi, env))
      case l: CTerm.Lam           => Step.Done(evalLam(l, env))
      case m: CTerm.Match         => matchStep(m, env)
      case b: CTerm.Body =>
        val withLets = b.lets.foldLeft(env) { case (curEnv, let) =>
          curEnv.putLocal(let.localRef, evalTerm(let.value, curEnv))
        }
        Step.Tail(b.res, withLets)
      case CTerm.Sort(level, _) =>
        Step.Done(Sorts.sort(getLevel(evalTerm(level, env))))
      case CTerm.Prop(_)               => Step.Done(Sorts.Prop)
      case CTerm.FormOp(form, args, _) => Step.Done(evalFormOp(form, args.map(evalTerm(_, env))))
      // Named field syntax is resolved to a selector application by checkSelect, so a Select can
      // only reach evaluation if something published unchecked syntax.
      case CTerm.Select(_, field, _) =>
        wtf(s"Unresolved field selection .$field reached evaluation")
    }

  private def evalMatch(m: CTerm.Match, env: Env): Value = evalSteps(matchStep(m, env))

  private def matchStep(m: CTerm.Match, env: Env): Step = {
    val scrut = evalTerm(m.scrut, env)
    val (ctorName, args) = scrut match {
      case ConstructorForm(name, storedArgs) => (name, storedArgs)
      case proof: VProof                     => return Step.Done(evalProofMatch(m, proof, env))
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
            return Step.Tail(branch.body, branchEnv(branch, etaFields, env))
          case None =>
        }
        // We are either blocked or stuck
        val headBlockers = other match {
          case Blocker(blockedOn) => blockedOn
          case _                  => DepSet.empty
        }
        val blockedOn = headBlockers
        return Step.Done(Value.canonicalizeProof(stuckMatchThunk(m, env, evalTerm(m.motive, env), blockedOn)))
    }

    // Exhaustiveness is settled by MatchChecker: a constructor-form scrutinee always has a branch.
    val branch =
      m.cases.find(c => c.ctorName == ctorName).getOrElse(wtf(s"Checked match has no branch for constructor $ctorName"))
    Step.Tail(branch.body, branchEnv(branch, args, env))
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

  private[raccoonlang] def evalBranch(branch: CoreAst.Case, args: Vector[Value], env: Env): Value = {
    evalTerm(branch.body, branchEnv(branch, args, env))
  }

  private def branchEnv(branch: CoreAst.Case, args: Vector[Value], env: Env): Env = {
    // Every caller supplies a scrutinee's stored fields to a branch MatchChecker already matched
    // against that constructor's arity.
    if (args.length != branch.argRefs.length)
      wtf(s"Checked branch for ${branch.ctorName} binds ${branch.argRefs.length} fields, got ${args.length}")
    args.zip(branch.argRefs).foldLeft(env) { case (curEnv, (argV, ref)) =>
      curEnv.putLocal(ref, Value.canonicalizeProof(argV))
    }
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

  /** Only the selected prelude may install primitive quotient bodies. */
  private[raccoonlang] def evalDecl(decl: Decl, env: Env, trusted: Boolean): Env =
    framed(Frame.InDefinition(decl.label)) {
      at(decl.span) {
        try
          decl match {
            case Decl.ConstDecl(name, ty, body, _) =>
              body match {
                case CoreAst.ConstBody.Builtin(_) =>
                  if (!trusted) fail(ReservedKernelName(name))
                  val tyV = TypeChecker.checkDeclType(ty, env).value
                  env.putGlobal(name, publishedValue(Builtins.instantiate(name, tyV), tyV))

                case CoreAst.ConstBody.TermBody(term) =>
                  val checkedTy = TypeChecker.checkDeclType(ty, env).value
                  val checked = TypeChecker.checkTerm(term, checkedTy, env)
                  val published = publishedValue(checked.value, checkedTy)
                  env.putGlobal(name, published)
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
        catch { case _: StackOverflowError => fail(EvaluationTooDeep) }
      }
    }

  /** Execute a checked program. Checking and declaration publication have already happened. */
  def run(program: Execution.CheckedProgram): Option[Value] = program.result

  /** Compatibility entry point for implementation code and same-package kernel tests. */
  private[raccoonlang] def run(p: Program, prelude: Prelude.Config = Prelude.default): Option[Value] =
    TypeChecker.checkRaw(p, prelude)

  private[raccoonlang] val preludeInitialEnv: Env = Env.empty.putGlobal("Level", LevelTpe)

  private[raccoonlang] def addPreludeDecl(env: Env, decl: Decl): Env = evalDecl(decl, env, trusted = true)

  private[raccoonlang] def buildPreludeEnv(core: Program): Env =
    core.decls.foldLeft(preludeInitialEnv)(addPreludeDecl)
}
