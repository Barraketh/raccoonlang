package com.raccoonlang

import com.raccoonlang.CoreAst.{Decl, Program, Term}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.{BinderOps, Projection}

/** The runtime evaluator; static validation is performed by TypeChecker. */
object Interpreter {
  val builtins: Env = {
    val base = Env.empty
      .putGlobal("Type", TypeTpe)
      .putGlobal("Prop", PropTpe)
      .putGlobal("Level", LevelTpe)
      .putGlobal("Level.zero", Level.zero)
      .putGlobal("Level.one", Level.one)
    base
      .putGlobal("Sort", sortBuiltin)
      .putGlobal("Level.succ", unaryLevelBuiltin("Level.succ", Level.succ))
      .putGlobal("Level.max", binaryLevelBuiltin("Level.max", (a, b) => Level.max(Vector(a, b))))
      .putGlobal("Level.imax", binaryLevelBuiltin("Level.imax", Level.imax))
  }

  /** Bootstrap constants available before the source prelude itself is admitted. */
  private[raccoonlang] val preludeInitialEnv: Env =
    Env.empty
      .putGlobal("Type", TypeTpe)
      .putGlobal("Prop", PropTpe)
      .putGlobal("Level", LevelTpe)
      .putGlobal("Level.zero", Level.zero)
      .putGlobal("Level.one", Level.one)

  private[raccoonlang] def buildEmptyPreludeEnv(program: Program): Env =
    Packed.finalizeTrustedBootstrap(TypeChecker.checkProgramTrusted(program, builtins)._1)

  /** Check and publish the selected source prelude once, including packed literal capabilities. */
  private[raccoonlang] def buildPreludeEnv(program: Program): Env =
    Packed.finalizeTrustedBootstrap(TypeChecker.checkProgramTrusted(program, preludeInitialEnv)._1)

  private def builtinPi(ref: CoreAst.LocalRef, ty: Value, out: Env => Value): VPi =
    VPi(
      Env.empty.putGlobal("Type", TypeTpe).putGlobal("Level", LevelTpe),
      Vector(
        CoreAst.Binder(ref, CoreAst.Term.GlobalRef(if (ty == LevelTpe) "Level" else "Type", Span(0, 0)), Span(0, 0))
      ),
      out,
      DepSet.empty,
      ValueId.Const(ref.name),
      () => TypeTpe
    )

  private def unaryLevelBuiltin(name: String, f: Level => Level): Value = {
    val ref = CoreAst.LocalRef(-1001, "u")
    val pi = builtinPi(ref, LevelTpe, _ => LevelTpe)
    VLam(
      pi,
      ValueId.Const(name),
      LamBody.Native((args, _) => f(getLevel(args.head)), Env.empty, isRawRecursive = false)
    )
  }

  private def binaryLevelBuiltin(name: String, f: (Level, Level) => Level): Value = {
    val a = CoreAst.LocalRef(-1002, "u")
    val b = CoreAst.LocalRef(-1003, "v")
    val binderA = CoreAst.Binder(a, CoreAst.Term.GlobalRef("Level", Span(0, 0)), Span(0, 0))
    val binderB = CoreAst.Binder(b, CoreAst.Term.GlobalRef("Level", Span(0, 0)), Span(0, 0))
    val pi = VPi(
      Env.empty.putGlobal("Type", TypeTpe).putGlobal("Level", LevelTpe),
      Vector(binderA, binderB),
      _ => LevelTpe,
      DepSet.empty,
      ValueId.Const(name),
      () => TypeTpe
    )
    VLam(
      pi,
      ValueId.Const(name),
      LamBody.Native((args, _) => f(getLevel(args(0)), getLevel(args(1))), Env.empty, false)
    )
  }

  private lazy val sortBuiltin: Value = {
    val ref = CoreAst.LocalRef(-1004, "u")
    val binder = CoreAst.Binder(ref, CoreAst.Term.GlobalRef("Level", Span(0, 0)), Span(0, 0))
    val pi = VPi(
      Env.empty.putGlobal("Type", TypeTpe).putGlobal("Level", LevelTpe),
      Vector(binder),
      applied => VSort(Level.succ(getLevel(applied(ref)))),
      DepSet.empty,
      ValueId.Const("Sort"),
      () => TypeTpe
    )
    VLam(pi, ValueId.Const("Sort"), LamBody.Native((args, _) => VSort(getLevel(args.head)), Env.empty, false))
  }

  def evalPi(pi: Term.Pi, env: Env): VPi = {
    val closed = env.closeForEval(CapturedRefs.getCapturedRefs(pi, env))
    evalPiClosed(pi, closed)
  }

  def rigidBinderValue(ref: CoreAst.LocalRef, tpe: Value): Value =
    FreshVar.freshVar(ref.name, tpe)

  private[raccoonlang] def piClassifierFromChecked(
      binders: Vector[CoreAst.Binder],
      freshEnv: Env,
      outValue: Value
  ): VSort = {
    val outLevel = TypeChecker.getUniverse(outValue).level
    val domLevels = binders.map(b => TypeChecker.getUniverse(freshEnv(b.localRef).tpe).level)
    val level =
      if (outLevel == Level.zero) Level.zero
      else if (Level.isNeverZero(outLevel)) Level.max(domLevels :+ outLevel)
      else domLevels.foldRight(outLevel)(Level.imax)
    VSort(level)
  }

  private[raccoonlang] def stablePiPropClassification(outValue: Value): Option[Boolean] = {
    val VSort(level) = TypeChecker.getUniverse(outValue)
    if (level == Level.zero) Some(true)
    else if (Level.isNeverZero(level)) Some(false)
    else None
  }

  private def piClassifier(binders: Vector[CoreAst.Binder], baseEnv: Env, out: CoreAst.Term): VSort = {
    val freshEnv = com.raccoonlang.telescope.BinderOps.freshen(binders, baseEnv)
    piClassifierFromChecked(binders, freshEnv, evalTerm(out, freshEnv))
  }

  /** Continue reduction when an EqStore solved a value's blocker. */
  def resolveInEqStore(value: Value, store: EqStore): Value = {
    val forced = store.force(value)
    forced match {
      case VApp(head, args, tpe, blocked) if blocked.intersects(store.solvedIds) =>
        val resolvedHead = ValueOps.materialize(resolveInEqStore(head, store), store)
        val resolvedArgs = args.map(ValueOps.materialize(_, store))
        resolvedHead match {
          case lambda: VLam                => resolveInEqStore(evalApply(lambda, resolvedArgs), store)
          case next @ Blocker(nextBlocked) => VApp(next, resolvedArgs, ValueOps.materialize(tpe, store), nextBlocked)
          case other                       => resolveInEqStore(evalApply(other, resolvedArgs), store)
        }
      case thunk: NeutralThunk if thunk.blockedOn.intersects(store.solvedIds) =>
        resolveInEqStore(evalTerm(thunk.term, ValueOps.materializeEnv(thunk.env, store)), store)
      case level: Level if level.synDeps.intersects(store.solvedIds) =>
        val pieces = Vector.newBuilder[Level]
        if (level.c > 0 || level.terms.isEmpty) pieces += Level.const(level.c)
        level.terms.foreach { case (atom, offset) =>
          val base = atom match {
            case Level.ParamAtom(id) =>
              store.subst
                .get(id)
                .map(v =>
                  resolveInEqStore(v, store) match {
                    case l: Level        => l
                    case Var(_, next, _) => Level.mk(next)
                    case other           => throw NotALevel(other)
                  }
                )
                .getOrElse(Level.mk(id))
            case Level.IMaxAtom(lhs, rhs) =>
              Level.imax(
                resolveInEqStore(lhs, store).asInstanceOf[Level],
                resolveInEqStore(rhs, store).asInstanceOf[Level]
              )
          }
          pieces += Level.addOffset(base, offset)
        }
        Level.max(pieces.result())
      case _ => forced
    }
  }

  def evalPiClosed(pi: Term.Pi, env: Env): VPi = {
    // Keep the closure contract at this boundary as well as in evalPi.  A caller may have
    // constructed an Env containing more locals than this Pi mentions (notably while publishing
    // a checked lambda); retaining those locals would make closure identity and dependencies
    // depend on evaluation history rather than on the residual syntax.
    val closedEnv = env.closeForEval(CapturedRefs.getCapturedRefs(pi, env))
    val runtimeBinders =
      if (pi.binders.exists(b => b.isImplicit && b.projection.isEmpty)) BinderOps.compileRuntime(pi.binders, closedEnv)
      else pi.binders
    val classifier = () => piClassifier(pi.binders, closedEnv, pi.out)
    val captures = closedEnv.locals.values.toVector
    VPi(
      closedEnv,
      runtimeBinders,
      bodyEnv => evalTerm(pi.out, bodyEnv),
      closedEnv.dependencies,
      Value.ValueId.LocalId(pi.nodeId, captures),
      classifier,
      pi.knownPropValued
    )
  }

  def evalTerm(term: Term, env: Env): Value = term match {
    case Term.GlobalRef(name, _) =>
      env(name) match {
        case head: ConstructorHead if head.totalArity == 0 =>
          Value.canonicalizeProof(
            Packed.foldCtor(head, Vector.empty, head.tpe).getOrElse(VCtor(head, Vector.empty, head.tpe))
          )
        case value => value
      }
    case Term.LocalRef(ref, _)          => env(ref)
    case Term.NatLit(value, _)          => Packed.evalNatLit(value, env)
    case Term.StrLit(scalars, _)        => Packed.evalStrLit(scalars, env)
    case Term.Select(base, field, span) => evalSelect(evalTerm(base, env), field, env, span)
    case pi: Term.Pi                    => evalPi(pi, env)
    case lam: Term.Lam                  => evalLam(lam, env)
    case Term.App(fn, args, span) =>
      val values = args.map(arg => evalTerm(arg, env))
      val vf = evalTerm(fn, env)
      evalApply(vf, reconstructImplicits(vf, values, span))
    case Term.Body(lets, result, _) =>
      evalBody(lets, result, env)
    case matchTerm: Term.Match => evalMatch(matchTerm, env)
  }

  def getLevel(v: Value): Level = Level.fromValue(v).getOrElse(throw NotALevel(v))

  private def evalSelect(base0: Value, field: String, env: Env, span: Span): Value = {
    val base = base0 match {
      case head: ConstructorHead if head.totalArity == 0 => VCtor(head, Vector.empty, head.tpe)
      case value                                         => value
    }
    base.tpe match {
      case InductiveFamilyValue(instance) =>
        val fn = env(s"${instance.head.name}.$field")
        evalApply(fn, reconstructImplicits(fn, Vector(base), span))
      case _ => throw NotFound(field, Some(span))
    }
  }

  private def evalMatch(matchTerm: Term.Match, env: Env): Value = {
    val scrut = evalTerm(matchTerm.scrut, env) match {
      case head: ConstructorHead if head.totalArity == 0 => VCtor(head, Vector.empty, head.tpe)
      case value                                         => value
    }
    scrut match {
      case proof: VProof => return evalProofMatch(matchTerm, proof, env)
      case _             =>
    }
    val cases = matchTerm.cases
    val selected = Value.ConstructorForm
      .unapply(scrut)
      .orElse(scrut match {
        case p: VPacked => Some(p.codec.decodeHead(p))
        case _          => None
      })
    selected match {
      case Some((name, fields)) =>
        cases.find(c => c.ctorName == name || c.ctorName == name.split('.').last) match {
          case None => throw WTF(s"No match case for $name at ${matchTerm.span}")
          case Some(branch) =>
            if (branch.argRefs.length != fields.length) throw ArityMismatch(fields.length, branch.argRefs.length)
            evalBranch(branch, fields, env)
        }
      case None =>
        StructEta.fields(scrut) match {
          case Some(fields) if cases.length == 1 =>
            evalBranch(cases.head, fields, env)
          case Some(_) => throw WTF(s"Eta-eligible struct match has ${cases.length} cases at ${matchTerm.span}")
          case None =>
            val outType = matchOutType(matchTerm, scrut, env)
            val closed = env.closeForEval(CapturedRefs.getCapturedRefs(matchTerm, env))
            val blockedOn = Blocker.unapply(scrut).getOrElse(DepSet.empty) ++ typeCollapseDeps(scrut.tpe)
            Value.canonicalizeProof(
              NeutralThunk(
                matchTerm,
                closed,
                ValueId.LocalId(matchTerm.nodeId, closed.locals.values.toVector),
                outType,
                blockedOn
              )
            )
        }
    }
  }

  /** Erased proof elimination with declaration-certified recovery for safe large elimination. */
  private def evalProofMatch(matchTerm: Term.Match, scrut: VProof, env: Env): Value = {
    val outType = matchOutType(matchTerm, scrut, env)
    if (Value.isPropositionType(outType)) Value.canonicalizeProof(VProof(outType))
    else stuckProofMatch(matchTerm, env, outType, scrut.tpe.synDeps)
  }

  private def stuckProofMatch(term: Term.Match, env: Env, outType: Value, blockedOn: DepSet): NeutralThunk = {
    val closed = env.closeForEval(CapturedRefs.getCapturedRefs(term, env))
    NeutralThunk(term, closed, ValueId.LocalId(term.nodeId, closed.locals.values.toVector), outType, blockedOn)
  }

  private[raccoonlang] def matchOutType(matchTerm: Term.Match, scrut: Value, env: Env): Value =
    matchTerm.motive.map(evalTerm(_, env)).getOrElse(scrut.tpe)

  /** Dependencies whose universe can still collapse a generic type into Prop. */
  private[raccoonlang] def typeCollapseDeps(tpe: Value): DepSet = {
    val classifierLevel = TypeChecker.getUniverse(tpe).level
    if (Level.isNeverZero(classifierLevel)) DepSet.empty else classifierLevel.synDeps
  }

  private[raccoonlang] def evalBranch(branch: CoreAst.Case, fields: Vector[Value], env: Env): Value = {
    if (branch.argRefs.length != fields.length) throw ArityMismatch(fields.length, branch.argRefs.length)
    val branchEnv = branch.argRefs.zip(fields).foldLeft(env) {
      case (current, (Some(ref), value)) => current.putLocal(ref, Value.canonicalizeProof(value))
      case (current, (None, _))          => current
    }
    evalTerm(branch.body, branchEnv)
  }

  private def evalBody(lets: Vector[CoreAst.Let], result: Term, env: Env): Value = {
    val bodyEnv = lets.foldLeft(env) { case (current, let) =>
      current.putLocal(let.localRef, Value.canonicalizeProof(evalTerm(let.value, current)))
    }
    evalTerm(result, bodyEnv)
  }

  def evalApply(fn: Value, args: Vector[Value]): Value = {
    val canonicalArgs = args.map(Value.canonicalizeProof)
    fn.tpe match {
      case pi: VPi =>
        if (canonicalArgs.length != pi.binders.length) throw ArityMismatch(pi.binders.length, canonicalArgs.length)
        // The checked evaluator has already validated these arguments.  Runtime application also
        // serves the deliberately unchecked evaluator, where inferred constructor/family values
        // need only be threaded through the telescope; type validation belongs to TypeChecker.
        val applied = BinderOps.instantiateFull(pi.binders, pi.env, canonicalArgs)
        fn match {
          case lam: VLam => Value.canonicalizeProof(runLam(lam, canonicalArgs))
          case head: ConstructorHead =>
            val stored = Value.constructorStoredArgs(head, canonicalArgs)
            val folded =
              Packed.foldCtor(head, stored, pi.codomain(applied)).getOrElse(VCtor(head, stored, pi.codomain(applied)))
            Value.canonicalizeProof(folded)
          case _: VProof =>
            Value.canonicalizeProof(VProof(pi.codomain(applied)))
          case value @ (_: VConst | _: VApp | _: NeutralThunk | _: Var) =>
            val blocked = Blocker.unapply(value).getOrElse(DepSet.empty)
            Value.canonicalizeProof(VApp(value, canonicalArgs, pi.codomain(applied), blocked))
          case _ => throw CannotApplyNonFunction(fn)
        }
      case _ => throw CannotApplyNonFunction(fn)
    }
  }

  /** Runtime Core applications retain only explicit arguments; reconstruct the same projections as checking. */
  private def reconstructImplicits(fn: Value, provided: Vector[Value], span: Span): Vector[Value] = fn.tpe match {
    case pi: VPi if pi.binders.exists(_.isImplicit) =>
      if (provided.length != pi.numExplicit) throw ArityMismatch(pi.numExplicit, provided.length, Some(span))
      var explicit = 0
      pi.binders.map { binder =>
        if (!binder.isImplicit) { val value = provided(explicit); explicit += 1; value }
        else {
          binder.projection match {
            case None => throw WTF(s"Implicit binder ${binder.name} has no projection spec", Some(span))
            case Some(spec) =>
              Projection.project(spec, provided) match {
                case Right(value) => value
                case Left(reason) => throw ImplicitReconstructionFailed(binder.name, "application", reason, Some(span))
              }
          }
        }
      }
    case _ => provided
  }

  def resultType(pi: VPi, args: Vector[Value]): Value = {
    if (args.length != pi.binders.length) throw ArityMismatch(pi.binders.length, args.length)
    val applied = pi.binders.zip(args).foldLeft(pi.env) { case (current, (binder, value)) =>
      current.putLocal(binder.localRef, Value.canonicalizeProof(value))
    }
    pi.codomain(applied)
  }

  private[raccoonlang] def evalLam(lam: Term.Lam, env: Env): VLam = {
    val vpi = evalPiClosed(lam.ty, env)
    if (vpi.isPropValued) return Value.canonicalizeProof(VProof(vpi)).asInstanceOf[VLam]
    val closure = env.closeForEval(CapturedRefs.getCapturedRefs(lam, env))
    val id =
      lam.name.map(Value.ValueId.Const).getOrElse(Value.ValueId.LocalId(lam.nodeId, closure.locals.values.toVector))
    VLam(vpi, id, Value.LamBody.Core(lam, closure))
  }

  private[raccoonlang] def evalLam(lam: Term.Lam, vpi: VPi, env: Env): VLam = {
    if (vpi.isPropValued) return Value.canonicalizeProof(VProof(vpi)).asInstanceOf[VLam]
    val closure = env.closeForEval(CapturedRefs.getCapturedRefs(lam, env))
    val id =
      lam.name.map(Value.ValueId.Const).getOrElse(Value.ValueId.LocalId(lam.nodeId, closure.locals.values.toVector))
    VLam(vpi, id, Value.LamBody.Core(lam, closure))
  }

  def runLam(lam: VLam, args: Vector[Value]): Value = lam.body match {
    case Value.LamBody.ProofEta =>
      val applied = lam.tpe.binders.zip(args).foldLeft(lam.tpe.env) { case (current, (binder, value)) =>
        current.putLocal(binder.localRef, Value.canonicalizeProof(value))
      }
      Value.canonicalizeProof(VProof(lam.tpe.codomain(applied)))
    case Value.LamBody.Core(term, closure) =>
      if (args.length != lam.tpe.binders.length) throw ArityMismatch(lam.tpe.binders.length, args.length)
      val applied = lam.tpe.binders.zip(args).foldLeft(closure) { case (current, (binder, value)) =>
        current.putLocal(binder.localRef, value)
      }
      val withPeers = term.recursivePeers.foldLeft(term.recursion match {
        case Some(recursion) => applied.putLocal(recursion.selfRef, lam)
        case None            => applied
      }) { case (current, (ref, name)) =>
        if (current.locals.contains(ref)) current
        else if (term.recursion.exists(_.selfRef == ref)) current.putLocal(ref, lam)
        else current.putLocal(ref, closure(name))
      }
      Value.canonicalizeProof(evalTerm(term.body, withPeers))
    case LamBody.Native(run, nativeEnv, _) =>
      if (args.length != lam.tpe.binders.length) throw ArityMismatch(lam.tpe.binders.length, args.length)
      Value.canonicalizeProof(run(args, nativeEnv))
  }

  def evalDecl(decl: Decl, env: Env): Env = decl match {
    case Decl.ConstDecl(isOpaque, name, ty, body, _) =>
      body match {
        case CoreAst.ConstBody.Builtin(span) =>
          throw ReservedKernelName(name, Some(span))
        case CoreAst.ConstBody.TermBody(term) =>
          val valueType = evalTerm(ty, env)
          if (isOpaque) env.putOpaque(name, valueType) else env.putGlobal(name, evalTerm(term, env))
      }
    case Decl.AxiomDecl(name, ty, _)            => env.putOpaque(name, evalTerm(ty, env))
    case d: Decl.InductiveDecl                  => InductiveChecks.evalInductive(d, env)
    case block: Decl.InductiveBlock             => InductiveChecks.evalInductiveBlock(block, env)
    case Decl.RecursiveDefBlock(definitions, _) => evalRecursive(definitions, env)
  }

  private def evalRecursive(definitions: Vector[CoreAst.RecursiveDef], env: Env): Env = {
    val names = definitions.map(_.name)
    env.putRecursiveGroup(
      names,
      groupEnv => {
        val peers = definitions.map(definition => definition.peerRef -> definition.name)
        definitions.map { definition =>
          val recursion = CoreAst.Recursion(definition.peerRef, definition.decreases)
          val lambda = Term.Lam(
            definition.ty,
            definition.body,
            definition.span,
            Some(definition.name),
            Some(recursion),
            peers
          )
          evalLam(lambda, groupEnv) match {
            case value: VLam => value
            case other       => throw WTF(s"Recursive definition ${definition.name} produced $other")
          }
        }
      }
    )
  }

  /**
   * Publish a recursive group whose Pi types and lambda residuals have already been checked.
   *
   * The ordinary [[evalRecursive]] path is intentionally still available for the unchecked interpreter. The checker
   * must use this path instead: evaluating a checked declaration by feeding its residual back through declaration
   * evaluation would run the checker a second time and make the source syntax, rather than the checked residual/value,
   * authoritative.
   */
  private[raccoonlang] def publishCheckedRecursive(
      definitions: Vector[(CoreAst.RecursiveDef, VPi)],
      env: Env
  ): Env = {
    val names = definitions.map(_._1.name)
    env.putRecursiveGroup(
      names,
      groupEnv =>
        definitions.map { case (definition, vpi) =>
          val lambda = Term.Lam(
            definition.ty,
            definition.body,
            definition.span,
            Some(definition.name),
            recursion = None,
            recursivePeers = definitions.map { case (peer, _) => peer.peerRef -> peer.name }
          )
          evalLam(lambda, vpi, groupEnv) match {
            case value: VLam => value
            case other       => throw WTF(s"Checked recursive definition ${definition.name} produced $other")
          }
        }
    )
  }

  def run(program: Program, initial: Env = builtins): Option[Value] = {
    val env = program.decls.foldLeft(initial) { case (current, decl) => evalDecl(decl, current) }
    program.body.map(evalTerm(_, env))
  }

  /** Source-facing entry point: ordinary declarations start from the selected checked prelude. */
  def run(program: Program, prelude: Prelude.Config): Option[Value] =
    run(program, prelude.checkedEnv)
}
