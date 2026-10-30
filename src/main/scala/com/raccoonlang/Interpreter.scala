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

  /** A kind with each solved variable replaced by its solution's normal form, so joins collapse as they normalize. */
  private def normalizeKind(k: Kind, eqStore: EqStore): Kind =
    k.vars.foldLeft(if (k.lin) Kind.lin else Kind.copy) { (joined, atom) =>
      val solved = eqStore.subst.get(atom) match {
        case Some(sol) =>
          eqStore.force(sol) match {
            case next: Kind    => normalizeKind(next, eqStore)
            case Var(_, id, _) => Kind.mk(id)
            case other         => throw NotAKind(other)
          }
        case None => Kind.mk(atom)
      }
      Kind.join(joined, solved)
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
      case k: Kind if k.vars.exists(eqStore.subst.contains)                    => normalizeKind(k, eqStore)

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
    case lit: ETerm.NatLit      => lit.value
    case lit: ETerm.StrLit      => lit.value
    case word: ETerm.Word       => evalWord(word, env)
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
          // A neutral function with nothing to wait on, such as a field projection of an axiom or a stuck application
          // of one, applies to a neutral application (KERNEL_FOLLOWUPS 1.3).
          case neutral @ (_: NeutralThunk | _: VApp) => VApp(neutral, vArgs, pi.codomain(envWithArgs))
          case _                                     => throw CannotApplyNonFunction(fn)
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

  def evalLam(l: ETerm.Lam, vpi: VPi, env: Env): VLam =
    evalLam(l, vpi, env, CapturedIndexes.getCapturedIndexes(l, env))

  /** `capturedIndexes` are `CapturedIndexes.getCapturedIndexes(l, env)`, which the checker also reads. */
  def evalLam(l: ETerm.Lam, vpi: VPi, env: Env, capturedIndexes: RoaringBitmap): VLam = {
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

        // Update env with recursive reference; a member of a mutual block reads its block's members from the globals
        // its environment was closed over, where the block is published.
        val selfEnv = term.recursiveSelf match {
          case Some(ref) => bodyEnv.putLocal(ref, lam)
          case None      => bodyEnv
        }
        val recurEnv = term.recursivePeers.foldLeft(selfEnv) { case (env, (ref, name)) =>
          env.putLocal(ref, coreEnv(name))
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

  def getKind(v: Value): Kind =
    v match {
      case k: Kind => k
      case v: Var  => Kind.mk(v.id)
      case v       => throw NotAKind(v)
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

  /**
   * A word, rebuilt from the back in one loop: the last splice is the end, each layer is consed onto the rest, whose
   * type is the layer's since a list-shaped family has no indices, and each other splice is appended to the rest by the
   * kernel `List` 's native. So evaluating a quotation rebuilds the value it was quoted from.
   */
  private def evalWord(word: ETerm.Word, env: Env): Value = {
    val head = env(word.consHead.name) match {
      case head: ConstructorHead => head
      case other => throw WTF(s"Word head ${word.consHead.name} is not a constructor: $other", Some(word.span))
    }
    var rest = evalTerm(word.pieces.last.asInstanceOf[ETerm.WordPiece.Splice].list, env)
    var index = word.pieces.length - 2
    while (index >= 0) {
      rest = word.pieces(index) match {
        case ETerm.WordPiece.Layer(before, after) =>
          val stored = before.drop(head.numErased).map(evalTerm(_, env)) ++ (rest +: after.map(evalTerm(_, env)))
          ConstructorValue(head, stored, rest.tpe)
        case ETerm.WordPiece.Splice(list) => packed.Words.append(evalTerm(list, env), rest)
      }
      index -= 1
    }
    rest
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

  private def evalMatch(m: ETerm.Match, env: Env): Value = evalMatchOn(m, evalTerm(m.scrut, env), env)

  /**
   * The match `m` on the value `scrut`, its scrutinee in `env`. A constructor selects its branch. A value at a
   * structure eta type takes the one branch with its eta view, its field projections (`StructEta`). Any other value is
   * stuck.
   */
  private[raccoonlang] def evalMatchOn(m: ETerm.Match, scrut: Value, env: Env): Value = {
    val (ctorName, args) = scrut match {
      case ConstructorValue(head, fields) => (head.name, fields)
      case _ =>
        StructEta.fields(scrut).filter(_ => m.cases.length == 1) match {
          case Some(fields) => (m.cases.head.ctorName, fields)
          case None         =>
            // We are either blocked or stuck
            val outType: Value = m.motive match {
              case Some(motive) => evalTypeTerm(motive, env)
              case None         => scrut.tpe
            }
            return stuckMatch(m, scrut, env, outType)
        }
    }

    val branch =
      m.cases.find(c => c.ctorName == ctorName).getOrElse(throw UnknownConstructor(ctorName, "", Some(m.span)))
    if (args.length != branch.argRefs.length)
      throw ArityMismatch(branch.argRefs.length, args.length, Some(branch.span))
    val fieldsEnv = args.zip(branch.argRefs).foldLeft(env) { case (curEnv, (argV, argRef)) =>
      argRef match {
        case Some(ref) => curEnv.putLocal(ref, argV)
        case None      => curEnv
      }
    }
    // A named equation, after the fields: the scrutinee is the case's constructor applied to them, so reflexivity.
    val newEnv = branch.equation.fold(fieldsEnv)(ref => fieldsEnv.putLocal(ref, MatchEquation.proof(env, scrut)))
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

  /** S2: a global of linear type would be copied by every reference, and nothing would consume it. */
  private def rejectLinearGlobal(subject: LinearGlobal.Subject, tpe: Value, span: Span): Unit =
    if (Linearity.isLinear(tpe)) throw LinearGlobal(subject, Some(span))

  def evalDecl(decl: Decl, env: Env): Env = {
    decl match {
      case Decl.ConstDecl(name, ty, body, span, isInstance, lazyGlobal) =>
        body match {
          // Only kernel and prelude sources declare builtins (`run`), and their declared types are trusted. None is a
          // global of linear type (S2): the kernel's are not, and every entry the kernel leaves to a prelude is a
          // `Native`, which only a function type instantiates.
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
                // Decided from the declared type, before the body is checked.
                rejectLinearGlobal(LinearGlobal.Definition(name), checked.value, TypeChecker.sourceSpan(ty))
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
        // S3, which also covers S2 for axioms.
        if (Linearity.axiomMentionsLinear(tyV)) throw LinearAxiom(name, Some(TypeChecker.sourceSpan(ty)))
        val checkValue = VConst(name, Symbol, tyV)
        putGlobal(env, name, checkValue, isInstance)

      case d: Decl.InductiveDecl => InductiveChecks.evalInductiveBlock(Vector(d), env)

      case Decl.MutualInductives(families, _) => InductiveChecks.evalInductiveBlock(families, env)

      // Every member is a function, so none is linear (S2). The block is published as lazy globals, each the checked
      // lambda closed over the published environment, so that a running member finds its peers by name there.
      case Decl.MutualDefs(members, _) =>
        val checked = TypeChecker.checkMutualDefs(members, env)
        lazy val values: Map[String, Value] =
          members.zip(checked).map { case (member, (lam, vpi)) => member.name -> evalLam(lam, vpi, published) }.toMap
        lazy val published: Env =
          members.foldLeft(env)((cur, member) => cur.putLazyGlobal(member.name, () => values(member.name)))
        published

    }

  }

  /**
   * Runs a program over its prelude. Before any declaration is evaluated, a `:= builtin` declared by the program itself
   * is `ProgramBuiltin` at its `builtin`: `Builtins.instantiate` trusts a builtin's declared type, so only the kernel
   * and the prelude declare builtins. With `allowUserAxioms` false, an axiom declared by the program itself is then
   * `UserAxiom` at its span; the prelude's axioms are the trusted bootstrap and are unaffected.
   *
   * A body of type `(sup: Protocol.Supply) -> R` is an entry: once it has checked, and `R` is unrestricted (S2), its
   * value is applied to the root supply, once, and the result is the program's. Only the entry module has a body and no
   * global is linear, so a run has exactly one root supply, and checking, which precedes it, never allocates. A body of
   * any other type is the program's result, which must be unrestricted.
   */
  def run(p: Program, prelude: Prelude.Config = Prelude.default, allowUserAxioms: Boolean = true): Option[Value] = {
    p.decls.foreach {
      case Decl.ConstDecl(name, _, CoreAst.ConstBody.Builtin(builtin), _, _, _) =>
        throw ProgramBuiltin(name, Some(builtin))
      case _ =>
    }
    if (!allowUserAxioms) axioms(p).headOption.foreach(axiom => throw UserAxiom(axiom.name, Some(axiom.span)))
    val env =
      p.decls.foldLeft(initialEnv(prelude)) { case (curWorlds, decl) => evalDecl(decl, curWorlds) }
    p.body.map { b =>
      val value = TypeChecker.checkTerm(b, env).value
      val span = TypeChecker.sourceSpan(b)
      entryResult(value.tpe) match {
        case Some(result) =>
          rejectLinearGlobal(LinearGlobal.EntryResult, result, span)
          evalApply(value, Vector(ProtocolPrimitives.rootSupply))
        case None =>
          rejectLinearGlobal(LinearGlobal.ProgramResult, value.tpe, span)
          value
      }
    }
  }

  /**
   * The result type `R` when `tpe` is an entry's, `(sup: Protocol.Supply) -> R`. `R` mentions no linear binder (S1), so
   * it is read under a fresh one. The binder is plain: an instance binder of linear type failed to check (L7), and a
   * binder with captures freshens to a type that is a variable, never `Supply`.
   */
  private def entryResult(tpe: Value): Option[Value] =
    tpe match {
      case pi: VPi if pi.binders.length == 1 =>
        val fresh = BinderOps.freshen(pi)
        Option.when(ValueEquivalence.defEq(fresh(pi.binders.head.localRef).tpe, Kernel.supplyType))(pi.codomain(fresh))
      case _ => None
    }

  /**
   * The axioms `p` declares, in declaration order. For a program, these are its user axioms, the unchecked assumptions
   * outside the trusted bootstrap: the loader merges every loaded module into the program, while the prelude's
   * declarations live in `Prelude.Config.core`, and a program declares no builtin (`run`). For a prelude's `core`, they
   * are the prelude's trusted axioms.
   */
  def axioms(p: Program): Vector[Decl.AxiomDecl] =
    p.decls.collect { case axiom: Decl.AxiomDecl => axiom }

  /** Values the elaborator also knows by name; the kernel's declarations are evaluated on top of these. */
  private[raccoonlang] def primitiveEnv: Env =
    Env.empty
      .putGlobal("Type", TypeTpe)
      .putGlobal("Level", LevelTpe)
      .putGlobal("Level.zero", Level.zero)
      .putGlobal("Level.one", Level.one)
      .putGlobal("Kind", KindTpe)
      .putGlobal("Kind.copy", Kind.copy)
      .putGlobal("Kind.lin", Kind.lin)
      .putGlobal("Prop", PropTpe)

  private[raccoonlang] def initialEnv(prelude: Prelude.Config = Prelude.default): Env =
    prelude.core.decls.foldLeft(Kernel.env) { case (curEnv, decl) =>
      evalDecl(decl, curEnv)
    }
}
