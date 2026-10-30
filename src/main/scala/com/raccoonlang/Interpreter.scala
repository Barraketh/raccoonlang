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

  /** The codomain of `pi` at `args`, which fit its binders: the type of an application of a value of type `pi`. */
  private[raccoonlang] def applicationType(pi: VPi, args: Vector[Value]): Value =
    pi.codomain(getEnvWithArgs(pi, pi.env, args))

  /**
   * How many demanded proof calls are running (docs/kernel.md, "Proof calls"). Inside one, a proof call runs at once,
   * as every call did before suspension, so a demanded proof costs what eager evaluation cost and builds no
   * suspensions. The evaluator is single-threaded, as `FreshVar` and packed storage are; `forceCall` restores the count
   * however a run ends.
   */
  private var forcing = 0

  /** The weak head normal form of `value` when it is a proof call (`VProofCall`), computed once; any other value. */
  def force(value: Value): Value =
    value match {
      case call: VProofCall => forceCall(call)
      case other            => other
    }

  /**
   * A proof call's forced value: its lambda run on its arguments. The body may return another proof call, one of its
   * arguments or one its closure holds, which was made outside this run; forcing follows that chain in a loop, and
   * every call on it memoizes the chain's end. A run that fails memoizes nothing, so a later demand fails alike.
   */
  private def forceCall(call: VProofCall): Value = {
    if (call.forced ne null) return call.forced
    var chain = List(call)
    var result: Value = null
    while (result eq null) {
      forcing += 1
      val next =
        try runLam(chain.head.fn, chain.head.args)
        finally forcing -= 1
      next match {
        case pending: VProofCall if pending.forced eq null => chain = pending :: chain
        case done: VProofCall                              => result = done.forced
        case value                                         => result = value
      }
    }
    chain.foreach(_.forced = result)
    result
  }

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
    case ETerm.App(fn, args, _) => evalSteps(applyTermStep(fn, args, env))
    case proj: ETerm.Proj       => StructEta.project(evalTerm(proj.base, env), proj.index)
    case lit: ETerm.NatLit      => lit.value
    case lit: ETerm.StrLit      => lit.value
    case word: ETerm.Word       => evalWord(word, env)
    case pi: ETerm.Pi           => evalPi(pi, env)
    case l: ETerm.Lam           => evalLam(l, env)
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

  /**
   * `fn` applied to `vArgs`, which fit its binders. Applying a proof demands it. A lambda binds its arguments itself
   * (`lamStep`), or reads them as a native, so only their count is checked here; any other head's application has the
   * head's codomain at them as its type. A checked lambda whose function type is a proposition is not run, outside a
   * demanded proof: the application is a proof call (`VProofCall`).
   */
  def evalApply(fn: Value, vArgs: Vector[Value]): Value = evalSteps(applyStep(fn, vArgs))

  /** `evalApply` 's step: a lambda that runs continues with its body, its tail. */
  private def applyStep(fn: Value, vArgs: Vector[Value]): AnyRef = {
    require(vArgs.nonEmpty, "evalApply requires at least one argument")

    force(fn) match {
      case lam: VLam =>
        val pi = lam.tpe
        if (pi.binders.length != vArgs.length) throw ArityMismatch(pi.binders.length, vArgs.length)
        lam.body match {
          case _: LamBody.Core if pi.tpe == PropTpe && forcing == 0 => new VProofCall(lam, vArgs)
          case _                                                    => lamStep(lam, vArgs)
        }
      case head =>
        head.tpe match {
          case pi: VPi =>
            def resultTy: Value = applicationType(pi, vArgs)
            head match {
              case h: VConst                               => VApp(h, vArgs, resultTy)
              case h: ConstructorHead                      => ConstructorValue(h, vArgs.drop(h.numErased), resultTy)
              case blocker @ ReductionBlockers(blockerIds) => VBlockedApp(blocker, vArgs, resultTy, blockerIds)
              // A neutral function with nothing to wait on, such as a field projection of an axiom or a stuck
              // application of one, applies to a neutral application (KERNEL_FOLLOWUPS 1.3).
              case neutral @ (_: NeutralThunk | _: VApp) => VApp(neutral, vArgs, resultTy)
              case _                                     => throw CannotApplyNonFunction(head)
            }
          case _ => throw CannotApplyNonFunction(head.tpe)
        }
    }
  }

  /**
   * An application's head and arguments are evaluated first, since evaluation is strict; a callee's body is its tail.
   */
  private def applyTermStep(fn: ElabAst.Term, args: Vector[ElabAst.Term], env: Env): AnyRef = {
    val vf = evalTerm(fn, env)
    val vArgs = args.map(a => evalTerm(a, env))
    if (vArgs.isEmpty) throw CannotApplyNonFunction(vf.tpe)
    applyStep(vf, vArgs)
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

  def runLam(lam: VLam, args: Vector[Value]): Value = evalSteps(lamStep(lam, args))

  /** A native's result, or a core lambda's body, its tail, in the env binding its arguments. */
  private def lamStep(lam: VLam, args: Vector[Value]): AnyRef = {
    lam.body match {
      case LamBody.Native(run, nativeEnv, _) => run(args, nativeEnv)
      // A recursive definition's self slot holds the lambda itself; a member of a mutual block reads its block's
      // members from the globals its environment was closed over, where the block is published.
      case LamBody.Core(term, coreEnv) =>
        new Tail(
          term.body,
          coreBodyEnv(
            lam.tpe,
            term,
            coreEnv,
            args,
            index => if (term.recursiveSelf.isDefined) lam else coreEnv(term.recursivePeers(index)._2)
          )
        )
    }
  }

  /**
   * The body of `lam`, a recursive definition or a member of a mutual block, on `args`, with its recursive slots bound
   * to `recursive` instead: one value for its self slot, or one for each member of its block, in the block's order.
   * Conversion opens two such definitions on shared fresh values for both (`ValueEquivalence`), so that it compares
   * their bodies, not their unfoldings.
   */
  def runLamOnRecursive(lam: VLam, args: Vector[Value], recursive: Vector[Value]): Value =
    lam.body match {
      case LamBody.Core(term, coreEnv) => evalTerm(term.body, coreBodyEnv(lam.tpe, term, coreEnv, args, recursive))
      case native                      => throw WTF(s"A native function has no recursive slots: $native")
    }

  /**
   * The env in which `term` 's body runs over `coreEnv` on `args`: its parameters bound to `args`, and its recursive
   * slots bound in order to `recursive(0)`, `recursive(1)`, …
   */
  private def coreBodyEnv(tpe: VPi, term: ETerm.Lam, coreEnv: Env, args: Vector[Value], recursive: Int => Value): Env = {
    val bodyEnv = getEnvWithArgs(tpe, coreEnv, args)
    val selfEnv = term.recursiveSelf.fold(bodyEnv)(ref => bodyEnv.putLocal(ref, recursive(0)))
    term.recursivePeers.iterator.zipWithIndex.foldLeft(selfEnv) { case (env, ((ref, _), index)) =>
      env.putLocal(ref, recursive(index))
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

  /**
   * A term in tail position, whose value is the value of the term being evaluated, with the env it is evaluated in
   * (docs/kernel.md, "Evaluation depth"). A step returns one instead of recursing into it, and `evalSteps` evaluates it
   * in a loop, so a tail position costs no host stack.
   */
  private final class Tail(val term: ElabAst.Term, val env: Env)

  def evalTerm(term: ElabAst.Term, env: Env): Value = evalSteps(stepAt(term, env))

  /**
   * Takes steps, from `first`, a value or a `Tail`, until one is a value. Each tail's step is located at it, as the
   * recursion it replaces was: the innermost evaluated term that carries a span gives an error its place.
   */
  private def evalSteps(first: AnyRef): Value = {
    var next = first
    while (next.isInstanceOf[Tail]) {
      val tail = next.asInstanceOf[Tail]
      next = stepAt(tail.term, tail.env)
    }
    next.asInstanceOf[Value]
  }

  /**
   * One step of `term` in `env`: its value, or its tail. The tails are a block's result after its lets, a match's
   * chosen branch, and a core lambda's body where it is applied, after the arguments.
   */
  private def stepAt(term: ElabAst.Term, env: Env): AnyRef =
    TypeChecker.at(term.span) {
      term match {
        case ETerm.App(fn, args, _) => applyTermStep(fn, args, env)
        case tt: ElabAst.TypeTerm   => evalTypeTerm(tt, env)
        case m: ETerm.Match         => matchStep(m, env)
        case b: ETerm.Body          => bodyStep(b, env)
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

  /**
   * `m` stuck on `scrut` in `env`, a value of `outType`; `scrut` is no proof call, since every caller forces it first.
   * Its identity is its code and its free locals' values (`MatchIdentity`), and its closed environment keeps exactly
   * those locals, so resuming it reads nothing its identity leaves out.
   */
  private[raccoonlang] def stuckMatch(
      m: ETerm.Match,
      scrut: Value,
      env: Env,
      outType: Value
  ): Value = {
    val layout = MatchIdentity.layout(m, env.locals.length)
    val closedEnv = RuntimeEnv.closeForEval(env, layout.capturedIndexes)
    NeutralThunk(m, closedEnv, MatchId(layout.code, layout.captures(env)), outType, ReductionBlockers.of(scrut))
  }

  private def evalMatch(m: ETerm.Match, env: Env): Value = evalSteps(matchStep(m, env))

  /** The match `m` in `env`: its scrutinee, then `matchOnStep`, stuck at its motive or else at the scrutinee's type. */
  private def matchStep(m: ETerm.Match, env: Env): AnyRef = {
    val scrut = evalTerm(m.scrut, env)
    matchOnStep(m, scrut, env, m.motive.fold(scrut.tpe)(evalTypeTerm(_, env)))
  }

  /**
   * The match `m` on the value `scrut0`, its scrutinee in `env`, which a match demands. A constructor selects its
   * branch. A value at a structure eta type takes the one branch with its eta view, its field projections
   * (`StructEta`). Any other value is stuck, a value of `outType`.
   */
  private[raccoonlang] def evalMatchOn(m: ETerm.Match, scrut0: Value, env: Env, outType: => Value): Value =
    evalSteps(matchOnStep(m, scrut0, env, outType))

  /** `evalMatchOn` 's step: the chosen branch's body is its tail. */
  private def matchOnStep(m: ETerm.Match, scrut0: Value, env: Env, outType: => Value): AnyRef = {
    val scrut = force(scrut0)
    val (ctorName, args) = scrut match {
      case ConstructorValue(head, fields) => (head.name, fields)
      case _ =>
        (if (m.cases.length == 1) StructEta.fields(scrut) else None) match {
          case Some(fields) => (m.cases.head.ctorName, fields)
          case None         => return stuckMatch(m, scrut, env, outType)
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
    new Tail(branch.body, newEnv)
  }

  /** A block's lets, in order; its result is its tail. */
  private def bodyStep(body: ETerm.Body, env: Env): AnyRef = {
    val newEnv = body.lets.foldLeft(env) { case (curEnv, l) =>
      val res = evalTerm(l.value, curEnv)
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.localRef.name, res)) else None
      curEnv.putLocal(l.localRef, res, instanceKey)
    }
    new Tail(body.res, newEnv)
  }

  private def putGlobal(env: Env, name: String, value: Value, isInstance: Boolean): Env =
    env.putGlobal(name, value, if (isInstance) Some(InstanceSearch.instanceKey(name, value)) else None)

  /** S2: a global of linear type would be copied by every reference, and nothing would consume it. */
  private def rejectLinearGlobal(subject: LinearGlobal.Subject, tpe: Value, span: Span): Unit =
    if (Linearity.isLinear(tpe)) throw LinearGlobal(subject, Some(span))

  /**
   * The environment with `decl` checked and added. An error the declaration's checks raise without a location, such as
   * a redeclared global, is located at the declaration. This is where a host stack overflow while checking it becomes
   * `EvaluationTooDeep`, located at the whole declaration (docs/kernel.md, "Evaluation depth"): no boundary inside a
   * declaration catches one.
   */
  def evalDecl(decl: Decl, env: Env): Env = TypeChecker.at(decl.span) {
    try checkDecl(decl, env)
    catch { case _: StackOverflowError => throw EvaluationTooDeep() }
  }

  private def checkDecl(decl: Decl, env: Env): Env =
    decl match {
      case Decl.ConstDecl(name, ty, body, span, isInstance) =>
        body match {
          // Only kernel and prelude sources declare builtins (`run`), and their declared types are trusted. None is a
          // global of linear type (S2): the kernel's are not, and every entry the kernel leaves to a prelude is a
          // `Native`, which only a function type instantiates.
          case CoreAst.ConstBody.Builtin(_) =>
            if (isInstance) throw WTF("Builtin declarations cannot be instances", Some(span))
            putGlobal(env, name, Builtins.instantiate(name, TypeChecker.getType(ty, env), span), isInstance)

          case CoreAst.ConstBody.TermBody(term) =>
            val checkedTy =
              TypeChecker.at(ty.span) {
                val checked = TypeChecker.checkTypeTerm(ty, env)
                TypeChecker.assertType(checked.value)
                // Decided from the declared type, before the body is checked.
                rejectLinearGlobal(LinearGlobal.Definition(name), checked.value, TypeChecker.sourceSpan(ty))
                checked
              }
            putGlobal(env, name, TypeChecker.checkTermAgainst(term, env, checkedTy).value, isInstance)
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

  /**
   * Runs a program over its prelude. Before any declaration is evaluated, a `:= builtin` declared by the program itself
   * is `ProgramBuiltin` at its `builtin`: `Builtins.instantiate` trusts a builtin's declared type, so only the kernel
   * and the prelude declare builtins. With `allowUserAxioms` false, an axiom declared by the program itself is then
   * `UserAxiom` at its span; the prelude's axioms are the trusted bootstrap and are unaffected.
   *
   * A body of type `(sup: Protocol.Supply) -> R` is an entry: once it has checked, and `R` is unrestricted (S2), its
   * value is applied to the root supply, once, and the result is the program's. Only the entry module has a body and no
   * global is linear, so a run has exactly one root supply, and checking, which precedes it, never allocates. A body of
   * any other type is the program's result, which must be unrestricted. The result is shown, so a proof call is forced
   * (docs/kernel.md, "Proof calls"); `PrettyPrinter` forces the ones inside it.
   */
  def run(p: Program, prelude: Prelude.Config = Prelude.default, allowUserAxioms: Boolean = true): Option[Value] = {
    p.decls.foreach {
      case Decl.ConstDecl(name, _, CoreAst.ConstBody.Builtin(builtin), _, _) =>
        throw ProgramBuiltin(name, Some(builtin))
      case _ =>
    }
    if (!allowUserAxioms) axioms(p).headOption.foreach(axiom => throw UserAxiom(axiom.name, Some(axiom.span)))
    val env =
      p.decls.foldLeft(initialEnv(prelude)) { case (curWorlds, decl) => evalDecl(decl, curWorlds) }
    p.body.map { b =>
      val span = TypeChecker.sourceSpan(b)
      // The program's boundary, as `evalDecl` is a declaration's: an overflow while checking or evaluating the body is
      // `EvaluationTooDeep` at the whole body.
      try {
        val value = TypeChecker.checkTerm(b, env).value
        entryResult(value.tpe) match {
          case Some(result) =>
            rejectLinearGlobal(LinearGlobal.EntryResult, result, span)
            force(evalApply(value, Vector(ProtocolPrimitives.rootSupply)))
          case None =>
            rejectLinearGlobal(LinearGlobal.ProgramResult, value.tpe, span)
            force(value)
        }
      } catch { case _: StackOverflowError => throw EvaluationTooDeep(Some(span)) }
    }
  }

  /**
   * The program's result as the CLI prints it. Printing forces the proof calls inside it (docs/kernel.md, "Proof
   * calls"), which is evaluation of the body, so an overflow there is `EvaluationTooDeep` at the body, `body`.
   */
  def show(result: Value, body: Span): String =
    try PrettyPrinter.print(result)
    catch { case _: StackOverflowError => throw EvaluationTooDeep(Some(body)) }

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
