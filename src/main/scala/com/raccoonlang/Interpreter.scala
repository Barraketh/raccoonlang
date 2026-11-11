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

  /** `resolveInEqStore` in a materialization session of its own. */
  def resolveInEqStore(v: Value, eqStore: EqStore): Value = {
    val materializer = new ValueOps.Materializer(eqStore, DepSet.empty)
    materializer.session(resolveInEqStore(v, materializer))
  }

  /**
   * Force links and resume blocked computations when a scheduling dependency has been solved. Materialization handles
   * transitive substitution of heads and arguments, in the session of `materializer`, whose store is `eqStore`. Stop
   * retrying when reduction returns the same blockers, even if a solved dependency remains syntactically present in an
   * opaque result.
   */
  private[raccoonlang] def resolveInEqStore(v: Value, materializer: ValueOps.Materializer): Value = {
    val eqStore = materializer.eqStore
    def retryUnlessStuckOn(next: Value, previousBlockers: DepSet): Value =
      next match {
        case Blocked(nextBlockers) if nextBlockers == previousBlockers => next
        case _                                                         => resolveInEqStore(next, materializer)
      }

    val v0 = eqStore.force(v)
    v0 match {
      case Blocked(blockerIds) if blockerIds.intersects(eqStore.solvedIds) =>
        v0 match {
          case VBlockedApp(h, args, tpe, oldBlockers) =>
            val h0 = materializer.materialize(h)
            val materializedArgs = args.map(materializer.materialize)
            h0 match {
              case lam: VLam => retryUnlessStuckOn(runLam(lam, materializedArgs), oldBlockers)
              case nextHead @ ReductionBlockers(nextBlockers) =>
                val next = VBlockedApp(nextHead, materializedArgs, materializer.materialize(tpe), nextBlockers)
                retryUnlessStuckOn(next, oldBlockers)
              case other =>
                resolveInEqStore(evalApply(other, materializedArgs), materializer)
            }
          case vm: NeutralThunk if vm.blockerIds.nonEmpty =>
            retryUnlessStuckOn(forceThunk(vm, materializer), vm.blockerIds)
          case _ => throw WTF(s"Blocked extractor matched unexpected value ${Mismatch.abbreviated(v0)}")
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
   * How many demanded suspended proofs are running (docs/kernel.md, "Proof calls"). Inside one, a proof call runs at
   * once, as every call did before suspension, so a demanded proof costs what eager evaluation cost. A match into a
   * proposition on a suspended proof, or an application of one, made inside it still suspends: the suspension came from
   * outside the run, and whether a value is suspended depends only on how it was computed. The evaluator is
   * single-threaded, as `FreshVar` and packed storage are; `forceSuspended` restores the count however a run ends.
   */
  private var forcing = 0

  /**
   * The weak head normal form of `value` when it is a suspended proof (`VSuspendedProof`), computed once; any other.
   */
  def force(value: Value): Value =
    value match {
      case proof: VSuspendedProof => forceSuspended(proof)
      case other                  => other
    }

  /**
   * A suspended proof's forced value: its computation run (`runSuspended`). The run may return another suspension, one
   * made outside it, such as an argument or one its closure holds; forcing follows that chain in a loop, and every
   * suspension on it memoizes the chain's end. A run that fails memoizes nothing, so a later demand fails alike.
   */
  private def forceSuspended(proof: VSuspendedProof): Value = {
    if (proof.forced ne null) return proof.forced
    var chain = List(proof)
    var result: Value = null
    while (result eq null) {
      forcing += 1
      val next =
        try runSuspended(chain.head)
        finally forcing -= 1
      next match {
        case pending: VSuspendedProof if pending.forced eq null => chain = pending :: chain
        case done: VSuspendedProof                              => result = done.forced
        case value                                              => result = value
      }
    }
    chain.foreach(_.forced = result)
    result
  }

  /**
   * One run of a suspended proof's computation, inside a demanded proof. A proof match forces its scrutinee and a proof
   * application its head, on the host stack, as eager evaluation evaluated them before the match or application; the
   * forced value is no suspension, so the match selects its branch, or is stuck, and the application runs.
   */
  private def runSuspended(proof: VSuspendedProof): Value =
    proof match {
      case call: VProofCall => runLam(call.fn, call.args)
      case m: VProofMatch   => evalSteps(matchOnStep(m.term, force(m.scrut), m.env, m.tpe))
      case app: VProofApply => evalSteps(applyStep(force(app.fn), app.args))
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
    // Identified by its code and the values it reads, in the order its code first reads them (`MatchIdentity`).
    val layout = MatchIdentity.layout(pi, env.locals.length)
    val id = ValueId.LocalId(layout.code, layout.captures(env))
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
   * `fn` applied to `vArgs`, which fit its binders. Applying a suspended proof does not demand it: the application is a
   * proof application (`VProofApply`), at the codomain of its proposition. A lambda binds its arguments itself
   * (`lamStep`), or reads them as a native, so only their count is checked here; any other head's application has the
   * head's codomain at them as its type. A checked lambda whose function type is a proposition is not run, outside a
   * demanded proof: the application is a proof call (`VProofCall`).
   */
  def evalApply(fn: Value, vArgs: Vector[Value]): Value = evalSteps(applyStep(fn, vArgs))

  /** `evalApply` 's step: a lambda that runs continues with its body, its tail. */
  private def applyStep(fn: Value, vArgs: Vector[Value]): AnyRef = {
    require(vArgs.nonEmpty, "evalApply requires at least one argument")

    fn match {
      case proof: VSuspendedProof => new VProofApply(proof, vArgs)
      case lam: VLam =>
        val pi = lam.tpe
        if (pi.binders.length != vArgs.length) throw ArityMismatch(pi.binders.length, vArgs.length)
        lam.body match {
          case _: LamBody.Core if pi.tpe == PropTpe && forcing == 0        => new VProofCall(lam, vArgs)
          case core: LamBody.Core if lam.id.isInstanceOf[ValueId.LocalId] => appliedStep(lam, core, vArgs)
          case _                                                           => lamStep(lam, vArgs)
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
      // Identified by its code and the values it reads, as a function type is (`evalPi`).
      case None =>
        val layout = MatchIdentity.layout(l, env.locals.length)
        ValueId.LocalId(layout.code, layout.captures(env))

    }
    VLam(vpi, id, LamBody.Core(l, RuntimeEnv.closeForEval(env, capturedIndexes)))
  }

  def runLam(lam: VLam, args: Vector[Value]): Value = evalSteps(lamStep(lam, args))

  /** A native's result, or a core lambda's body, its tail, in the env binding its arguments. */
  private def lamStep(lam: VLam, args: Vector[Value]): AnyRef = {
    lam.body match {
      case LamBody.Native(run, nativeEnv, _) => run(args, nativeEnv)
      case core: LamBody.Core                => new Tail(core.term.body, bodyEnv(lam, core, args))
    }
  }

  /**
   * The env in which `core`, the body of `lam`, runs on `args`. A recursive definition's self slot holds the lambda
   * itself; a member of a mutual block reads its block's members from the globals its environment was closed over,
   * where the block is published.
   */
  private def bodyEnv(lam: VLam, core: LamBody.Core, args: Vector[Value]): Env = {
    val term = core.term
    coreBodyEnv(
      lam.tpe,
      term,
      core.env,
      args,
      index => if (term.recursiveSelf.isDefined) lam else core.env(term.recursivePeers(index)._2)
    )
  }

  /**
   * At most this many applications of one closure are recorded (`AppliedTail`); past it, new arguments run without being
   * recorded, and the recorded ones still answer. A closure's memo then holds a bounded number of values for as long as
   * the closure lives, which matters for one held by a global.
   */
  private[raccoonlang] val MemoCap = 4096

  /**
   * A test hook: when set, a memoized application that finds a recorded value also runs the body again and passes the
   * closure, the arguments, the recorded value and the new one to it, which may compare them. Unset, a hit reads it once.
   */
  private[raccoonlang] var hitCheck: (VLam, Vector[Value], Value, Value) => Unit = null

  /**
   * `lamStep` for a memoized application of `lam`, whose body is `core`, to `args`, which fit its binders: the value an
   * earlier application with the same key returned (`ValueKey.applicationKey`), or else the body, its tail, which
   * `evalSteps` records under the key once the tail has its value. The key holds whether a demanded proof is running,
   * since a run inside one leaves no proof call suspended.
   *
   * Evaluation reads no store and makes no fresh variable, so the body evaluates to one value on the same arguments.
   * Equal keys say a little less: keys ignore some parts, such as a variable's type, which a type pattern's capture
   * reads. Arguments that hold no suspended proof, the only ones keyed, differ there only where a store's solution was
   * substituted into one and not the other, which needs a variable some store has linked (`EqStore.mentionsLinked`).
   * So an application whose arguments mention one is not memoized, and a recorded value that mentions one is not
   * returned: a run on such arguments would have kept the variable. Identities also ignore the parts of a captured
   * record that the code does not read (`MatchIdentity`), which a stuck match's or a closure's environment keeps in a
   * result; a recorded value is returned only when its dependencies are among those of `lam` and `args`, as a run's
   * are, so that no variable reaches a context through a part no run there would have read. A run that fails records
   * nothing.
   */
  private def appliedStep(lam: VLam, core: LamBody.Core, args: Vector[Value]): AnyRef = {
    val key =
      if (args.exists(arg => EqStore.mentionsLinked(arg.synDeps))) null
      else ValueKey.applicationKey(args, forcing > 0)
    if (key eq null) return new Tail(core.term.body, bodyEnv(lam, core, args))
    val memo = lam.applied
    if (memo ne null) {
      val known = memo.get(key)
      if ((known ne null) && !EqStore.mentionsLinked(known.synDeps) && depsWithin(known.synDeps, lam, args)) {
        if (hitCheck ne null) hitCheck(lam, args, known, evalSteps(new Tail(core.term.body, bodyEnv(lam, core, args))))
        return known
      }
    }
    new AppliedTail(core.term.body, bodyEnv(lam, core, args), lam, key)
  }

  /** Whether every variable in `deps` is a dependency of `lam` or of one of `args`. */
  private def depsWithin(deps: DepSet, lam: VLam, args: Vector[Value]): Boolean = {
    var within = true
    deps.foreach(id => if (within && !lam.synDeps.contains(id) && !args.exists(_.synDeps.contains(id))) within = false)
    within
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

  /**
   * `thunk` resumed in `materializer` 's session: its match on its scrutinee's value, materialized, which resolves it
   * where it was blocked, in its environment materialized, which holds its captures, at its type materialized. It reads
   * only what the thunk's identity holds, never the scrutinee term, whose locals the environment does not keep.
   * Evaluation commutes with substitution, so this is the match evaluated in its materialized environment.
   */
  private def forceThunk(thunk: NeutralThunk, materializer: ValueOps.Materializer): Value =
    evalMatchOn(
      thunk.term,
      materializer.materialize(thunk.id.scrut),
      materializer.materializeEnv(thunk.env),
      materializer.materialize(thunk.tpe)
    )

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
  private class Tail(val term: ElabAst.Term, val env: Env)

  /**
   * The tail that is the body of a memoized application of `lam` (`appliedStep`), whose value is recorded in `lam`
   * under `key` once it has one.
   */
  private final class AppliedTail(term: ElabAst.Term, env: Env, lam: VLam, key: ValueKey.Key) extends Tail(term, env) {
    def record(value: Value): Unit = {
      if (lam.applied eq null) lam.applied = new java.util.HashMap[ValueKey.Key, Value]()
      if (lam.applied.size < MemoCap || lam.applied.containsKey(key)) lam.applied.put(key, value)
    }
  }

  def evalTerm(term: ElabAst.Term, env: Env): Value = evalSteps(stepAt(term, env))

  /**
   * Takes steps, from `first`, a value or a `Tail`, until one is a value. Each tail's step is located at it, as the
   * recursion it replaces was: the innermost evaluated term that carries a span gives an error its place. Every tail's
   * value is the last step's, so each memoized application among them (`AppliedTail`) records it then; a chain of them
   * costs heap, not host stack. Steps that throw record nothing.
   */
  private def evalSteps(first: AnyRef): Value = {
    var next = first
    var applied: List[AppliedTail] = Nil
    while (next.isInstanceOf[Tail]) {
      val tail = next.asInstanceOf[Tail]
      if (tail.isInstanceOf[AppliedTail]) applied = tail.asInstanceOf[AppliedTail] :: applied
      next = stepAt(tail.term, tail.env)
    }
    val value = next.asInstanceOf[Value]
    applied.foreach(_.record(value))
    value
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
      case other =>
        throw WTF(
          s"Word head ${word.consHead.name} is not a constructor: ${Mismatch.abbreviated(other)}",
          Some(word.span)
        )
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
   * `m` stuck on `scrut`, the value of its scrutinee in `env`, a value of `outType`; `scrut` is no suspended proof: no
   * caller passes one. `env` holds every local the rest of `m` reads. Its identity is its code with its scrutinee a
   * hole, `scrut`, and the values of the free locals the rest mentions (`MatchIdentity`), and its closed environment
   * keeps exactly those locals, so resuming it on `scrut` (`forceThunk`) reads nothing its identity leaves out.
   */
  private[raccoonlang] def stuckMatch(
      m: ETerm.Match,
      scrut: Value,
      env: Env,
      outType: Value
  ): Value = {
    val layout = MatchIdentity.layout(m, env.locals.length)
    val closedEnv = RuntimeEnv.closeForEval(env, layout.capturedIndexes)
    NeutralThunk(m, closedEnv, MatchId(layout.code, scrut, layout.captures(env)), outType, ReductionBlockers.of(scrut))
  }

  /** The match `m` in `env`: its scrutinee, then `matchOnStep`, stuck at its motive or else at the scrutinee's type. */
  private def matchStep(m: ETerm.Match, env: Env): AnyRef = {
    val scrut = evalTerm(m.scrut, env)
    matchOnStep(m, scrut, env, m.motive.fold(scrut.tpe)(evalTypeTerm(_, env)))
  }

  /**
   * The match `m` on the value `scrut0`, its scrutinee's, in `env`, which holds every local the rest of `m` reads; a
   * resumed stuck match's holds no other (`forceThunk`), so nothing here reads the scrutinee term. A match from a proof
   * into a proposition (`m.proofIntoProp`) on a suspended proof is a proof match (`VProofMatch`), which forces it only
   * when demanded; that it is suspended is decided by its form, not by whether it was forced. Any other match demands
   * its scrutinee. A constructor selects its branch. A value at a structure eta type takes the one branch with its eta
   * view, its field projections (`StructEta`). Any other value is stuck, a value of `outType`.
   */
  private[raccoonlang] def evalMatchOn(m: ETerm.Match, scrut0: Value, env: Env, outType: => Value): Value =
    evalSteps(matchOnStep(m, scrut0, env, outType))

  /** `evalMatchOn` 's step: the chosen branch's body is its tail. */
  private def matchOnStep(m: ETerm.Match, scrut0: Value, env: Env, outType: => Value): AnyRef = {
    scrut0 match {
      case proof: VSuspendedProof if m.proofIntoProp =>
        return new VProofMatch(m, proof, RuntimeEnv.closeForEval(env, CapturedIndexes.getCapturedIndexes(m, env)))
      case _ =>
    }
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
   * Runs a program that imports nothing over its prelude: its trust checks (`trustViolation`), then its declarations,
   * then its body (`runBody`).
   */
  def run(p: Program, prelude: Prelude.Config = Prelude.default, allowUserAxioms: Boolean = true): Option[Value] = {
    trustViolation(p.decls, allowUserAxioms).foreach(violation => throw violation)
    val env =
      p.decls.foldLeft(initialEnv(prelude)) { case (curWorlds, decl) => evalDecl(decl, curWorlds) }
    p.body.map(runBody(_, env))
  }

  /**
   * What a program's own declarations, `decls`, in order, may not do, before any of them is evaluated: declare a
   * `:= builtin`, which is `ProgramBuiltin` at its `builtin`, since `Builtins.instantiate` trusts a builtin's declared
   * type, so only the kernel and the prelude declare builtins; then, with `allowUserAxioms` false, declare an axiom,
   * which is `UserAxiom` at its span. The prelude's axioms are the trusted bootstrap and are unaffected. A program of
   * several modules gives its modules' declarations in its depth-first import order, its own last.
   */
  def trustViolation(decls: Iterable[Decl], allowUserAxioms: Boolean): Option[TypeError] =
    decls
      .collectFirst { case Decl.ConstDecl(name, _, CoreAst.ConstBody.Builtin(builtin), _, _) =>
        ProgramBuiltin(name, Some(builtin))
      }
      .orElse {
        if (allowUserAxioms) None
        else decls.collectFirst { case axiom: Decl.AxiomDecl => UserAxiom(axiom.name, Some(axiom.span)) }
      }

  /**
   * A program's body `b`, checked and run in `env`, the environment after its declarations.
   *
   * A body of type `(sup: Protocol.Supply) -> R` is an entry: once it has checked, and `R` is unrestricted (S2), its
   * value is applied to the root supply, once, and the result is the program's. Only the entry module has a body and no
   * global is linear, so a run has exactly one root supply, and checking, which precedes it, never allocates. A body of
   * any other type is the program's result, which must be unrestricted. The result is shown, so a proof call is forced
   * (docs/kernel.md, "Proof calls"); `PrettyPrinter` forces the ones inside it.
   */
  def runBody(b: CoreAst.Term, env: Env): Value = {
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

  /**
   * A module's declarations, `decls`, checked in order over `env`, the top-level environment of its import closure, as
   * `evalDecl` checks each: the environment they end in, and what they added to `env` (`ModuleEffect`), which an
   * importer replays (`TypecheckEnv.withEffect`) instead of checking them again.
   *
   * The globals a declaration adds are those `declaredGlobals` names: `evalDecl` binds each, and since binding a global
   * twice is `AlreadyDefined`, the environment grows by exactly as many globals as they are only when it adds no other.
   * Instances are only ever appended to their key's bucket, so a module's are each bucket's new tail.
   */
  def checkModule(decls: Vector[Decl], env: TypecheckEnv): (TypecheckEnv, ModuleEffect) = {
    val end = topLevel(decls.foldLeft(env: Env)((cur, decl) => evalDecl(decl, cur)))
    val names = decls.flatMap(declaredGlobals)
    if (end.globals.size != env.globals.size + names.length)
      throw WTF(s"A module's declarations added ${end.globals.size - env.globals.size} globals, not ${names.length}")
    val instances = end.globalInstances.buckets.flatMap { case (key, values) =>
      val before = env.globalInstances.get(key).length
      Option.when(values.length > before)(key -> values.drop(before))
    }
    (end, ModuleEffect(names.map(name => name -> end.globals(name)), instances))
  }

  /**
   * `env`, an environment between top-level declarations, as the `TypecheckEnv` it is: `Env.empty` is one, and
   * `evalDecl` adds globals to the environment it is given, which a `TypecheckEnv` adds to itself.
   */
  private[raccoonlang] def topLevel(env: Env): TypecheckEnv =
    env match {
      case top: TypecheckEnv => top
      case other             => throw WTF(s"A top-level environment is a ${other.getClass.getSimpleName}")
    }

  /** The globals `evalDecl` binds for `decl`: its name, or a block's, and an inductive family's constructors. */
  private def declaredGlobals(decl: Decl): Vector[String] =
    decl match {
      case Decl.ConstDecl(name, _, _, _, _)   => Vector(name)
      case Decl.AxiomDecl(name, _, _, _)      => Vector(name)
      case family: Decl.InductiveDecl         => family.header.name +: family.ctors.map(_.canonicalName)
      case Decl.MutualInductives(families, _) => families.flatMap(declaredGlobals)
      case Decl.MutualDefs(members, _)        => members.map(_.name)
    }

  /**
   * The program's result as the CLI prints it. Printing forces the proof calls inside it (docs/kernel.md, "Proof
   * calls"), which is evaluation of the body: an error a run raises is the program's, as it was when the body evaluated
   * them, and an overflow is `EvaluationTooDeep` at the body, `body`.
   */
  def show(result: Value, body: Span): String =
    try PrettyPrinter.printResult(result)
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
   * The axioms `decls` declare, in declaration order. For a program's own declarations, its modules' in its depth-first
   * import order, these are its user axioms, the unchecked assumptions outside the trusted bootstrap: the prelude's
   * declarations live in `Prelude.Config.core`, and a program declares no builtin (`trustViolation`). For a prelude's
   * `core`, they are the prelude's trusted axioms.
   */
  def axioms(decls: Iterable[Decl]): Vector[Decl.AxiomDecl] =
    decls.iterator.collect { case axiom: Decl.AxiomDecl => axiom }.toVector

  def axioms(p: Program): Vector[Decl.AxiomDecl] = axioms(p.decls)

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
