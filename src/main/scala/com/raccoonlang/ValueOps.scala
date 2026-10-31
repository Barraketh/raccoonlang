package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.packed.Words

object ValueOps {

  /** Transitively substitute solved dependencies and resume affected blocked computations before rebuilding values. */
  def materialize(value: Value, eqStore: EqStore): Value = {
    val materializer = new Materializer(eqStore, DepSet.empty)
    materializer.session(materializer.materialize(value))
  }

  def materializeEnv(env: Env, eqStore: EqStore): Env = new Materializer(eqStore, DepSet.empty).materializeEnv(env)

  /**
   * `value` materialized, with every suspended proof (`VSuspendedProof`) whose dependencies meet `ids` replaced by its
   * forced value, materialized in turn, so that the result's dependencies among `ids` are its forced dependencies
   * (`Value.forcedDeps`). A suspension's own dependencies over-approximate its forced value's; this is the value eager
   * evaluation held where a link must not mention a variable that only a suspension's parts mention (`EqStore`).
   */
  def forceProofCalls(value: Value, eqStore: EqStore, ids: DepSet): Value = {
    val materializer = new Materializer(eqStore, ids)
    materializer.session(materializer.materialize(value))
  }

  /**
   * One materialization: the solved variables of `eqStore`, and the suspended proofs `forcing` names
   * (`forceProofCalls`), which is empty for plain materialization, which keeps suspensions suspended. It is a function
   * of the value and the store, which are immutable, so within a session it materializes each value and environment, by
   * identity, once: a graph whose parts are shared, such as a tree whose two children are one value, is rebuilt in time
   * linear in its distinct parts, and keeps its sharing. A session is a root call, or the mapping of an environment
   * that one returned, which runs later; between sessions it keeps no table, so a value holding a materialized
   * environment does not retain the work that built it.
   */
  private[raccoonlang] final class Materializer(val eqStore: EqStore, forcing: DepSet) {
    private var depth = 0
    private var values: java.util.IdentityHashMap[Value, Value] = null
    private var envs: java.util.IdentityHashMap[Env, Env] = null

    /** `body`, whose materializations share their results, and those of any session it is inside. */
    def session[A](body: => A): A = {
      if (depth == 0) {
        values = new java.util.IdentityHashMap[Value, Value]()
        envs = new java.util.IdentityHashMap[Env, Env]()
      }
      depth += 1
      try body
      finally {
        depth -= 1
        if (depth == 0) {
          values = null
          envs = null
        }
      }
    }

    def materializeEnv(env: Env): Env =
      if (depth == 0) MappedEnv(env, this)
      else {
        val known = envs.get(env)
        if (known ne null) known
        else {
          val mapped = MappedEnv(env, this)
          envs.put(env, mapped)
          mapped
        }
      }

    def materialize(value: Value): Value = {
      if (!mayNeedMaterialization(value)) return value
      if (depth == 0) return session(materialize(value))
      val known = values.get(value)
      if (known ne null) return known

      val resolved = Interpreter.resolveInEqStore(value, this)
      val result = if (mayNeedMaterialization(resolved)) rebuild(resolved) else resolved
      values.put(value, result)
      if (resolved ne value) values.put(resolved, result)
      result
    }

    private def rebuild(resolved: Value): Value =
      resolved match {
        case LevelTpe | KindTpe | KernelObject | PropTpe => resolved
        case level: Level                                => materializeLevel(level)
        case kind: Kind                                  => materializeKind(kind)
        case VUniv(kind, level)                          => VUniv(materializeKind(kind), materializeLevel(level))
        case Var(name, id, tpe)                          => Var(name, id, materialize(tpe))
        case VConst(name, constType, tpe)                => VConst(name, constType, materialize(tpe))
        case poly: VNatPoly                              => NatNormalForm.substituteAtoms(poly, materialize(_))
        // In one loop, splicing in a solved terminator; every part of the result is materialized, so it is too.
        case word: VWord => Words.map(word, mayChange, materialize(_))
        case VApp(head, args, tpe, blockerIds) =>
          val nextHead = materialize(head)
          val nextArgs = args.map(materialize(_))
          val nextType = materialize(tpe)
          nextHead match {
            case ctor: ConstructorHead => ConstructorValue(ctor, nextArgs, nextType)
            case _                     => VApp(nextHead, nextArgs, nextType, materializeDeps(blockerIds))
          }
        case NeutralThunk(term, env, id, tpe, blockerIds) =>
          NeutralThunk(
            term,
            materializeEnv(env),
            MatchId(id.code, id.captures.map(materialize(_))),
            materialize(tpe),
            materializeDeps(blockerIds)
          )
        case ctor: ConstructorHead =>
          ctor.copy(tpe = materialize(ctor.tpe))
        case pi: VPi =>
          materializePi(pi)
        case VLam(tpe, id, body) =>
          VLam(materializePi(tpe), materializeId(id), materializeLamBody(body))
        // Still suspended, over its materialized parts (docs/kernel.md, "Proof calls"): running it then gives what
        // materializing its forced value gives, since evaluation commutes with substitution, as resolving a blocked
        // computation on materialized arguments already assumes. A forced suspension keeps its forced value,
        // materialized, which is what eager evaluation held. A suspension `forcing` names is its forced value.
        case proof: VSuspendedProof =>
          val next = proof match {
            case call: VProofCall =>
              val fn = materialize(call.fn) match {
                case lam: VLam => lam
                case other     => throw WTF(s"Proof call head ${call.fn} materialized to $other")
              }
              new VProofCall(fn, call.args.map(materialize(_)))
            case m: VProofMatch   => new VProofMatch(m.term, materialize(m.scrut), materializeEnv(m.env))
            case app: VProofApply => new VProofApply(materialize(app.fn), app.args.map(materialize(_)))
          }
          if (proof.forced ne null) next.forced = Interpreter.force(materialize(proof.forced))
          if (next.synDeps.intersects(forcing)) materialize(Interpreter.force(next)) else next
      }

    private def mayChange(deps: DepSet): Boolean = deps.intersects(eqStore.solvedIds) || deps.intersects(forcing)

    // An empty store is common (fresh unification and match checking); skip computing dependencies then.
    private def mayNeedMaterialization(value: Value): Boolean =
      (eqStore.subst.nonEmpty || forcing.nonEmpty) && mayChange(value.synDeps)

    private def materializeLevel(level: Level): Level =
      Interpreter.resolveInEqStore(level, this) match {
        case l: Level => l
        case other    => throw NotALevel(other)
      }

    private def materializeKind(kind: Kind): Kind =
      Interpreter.resolveInEqStore(kind, this) match {
        case k: Kind => k
        case other   => throw NotAKind(other)
      }

    private def materializeUniverse(value: Universe): Universe =
      materialize(value) match {
        case u: VUniv => u
        case PropTpe  => PropTpe
        case other    => throw NotAType(other)
      }

    /**
     * A function type's dependencies are its captures' (`Interpreter.evalPi`). Forcing proof calls among them drops
     * dependencies the materialized solutions do not account for, so they are then read off the materialized captures.
     */
    private def materializePi(pi: VPi): VPi = {
      val id = materializeId(pi.id)
      val synDeps =
        if (forcing.isEmpty) materializeDeps(pi.synDeps)
        else
          id match {
            case ValueId.LocalId(_, captures) => DepSet.unionAll(captures.map(_.synDeps))
            case ValueId.Const(_)             => materializeDeps(pi.synDeps)
          }
      pi.copy(env = materializeEnv(pi.env), synDeps = synDeps, id = id, tpe = materializeUniverse(pi.tpe))
    }

    private def materializeId(id: ValueId): ValueId =
      id match {
        case local: ValueId.LocalId => materializeLocalId(local)
        case other                  => other
      }

    private def materializeLocalId(id: ValueId.LocalId): ValueId.LocalId =
      ValueId.LocalId(id.nodeId, id.captures.map(materialize(_)))

    private def materializeLamBody(body: LamBody): LamBody =
      body match {
        case LamBody.Core(term, env) => LamBody.Core(term, materializeEnv(env))
        case LamBody.Native(run, env, isRawRecursive) =>
          LamBody.Native(run, materializeEnv(env), isRawRecursive)
      }

    private def materializeDeps(deps: DepSet): DepSet = {
      if (!deps.intersects(eqStore.solvedIds)) return deps
      val res = DepSet.newBuilder
      deps.foreach { id =>
        eqStore.subst.get(id) match {
          case Some(solution) => res.unionInPlace(materialize(solution).synDeps)
          case None           => res.add(id)
        }
      }
      res.result()
    }
  }

  /** `base` with its local values materialized, all of them in one session, when one is first read. */
  private final case class MappedEnv(base: Env, materializer: Materializer) extends DelegatingEnv {
    override def updateBase(newBase: Env): Env = copy(base = newBase)

    override lazy val locals: Vector[Binding] =
      materializer.session(base.locals.map(_.mapValue(materializer.materialize)))

    override def localBinding(ref: CoreAst.LocalRef): Binding =
      if (ref.id >= 0 && ref.id < locals.length) locals(ref.id)
      else throw NotFound(s"${ref.name}#${ref.id}")
  }
}
