package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.packed.Words

object ValueOps {

  /** Transitively substitute solved dependencies and resume affected blocked computations before rebuilding values. */
  def materialize(value: Value, eqStore: EqStore): Value = new Materializer(eqStore, DepSet.empty).materialize(value)

  def materializeEnv(env: Env, eqStore: EqStore): Env = new Materializer(eqStore, DepSet.empty).materializeEnv(env)

  /**
   * `value` materialized, with every proof call (`VProofCall`) whose dependencies meet `ids` replaced by its forced
   * value, materialized in turn, so that the result's dependencies among `ids` are its forced dependencies
   * (`Value.forcedDeps`). A proof call's own dependencies over-approximate its forced value's; this is the value eager
   * evaluation held where a link must not mention a variable that only a proof call's arguments mention (`EqStore`).
   */
  def forceProofCalls(value: Value, eqStore: EqStore, ids: DepSet): Value =
    new Materializer(eqStore, ids).materialize(value)

  /**
   * One materialization: the solved variables of `eqStore`, and the proof calls `forcing` names (`forceProofCalls`),
   * which is empty for plain materialization, which keeps proof calls suspended.
   */
  private final class Materializer(eqStore: EqStore, forcing: DepSet) {
    def materializeEnv(env: Env): Env = {
      MappedEnv(env, value => materialize(value))
    }

    def materialize(value: Value): Value = {
      if (!mayNeedMaterialization(value)) return value

      val resolved = Interpreter.resolveInEqStore(value, eqStore)
      if (!mayNeedMaterialization(resolved)) return resolved

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
        // Still suspended, over the materialized lambda and arguments (docs/kernel.md, "Proof calls"): running it
        // then gives what materializing its forced value gives, since evaluation commutes with substitution, as
        // resolving a blocked computation on materialized arguments already assumes. A forced call keeps its forced
        // value, materialized, which is what eager evaluation held. A call `forcing` names is its forced value.
        case call: VProofCall =>
          val fn = materialize(call.fn) match {
            case lam: VLam => lam
            case other     => throw WTF(s"Proof call head ${call.fn} materialized to $other")
          }
          val next = new VProofCall(fn, call.args.map(materialize(_)))
          if (call.forced ne null) next.forced = Interpreter.force(materialize(call.forced))
          if (next.synDeps.intersects(forcing)) materialize(Interpreter.force(next)) else next
      }
    }

    private def mayChange(deps: DepSet): Boolean = deps.intersects(eqStore.solvedIds) || deps.intersects(forcing)

    // An empty store is common (fresh unification and match checking); skip computing dependencies then.
    private def mayNeedMaterialization(value: Value): Boolean =
      (eqStore.subst.nonEmpty || forcing.nonEmpty) && mayChange(value.synDeps)

    private def materializeLevel(level: Level): Level =
      Interpreter.resolveInEqStore(level, eqStore) match {
        case l: Level => l
        case other    => throw NotALevel(other)
      }

    private def materializeKind(kind: Kind): Kind =
      Interpreter.resolveInEqStore(kind, eqStore) match {
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

  private final case class MappedEnv(base: Env, mapValue: Value => Value) extends DelegatingEnv {
    override def updateBase(newBase: Env): Env = copy(base = newBase)

    override lazy val locals: Vector[Binding] = base.locals.map(_.mapValue(mapValue))

    override def localBinding(ref: CoreAst.LocalRef): Binding =
      if (ref.id >= 0 && ref.id < locals.length) locals(ref.id)
      else throw NotFound(s"${ref.name}#${ref.id}")
  }
}
