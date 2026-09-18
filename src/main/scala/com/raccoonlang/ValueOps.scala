package com.raccoonlang

import com.raccoonlang.Value._

import scala.collection.immutable.VectorMap

object ValueOps {
  def materialize(value: Value, eqStore: EqStore): Value = Materialize.materialize(value)(eqStore)
  def materializeEnv(env: Env, eqStore: EqStore): Env = Materialize.materializeEnv(env)(eqStore)

  private object Materialize {
    def materializeEnv(env: Env)(implicit eqStore: EqStore): Env = {
      if (!env.locals.values.exists(mayNeedMaterialization)) env
      else env.copy(locals = VectorMap.from(env.locals.iterator.map { case (ref, value) => ref -> materialize(value) }))
    }

    def materialize(value: Value)(implicit eqStore: EqStore): Value = {
      if (!mayNeedMaterialization(value)) return value
      val resolved = Interpreter.resolveInEqStore(value, eqStore)
      if (!mayNeedMaterialization(resolved)) return resolved
      val rebuilt = resolved match {
        case LevelTpe                => resolved
        case VSort(level)            => VSort(Interpreter.resolveInEqStore(level, eqStore).asInstanceOf[Level])
        case level: Level            => level
        case Var(name, id, tpe)      => Var(name, id, materialize(tpe))
        case VConst(name, kind, tpe) => VConst(name, kind, materialize(tpe))
        case ConstructorHead(name, erased, arity, tpe, confusion) =>
          ConstructorHead(name, erased, arity, materialize(tpe), confusion)
        case VApp(head, args, tpe, blocked) =>
          VApp(materialize(head), args.map(materialize), materialize(tpe), blocked)
        case NeutralThunk(term, env, id, tpe, blocked) =>
          NeutralThunk(term, materializeEnv(env), materializeLocalId(id), materialize(tpe), blocked)
        case VProof(tpe) => VProof(materialize(tpe))
        case pi: VPi =>
          val originalStore = eqStore
          pi.copy(
            env = materializeEnv(pi.env),
            synDeps = materializeDeps(pi.synDeps),
            id = materializeId(pi.id),
            classifier0 = () => materialize(pi.tpe)(originalStore).asInstanceOf[VSort]
          )
        case lam: VLam =>
          val body = lam.body match {
            case LamBody.Core(term, env) => LamBody.Core(term, materializeEnv(env))
            case native: LamBody.Native  => native.copy(env = materializeEnv(native.env))
            case LamBody.ProofEta        => LamBody.ProofEta
          }
          lam.copy(tpe = materialize(lam.tpe).asInstanceOf[VPi], body = body, id = materializeId(lam.id))
      }
      Value.canonicalizeProof(rebuilt)
    }

    private def mayNeedMaterialization(value: Value)(implicit eqStore: EqStore): Boolean =
      value.synDeps.intersects(eqStore.solvedIds)

    private def materializeId(id: ValueId)(implicit eqStore: EqStore): ValueId = id match {
      case local: ValueId.LocalId => materializeLocalId(local)
      case other                  => other
    }

    private def materializeLocalId(id: ValueId.LocalId)(implicit eqStore: EqStore): ValueId.LocalId =
      ValueId.LocalId(id.nodeId, id.captures.map(materialize))

    private def materializeDeps(deps: DepSet)(implicit eqStore: EqStore): DepSet = {
      val result = DepSet.newBuilder
      deps.foreach { id =>
        eqStore.subst.get(id) match {
          case Some(solution) => result.unionInPlace(materialize(solution).synDeps)
          case None           => result.add(id)
        }
      }
      result.result()
    }
  }
}
