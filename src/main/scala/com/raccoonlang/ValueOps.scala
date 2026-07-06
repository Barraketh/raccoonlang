package com.raccoonlang

import com.raccoonlang.Value._

import scala.collection.immutable.VectorMap

object ValueOps {
  def materialize(value: Value, eqStore: EqStore): Value = Materialize.materialize(value)(eqStore)

  def materializeEnv(env: Env[Value], eqStore: EqStore): Env[Value] = Materialize.materializeEnv(env)(eqStore)

  private object Materialize {
    def materializeEnv(env: Env[Value])(implicit eqStore: EqStore): Env[Value] =
      env.copy(locals = VectorMap.from(env.locals.iterator.map { case (ref, value) => ref -> materialize(value) }))

    def materialize(value: Value)(implicit eqStore: EqStore): Value = {
      if (!mayNeedMaterialization(value)) return value

      val resolved = Interpreter.resolveInEqStore(value, eqStore)
      if (!mayNeedMaterialization(resolved)) return resolved

      resolved match {
        case LevelTpe                     => resolved
        case level: Level                 => materializeLevel(level)
        case VSort(level)                 => VSort(materializeLevel(level))
        case Var(name, id, tpe)           => Var(name, id, materialize(tpe))
        case VConst(name, constType, tpe) => VConst(name, constType, materialize(tpe))
        case VApp(head, args, tpe, blockerId) =>
          VApp(materialize(head), args.map(materialize(_)), materialize(tpe), blockerId)
        case NeutralThunk(term, env, id, tpe, blockerId) =>
          NeutralThunk(
            term,
            materializeEnv(env),
            materializeLocalId(id),
            materialize(tpe),
            blockerId
          )
        case ctor: ConstructorHead =>
          ctor.copy(tpe = materialize(ctor.tpe))
        case pi: VPi =>
          materializePi(pi)
        case VLam(tpe, id, body) =>
          VLam(materializePi(tpe), materializeId(id), materializeLamBody(body))
      }
    }

    private def mayNeedMaterialization(value: Value)(implicit eqStore: EqStore): Boolean =
      value.synDeps.intersects(eqStore.solvedIds)

    private def materializeLevel(level: Level)(implicit eqStore: EqStore): Level =
      Interpreter.resolveInEqStore(level, eqStore) match {
        case l: Level => l
        case other    => throw NotALevel(other)
      }

    private def materializeUniverse(value: VSort)(implicit eqStore: EqStore): VSort =
      materialize(value) match {
        case u: VSort => u
        case other    => throw NotAType(other)
      }

    private def materializePi(pi: VPi)(implicit eqStore: EqStore): VPi =
      pi.copy(
        env = materializeEnv(pi.env),
        synDeps = materializeDeps(pi.synDeps),
        id = materializeId(pi.id),
        tpe = materializeUniverse(pi.tpe)
      )

    private def materializeId(id: ValueId)(implicit eqStore: EqStore): ValueId =
      id match {
        case local: ValueId.LocalId => materializeLocalId(local)
        case other                  => other
      }

    private def materializeLocalId(id: ValueId.LocalId)(implicit eqStore: EqStore): ValueId.LocalId =
      ValueId.LocalId(id.nodeId, id.captures.map(materialize(_)))

    private def materializeLamBody(body: LamBody)(implicit eqStore: EqStore): LamBody =
      body match {
        case LamBody.Core(term, env) => LamBody.Core(term, materializeEnv(env))
        case LamBody.Native(run, env, isRawRecursive) =>
          LamBody.Native(run, materializeEnv(env), isRawRecursive)
      }

    private def materializeDeps(deps: DepSet)(implicit eqStore: EqStore): DepSet = {
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
}
