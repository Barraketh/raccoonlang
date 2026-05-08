package com.raccoonlang

import com.raccoonlang.Value._

object ValueOps {
  def materializeEnv(env: EnvLike[_], eqStore: EqStore): RuntimeEnv = {
    val locals = env.locals.map(_.mapValue(materialize(_, eqStore)))

    RuntimeEnv(env.globals, locals)
  }

  def materialize(value: Value, eqStore: EqStore): Value = {
    if (!mayNeedMaterialization(value, eqStore)) return value

    val resolved = Interpreter.resolveInEqStore(value)(eqStore)
    if (!mayNeedMaterialization(resolved, eqStore)) return resolved

    resolved match {
      case LevelTpe | KernelObject | PropTpe | NormalizerType => resolved
      case n: Normalizer                                      => n
      case level: Level                                       => materializeLevel(level, eqStore)
      case VSort(level)                                       => VSort(materializeLevel(level, eqStore))
      case Var(name, id, tpe)                                 => Var(name, id, materialize(tpe, eqStore))
      case VConst(name, constType, tpe)                       => VConst(name, constType, materialize(tpe, eqStore))
      case VApp(head, args, tpe) =>
        VApp(materializeConst(head, eqStore), args.map(materialize(_, eqStore)), materialize(tpe, eqStore))
      case VBlockedApp(head, args, tpe, blockerId) =>
        VBlockedApp(
          materialize(head, eqStore),
          args.map(materialize(_, eqStore)),
          materialize(tpe, eqStore),
          blockerId
        )
      case VBlockedThunk(body, id, tpe, blockerId) =>
        VBlockedThunk(
          materializeBlockedThunkBody(body, eqStore),
          materializeLocalId(id, eqStore),
          materialize(tpe, eqStore),
          blockerId
        )
      case ctor: ConstructorHead =>
        ctor.copy(tpe = materialize(ctor.tpe, eqStore))
      case VCtor(head, fields, tpe) =>
        VCtor(
          head.copy(tpe = materialize(head.tpe, eqStore)),
          fields.map(materialize(_, eqStore)),
          materialize(tpe, eqStore)
        )
      case pi: VPi =>
        materializePi(pi, eqStore)
      case VLam(tpe, id, isStable, body) =>
        VLam(materializePi(tpe, eqStore), materializeId(id, eqStore), isStable, materializeLamBody(body, eqStore))
    }
  }

  private def mayNeedMaterialization(value: Value, eqStore: EqStore): Boolean =
    value.synDeps.intersects(eqStore.solvedIds)

  private def materializeLevel(level: Level, eqStore: EqStore): Level =
    Interpreter.resolveInEqStore(level)(eqStore) match {
      case l: Level => l
      case other    => throw NotALevel(other)
    }

  private def materializeUniverse(value: Universe, eqStore: EqStore): Universe =
    materialize(value, eqStore) match {
      case u: Universe => u
      case other       => throw NotAType(other)
    }

  private def materializePi(pi: VPi, eqStore: EqStore): VPi =
    pi.copy(
      env = materializeEnv(pi.env, eqStore),
      synDeps = materializeDeps(pi.synDeps, eqStore),
      id = materializeId(pi.id, eqStore),
      tpe = materializeUniverse(pi.tpe, eqStore)
    )

  private def materializeConst(value: VConst, eqStore: EqStore): VConst =
    value.copy(tpe = materialize(value.tpe, eqStore))

  private def materializeId(id: ValueId, eqStore: EqStore): ValueId =
    id match {
      case local: ValueId.LocalId => materializeLocalId(local, eqStore)
      case other                  => other
    }

  private def materializeLocalId(id: ValueId.LocalId, eqStore: EqStore): ValueId.LocalId =
    ValueId.LocalId(id.nodeId, id.captures.map(materialize(_, eqStore)))

  private def materializeLamBody(body: LamBody, eqStore: EqStore): LamBody =
    body match {
      case LamBody.Core(term, env) => LamBody.Core(term, materializeEnv(env, eqStore))
      case native: LamBody.Native  => native
    }

  private def materializeBlockedThunkBody(body: BlockedThunkBody, eqStore: EqStore): BlockedThunkBody =
    body match {
      case BlockedThunkBody.Select(base, field, env, locationId) =>
        BlockedThunkBody.Select(materialize(base, eqStore), field, materializeEnv(env, eqStore), locationId)
      case BlockedThunkBody.Match(term, env) =>
        BlockedThunkBody.Match(term, materializeEnv(env, eqStore))
    }

  private def materializeDeps(deps: DepSet, eqStore: EqStore): DepSet = {
    val res = DepSet.newBuilder
    deps.foreach { id =>
      eqStore.subst.get(id) match {
        case Some(solution) => res.unionInPlace(materialize(solution, eqStore).synDeps)
        case None           => res.add(id)
      }
    }
    res.result()
  }
}
