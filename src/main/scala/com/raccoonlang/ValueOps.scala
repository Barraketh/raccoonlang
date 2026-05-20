package com.raccoonlang

import com.raccoonlang.Value._

object ValueOps {
  def materialize(value: Value, eqStore: EqStore): Value = Materialize.materialize(value)(eqStore)

  def materializeEnv(env: EnvLike[_], eqStore: EqStore): RuntimeEnv = Materialize.materializeEnv(env)(eqStore)

  private object Materialize {
    def materializeEnv(env: EnvLike[_])(implicit eqStore: EqStore): RuntimeEnv = {
      val locals = env.locals.map(_.mapValue(materialize(_)))

      RuntimeEnv(env.globals, locals)
    }

    def materialize(value: Value)(implicit eqStore: EqStore): Value = {
      if (!mayNeedMaterialization(value)) return value

      val resolved = Interpreter.resolveInEqStore(value)(eqStore)
      if (!mayNeedMaterialization(resolved.value)) return resolved.value

      resolved.caseOf {
        case LevelTpe | KernelObject | PropTpe | NormalizerType => resolved.value
        case n: Normalizer                                      => n
        case level: Level                                       => materializeLevel(level)
        case VSort(level)                                       => VSort(materializeLevel(level))
        case Var(name, id, tpe)                                 => Var(name, id, materialize(tpe))
        case VConst(name, constType, tpe)                       => VConst(name, constType, materialize(tpe))
        case VApp(head, args, tpe) =>
          VApp(materializeConst(head), args.map(materialize(_)), materialize(tpe))
        case VBlockedApp(head, args, tpe, blockerId) =>
          VBlockedApp(
            materialize(head),
            args.map(materialize(_)),
            materialize(tpe),
            blockerId
          )
        case VBlockedThunk(body, id, tpe, blockerId) =>
          VBlockedThunk(
            materializeThunkBody(body),
            materializeLocalId(id),
            materialize(tpe),
            blockerId
          )
        case VStuckThunk(body, id, tpe) =>
          VStuckThunk(
            materializeThunkBody(body),
            materializeLocalId(id),
            materialize(tpe)
          )
        case ctor: ConstructorHead =>
          ctor.copy(tpe = materialize(ctor.tpe))
        case VCtor(head, args, tpe) =>
          VCtor(
            head.copy(tpe = materialize(head.tpe)),
            args.map(materialize(_)),
            materialize(tpe)
          )
        case pi: VPi =>
          materializePi(pi)
        case VLam(tpe, id, isStable, body) =>
          VLam(materializePi(tpe), materializeId(id), isStable, materializeLamBody(body))
      }
    }

    private def mayNeedMaterialization(value: Value)(implicit eqStore: EqStore): Boolean =
      value.synDeps.intersects(eqStore.solvedIds)

    private def materializeLevel(level: Level)(implicit eqStore: EqStore): Level =
      level.caseOf {
        case l: Level => l
        case other    => throw NotALevel(other)
      }

    private def materializeUniverse(value: Universe)(implicit eqStore: EqStore): Universe =
      materialize(value) match {
        case u: Universe => u
        case other       => throw NotAType(other)
      }

    private def materializePi(pi: VPi)(implicit eqStore: EqStore): VPi =
      pi.copy(
        env = materializeEnv(pi.env),
        synDeps = materializeDeps(pi.synDeps),
        id = materializeId(pi.id),
        tpe = materializeUniverse(pi.tpe)
      )

    private def materializeConst(value: VConst)(implicit eqStore: EqStore): VConst =
      value.copy(tpe = materialize(value.tpe))

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
        case native: LamBody.Native  => native
      }

    private def materializeThunkBody(body: ThunkBody)(implicit eqStore: EqStore): ThunkBody =
      body match {
        case ThunkBody.Select(base, field, env, locationId) =>
          ThunkBody.Select(materialize(base), field, materializeEnv(env), locationId)
        case ThunkBody.Match(term, env) =>
          ThunkBody.Match(term, materializeEnv(env))
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
