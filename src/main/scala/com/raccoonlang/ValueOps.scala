package com.raccoonlang

import com.raccoonlang.Value._

object ValueOps {
  def materialize(value: Value, eqStore: EqStore): Value = Materialize.materialize(value)(eqStore)

  def materializeEnv(env: Env, eqStore: EqStore): Env = Materialize.materializeEnv(env)(eqStore)

  private object Materialize {
    def materializeEnv(env: Env)(implicit eqStore: EqStore): Env = {
      MappedEnv(env, value => materialize(value))
    }

    private final case class MappedEnv(base: Env, mapValue: Value => Value) extends DelegatingEnv {
      override def updateBase(newBase: Env): Env = copy(base = newBase)

      override lazy val locals: Vector[Binding] = base.locals.map(_.mapValue(mapValue))

      override def localBinding(ref: CoreAst.LocalRef): Binding =
        if (ref.id >= 0 && ref.id < locals.length) locals(ref.id)
        else throw NotFound(s"${ref.name}#${ref.id}")
    }

    def materialize(value: Value)(implicit eqStore: EqStore): Value = {
      if (!mayNeedMaterialization(value)) return value

      val resolved = Interpreter.resolveInEqStore(value, eqStore)
      if (!mayNeedMaterialization(resolved)) return resolved

      resolved match {
        case LevelTpe | KernelObject | PropTpe | NormalizerType => resolved
        case n: Normalizer                                      => n
        case level: Level                                       => materializeLevel(level)
        case VSort(level)                                       => VSort(materializeLevel(level))
        case Var(name, id, tpe)                                 => Var(name, id, materialize(tpe))
        case VConst(name, constType, tpe)                       => VConst(name, constType, materialize(tpe))
        case VApp(head, args, tpe, blockerId, spine) =>
          VApp(materialize(head), args.map(materialize(_)), materialize(tpe), blockerId, spine.map(materializeSpine))
        case NeutralThunk(term, env, id, tpe, blockerId, spine) =>
          NeutralThunk(
            term,
            materializeEnv(env),
            materializeLocalId(id),
            materialize(tpe),
            blockerId,
            spine.map(materializeSpine)
          )
        case ctor: ConstructorHead =>
          ctor.copy(tpe = materialize(ctor.tpe))
        case pi: VPi =>
          materializePi(pi)
        case VLam(tpe, id, isStable, body) =>
          VLam(materializePi(tpe), materializeId(id), isStable, materializeLamBody(body))
      }
    }

    private def mayNeedMaterialization(value: Value)(implicit eqStore: EqStore): Boolean =
      value.synDeps.intersects(eqStore.solvedIds)

    // Spines are views, not structure: rebuild positionally rather than re-entering `materialize`, which
    // could reduce the named form away.
    private def materializeSpine(s: VApp)(implicit eqStore: EqStore): VApp =
      VApp(materialize(s.head), s.args.map(materialize(_)), materialize(s.tpe), s.blockerId, None)

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
