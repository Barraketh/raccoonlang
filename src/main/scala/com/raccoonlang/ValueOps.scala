package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.packed.Words

object ValueOps {

  /** Transitively substitute solved dependencies and resume affected blocked computations before rebuilding values. */
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
        case LevelTpe | KernelObject | PropTpe => resolved
        case level: Level                      => materializeLevel(level)
        case VSort(level)                      => VSort(materializeLevel(level))
        case Var(name, id, tpe)                => Var(name, id, materialize(tpe))
        case VConst(name, constType, tpe)      => VConst(name, constType, materialize(tpe))
        case poly: VNatPoly                    => NatNormalForm.substituteAtoms(poly, materialize(_))
        // In one loop, splicing in a solved terminator; every part of the result is materialized, so it is too.
        case word: VWord => Words.map(word, _.intersects(eqStore.solvedIds), materialize(_))
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
            materializeLocalId(id),
            materialize(tpe),
            materializeDeps(blockerIds)
          )
        case ctor: ConstructorHead =>
          ctor.copy(tpe = materialize(ctor.tpe))
        case pi: VPi =>
          materializePi(pi)
        case VLam(tpe, id, body) =>
          VLam(materializePi(tpe), materializeId(id), materializeLamBody(body))
      }
    }

    // An empty store is common (fresh unification and match checking); skip computing dependencies then.
    private def mayNeedMaterialization(value: Value)(implicit eqStore: EqStore): Boolean =
      eqStore.subst.nonEmpty && value.synDeps.intersects(eqStore.solvedIds)

    private def materializeLevel(level: Level)(implicit eqStore: EqStore): Level =
      Interpreter.resolveInEqStore(level, eqStore) match {
        case l: Level => l
        case other    => throw NotALevel(other)
      }

    private def materializeUniverse(value: Universe)(implicit eqStore: EqStore): Universe =
      materialize(value) match {
        case u: VSort => u
        case PropTpe  => PropTpe
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
}
