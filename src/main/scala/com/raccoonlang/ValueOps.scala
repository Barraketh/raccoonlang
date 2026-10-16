package com.raccoonlang

import com.raccoonlang.Value._

import scala.collection.immutable.VectorMap
import scala.reflect.ClassTag

object ValueOps {
  def materialize(value: Value, eqStore: EqStore): Value = Materialize.materialize(value)(eqStore)

  def materializeEnv(env: Env, eqStore: EqStore): Env = Materialize.materializeEnv(env)(eqStore)

  private object Materialize {
    def materializeEnv(env: Env)(implicit eqStore: EqStore): Env =
      env.copy(locals = VectorMap.from(env.locals.iterator.map { case (ref, value) => ref -> materialize(value) }))

    def materialize(value: Value)(implicit eqStore: EqStore): Value = {
      if (!mayNeedMaterialization(value)) return value

      val resolved = Interpreter.resolveInEqStore(value, eqStore)
      if (!mayNeedMaterialization(resolved)) return resolved

      val rebuilt = resolved match {
        case _: ParameterTpe | SortParameter | Large => resolved
        case level: Level                            => materializeParameter(level)
        case sort: VSort                             => materializeClassifier(sort)
        case Var(name, id, tpe)                      => Var(name, id, materialize(tpe))
        case VConst(name, constType, tpe)            => VConst(name, constType, materialize(tpe))
        case VApp(head, args, tpe, blockedOn) =>
          val materializedHead = materialize(head)
          val materializedArgs = args.map(materialize(_))
          val materializedTpe = materialize(tpe)
          VApp(materializedHead, materializedArgs, materializedTpe, blockedOn)
        case NeutralThunk(term, env, id, tpe, blockedOn) =>
          NeutralThunk(
            term,
            materializeEnv(env),
            materializeLocalId(id),
            materialize(tpe),
            blockedOn
          )
        case ctor: ConstructorHead =>
          ctor.copy(tpe = materialize(ctor.tpe))
        case pi: VPi =>
          materializePi(pi)
        case VLam(tpe, id, body) =>
          VLam(materializePi(tpe), materializeId(id), materializeLamBody(body))
        case p: VProof =>
          VProof(materialize(p.tpe))
      }
      // Deferred collapse: a type may resolve to a proposition only once its metas solve
      // (e.g. u := 0); the proof policy applies at that point (docs/kernel.md#proofs-and-elimination). Deferred struct
      // expansion deliberately does NOT happen here: materialization reaches inside values
      // (projection bases, thunk envs), and wrapping an interior copy while bare copies circulate
      // would split the representation with no mixed defEq rule to reunite it (StructEta).
      Value.canonicalizeProof(rebuilt)
    }

    private def mayNeedMaterialization(value: Value)(implicit eqStore: EqStore): Boolean =
      value.synDeps.intersects(eqStore.solvedIds)

    /** A level resolves to another normalized level. */
    private def materializeParameter[P <: Value: ClassTag](parameter: P)(implicit eqStore: EqStore): P =
      Interpreter.resolveInEqStore(parameter, eqStore) match {
        case normal: P => normal
        case other     => wtf(s"$parameter : ${parameter.tpe} materialized to $other : ${other.tpe}")
      }

    private def materializeClassifier(classifier: Classifier)(implicit eqStore: EqStore): Classifier =
      classifier match {
        case sort: VSort =>
          if (mayNeedMaterialization(sort))
            Sorts.sort(
              materializeParameter(sort.level)
            )
          else sort
        case Large => Large
      }

    private def materializePi(pi: VPi)(implicit eqStore: EqStore): VPi = {
      // The classifier stays lazy: force the original thunk only on demand, then rewrite solved
      // metas under this (immutable) store.
      val store = eqStore
      pi.copy(
        env = materializeEnv(pi.env),
        synDeps = materializeDeps(pi.synDeps),
        id = materializeId(pi.id),
        classifier0 = () => materializeClassifier(pi.tpe)(store)
      )
    }

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
        case LamBody.ProofEta => LamBody.ProofEta
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
