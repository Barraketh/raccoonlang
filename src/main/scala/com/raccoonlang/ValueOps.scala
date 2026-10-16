package com.raccoonlang

import com.raccoonlang.Value._

import scala.collection.immutable.VectorMap

object ValueOps {
  def materialize(value: Value, eqStore: EqStore): Value = newMaterializer(eqStore).materialize(value)

  def materializeEnv(env: Env, eqStore: EqStore): Env = newMaterializer(eqStore).materializeEnv(env)

  private[raccoonlang] def newMaterializer(eqStore: EqStore): Materializer = new Materializer(eqStore)

  /** A delayed classifier starts a fresh root operation when it is first forced. */
  private[raccoonlang] def materializeClassifier(classifier: Classifier, eqStore: EqStore): Classifier =
    classifier match {
      case sort: VSort if !sort.synDeps.intersects(eqStore.solvedIds) => sort
      case Large                                                      => Large
      case other => newMaterializer(eqStore).materializeClassifier(other)
    }

  /**
   * One identity memo scoped to one eager materialization root and one immutable equality store. The resolver shares
   * this session when it materializes values while reducing blocked applications or thunks.
   */
  private[raccoonlang] final class Materializer private[ValueOps] (val eqStore: EqStore) {
    private val values = new java.util.IdentityHashMap[Value, Value]()
    private val envs = new java.util.IdentityHashMap[Env, Env]()

    def resolve(value: Value): Value = Interpreter.resolveInEqStore(value, this)

    def materializeEnv(env: Env): Env = {
      if (envs.containsKey(env)) return envs.get(env)

      val rebuilt = env.copy(
        locals = VectorMap.from(env.locals.iterator.map { case (ref, value) => ref -> materialize(value) })
      )
      envs.put(env, rebuilt)
      rebuilt
    }

    def materialize(value: Value): Value = {
      if (values.containsKey(value)) return values.get(value)
      if (!mayNeedMaterialization(value)) {
        values.put(value, value)
        return value
      }

      val resolved = resolve(value)
      if (values.containsKey(resolved)) {
        val cached = values.get(resolved)
        values.put(value, cached)
        return cached
      }
      if (!mayNeedMaterialization(resolved)) {
        values.put(value, resolved)
        if (resolved ne value) values.put(resolved, resolved)
        return resolved
      }

      val rebuilt = resolved match {
        case LevelTpe | LevelClassifier | Large => resolved
        case level: Level                       => materializeLevel(level)
        case sort: VSort                        => rebuildClassifier(sort)
        case Var(name, id, tpe)                 => Var(name, id, materialize(tpe))
        case VConst(name, constType, tpe)       => VConst(name, constType, materialize(tpe))
        case VApp(head, args, tpe, blockedOn) =>
          VApp(materialize(head), args.map(materialize), materialize(tpe), blockedOn)
        case NeutralThunk(term, env, id, tpe, blockedOn) =>
          NeutralThunk(term, materializeEnv(env), materializeLocalId(id), materialize(tpe), blockedOn)
        case ctor: ConstructorHead => ctor.copy(tpe = materialize(ctor.tpe))
        case pi: VPi               => materializePi(pi)
        case VLam(tpe, id, body)   => VLam(materializePi(tpe), materializeId(id), materializeLamBody(body))
        case proof: VProof         => VProof(materialize(proof.tpe))
      }
      // Materialization can reveal the exact proposition behind a type meta, so rerun proof reconstruction and
      // canonicalization against that sharpened type. Deferred structure expansion remains at its equality boundary.
      val canonical = Value.canonicalizeProof(rebuilt)
      values.put(value, canonical)
      if (resolved ne value) values.put(resolved, canonical)
      canonical
    }

    private def mayNeedMaterialization(value: Value): Boolean =
      value.synDeps.intersects(eqStore.solvedIds)

    private def materializeLevel(level: Level): Level =
      resolve(level) match {
        case normal: Level => normal
        case other         => wtf(s"$level : ${level.tpe} materialized to $other : ${other.tpe}")
      }

    def materializeClassifier(classifier: Classifier): Classifier =
      classifier match {
        case sort: VSort => materialize(sort).asInstanceOf[VSort]
        case Large       => Large
      }

    private def rebuildClassifier(classifier: Classifier): Classifier =
      classifier match {
        case sort: VSort =>
          if (mayNeedMaterialization(sort))
            if (sort.isProp) Sorts.Prop
            else Sorts.sort(materializeLevel(sort.level))
          else sort
        case Large => Large
      }

    private def materializePi(pi: VPi): VPi = {
      val store = eqStore
      val originalPi = pi
      pi.copy(
        env = materializeEnv(pi.env),
        synDeps = materializeDeps(pi.synDeps),
        id = materializeId(pi.id),
        classifier0 = () => ValueOps.materializeClassifier(originalPi.tpe, store),
        isPropValued = pi.isPropValued
      )
    }

    private def materializeId(id: ValueId): ValueId =
      id match {
        case local: ValueId.LocalId => materializeLocalId(local)
        case other                  => other
      }

    private def materializeLocalId(id: ValueId.LocalId): ValueId.LocalId =
      ValueId.LocalId(id.nodeId, id.captures.map(materialize))

    private def materializeLamBody(body: LamBody): LamBody =
      body match {
        case LamBody.Core(term, env) => LamBody.Core(term, materializeEnv(env))
        case LamBody.Native(run, env, isRawRecursive) =>
          LamBody.Native(run, materializeEnv(env), isRawRecursive)
        case LamBody.ProofEta => LamBody.ProofEta
      }

    private def materializeDeps(deps: DepSet): DepSet = {
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
