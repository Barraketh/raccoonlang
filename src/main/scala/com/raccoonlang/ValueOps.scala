package com.raccoonlang

import com.raccoonlang.Value._

import scala.collection.immutable.SeqMap
import scala.reflect.ClassTag

object ValueOps {
  def materialize(value: Value, eqStore: EqStore): Value = Materialize.materialize(value)(eqStore)

  def materializeEnv(env: Env, eqStore: EqStore): Env = Materialize.materializeEnv(env)(eqStore)

  /** An application's stored argument or a local, materialized, unforced evidence staying unforced. */
  def materializeArgument(arg: Value, eqStore: EqStore): Value = Materialize.materializeArgument(arg)(eqStore)

  private object Materialize {

    /**
     * Each local materialized as an argument is: one bound to unforced evidence, as a destructuring binds it, stays so.
     */
    def materializeEnv(env: Env)(implicit eqStore: EqStore): Env =
      env
        .copy(
          baseLocals = SeqMap.from(env.baseLocals.iterator.map { case (ref, value) =>
            ref -> materializeArgument(value)
          }),
          runtimeLocals = SeqMap.from(env.runtimeLocals.iterator.map { case (ref, value) =>
            ref -> materializeArgument(value)
          }),
          runtimeFrames = env.runtimeFrames.map(_.mapValues(materializeArgument))
        )
        .rebuildRuntimeLookupIndex

    def materialize(value: Value)(implicit eqStore: EqStore): Value = {
      if (!mayNeedMaterialization(value)) return value

      val resolved = Interpreter.resolveInEqStore(value, eqStore)
      if (!mayNeedMaterialization(resolved)) return resolved

      val rebuilt = resolved match {
        case _: ParameterTpe | SortParameter | Large => resolved
        case level: Level                            => materializeParameter(level)
        case kind: Kind                              => materializeParameter(kind)
        case lifetime: Lifetime                      => materializeParameter(lifetime)
        case sort: VSort                             => materializeClassifier(sort)
        case Var(name, id, tpe)                      => Var(name, id, materialize(tpe))
        case VConst(name, constType, tpe)            => VConst(name, constType, materialize(tpe))
        case app: VApp =>
          val (head, tpe, blockedOn) = (app.head, app.tpe, app.blockedOn)
          val materializedHead = materialize(head)
          val materializedArgs = app.storedArgs.map(materializeArgument(_))
          val materializedTpe = materialize(tpe)
          (materializedHead, blockedOn) match {
            case (h: ConstructorHead, blockers) if blockers.isEmpty =>
              Packed
                .foldCtor(h, materializedArgs, materializedTpe)
                .getOrElse(VApp(materializedHead, materializedArgs, materializedTpe, blockedOn))
            case _ => VApp(materializedHead, materializedArgs, materializedTpe, blockedOn)
          }
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
        // A packed literal's type is closed (VPacked requires it), so it never reaches here:
        // `mayNeedMaterialization` has already returned false for anything with no dependencies.
        case p: VPacked                 => p
        case deferred: DeferredEvidence => deferred.escaped
      }
      // A type meta may resolve to a proposition; the proof policy applies after materializing it
      // (docs/kernel.md#proofs-and-elimination). Deferred struct
      // expansion deliberately does NOT happen here: materialization reaches inside values
      // (projection bases, thunk envs), and wrapping an interior copy while bare copies circulate
      // would split the representation with no mixed defEq rule to reunite it (StructEta).
      Value.canonicalizeProof(rebuilt)
    }

    /**
     * An application's stored argument. Unforced evidence stays unforced, its proposition materialized when it is
     * forced: materializing is not a use of the proof.
     */
    def materializeArgument(arg: Value)(implicit eqStore: EqStore): Value =
      arg match {
        case deferred: DeferredEvidence => deferred.map(materialize(_))
        case other                      => materialize(other)
      }

    // Constant time: a value's dependencies are computed when it is built.
    private def mayNeedMaterialization(value: Value)(implicit eqStore: EqStore): Boolean =
      value.synDeps.intersects(eqStore.solvedIds)

    /** A level, kind or lifetime, which resolves to a normal form of the same sort parameter. */
    private def materializeParameter[P <: Value: ClassTag](parameter: P)(implicit eqStore: EqStore): P =
      Interpreter.resolveInEqStore(parameter, eqStore) match {
        case normal: P => normal
        case other     => wtf(s"$parameter : ${parameter.tpe} materialized to $other : ${other.tpe}")
      }

    private def materializeClassifier(classifier: Classifier)(implicit eqStore: EqStore): Classifier =
      classifier match {
        case sort: VSort =>
          if (mayNeedMaterialization(sort))
            if (Sorts.isProp(sort)) Sorts.prop(materializeParameter(sort.scope))
            else
              Sorts.sort(
                materializeParameter(sort.level),
                materializeParameter(sort.kind),
                materializeParameter(sort.scope)
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
        closureKind = materializeParameter(pi.closureKind),
        closureScope = materializeParameter(pi.closureScope),
        mentionedScope = materializeParameter(pi.mentionedScope),
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
