package com.raccoonlang

import com.raccoonlang.Value._

object ValueOps {
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
      case VBlockedThunk(thunk, id, tpe, blockerId) =>
        VBlockedThunk(
          thunk,
          ValueId.LocalId(id.nodeId, id.captures.map(materialize(_, eqStore))),
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
      case VLam(tpe, id, isStable, run) =>
        VLam(materializePi(tpe, eqStore), materializeId(id, eqStore), isStable, run)
    }
  }

  private def mayNeedMaterialization(value: Value, eqStore: EqStore): Boolean =
    if (eqStore.subst.isEmpty) false
    else
      value match {
        case blocked: Blocker => ((value.synDeps + blocked.blockerId) & eqStore.solvedIds).nonEmpty
        case _                => (value.synDeps & eqStore.solvedIds).nonEmpty
      }

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
    pi.copy(tpe = materializeUniverse(pi.tpe, eqStore))

  private def materializeConst(value: VConst, eqStore: EqStore): VConst =
    value.copy(tpe = materialize(value.tpe, eqStore))

  private def materializeId(id: ValueId, eqStore: EqStore): ValueId =
    id match {
      case ValueId.LocalId(nodeId, captures) => ValueId.LocalId(nodeId, captures.map(materialize(_, eqStore)))
      case other                             => other
    }
}
