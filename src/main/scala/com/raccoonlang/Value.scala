package com.raccoonlang

import com.raccoonlang.CoreAst.{Binder, Term, TypeTerm}
import com.raccoonlang.Util.NEL

import scala.collection.immutable.BitSet

final case class InductiveMeta(
    constructorNames: Vector[String],
    paramCount: Int,
    indexCount: Int
)

sealed trait ConstType
case class Inductive(meta: InductiveMeta) extends ConstType
case object Symbol extends ConstType

sealed trait Value {
  def tpe: Value
  def synDeps: BitSet

  override def toString: String = PrettyPrinter.print(this)
}

sealed trait TopLevelValue extends Value {
  override val synDeps: BitSet = BitSet.empty
}

object Value {

  // A value that will block a computation - specifically, when trying to either match or apply it.
  // Specifically, Var, VBlockedApp, or BlockedMatch
  sealed trait Blocker extends Value {
    def blockerId: VarId
  }

  // A computation that is blocked but could proceed when blockerId is resolved. VBlockedApp or BlockedMatch
  sealed trait Blocked extends Blocker

  sealed trait UpdatableType {
    def withTpe(tpe: Value): Value
  }

  type VarId = Int

  // Identifier for lambdas to shortcut equality when possible.
  sealed trait LamId

  object LamId {
    final case class Const(name: String) extends LamId {
      override def toString: String = name
    }

    final case class LocalId(nodeId: Int, params: Vector[Value]) extends LamId
  }

  sealed trait Universe extends Value

  case object LevelTpe extends TopLevelValue {
    override def tpe: Value = VSort(Level.zero)
  }

  case object KernelObject extends TopLevelValue {
    override def tpe: Value = KernelObject
  }

  case object PropTpe extends TopLevelValue with Universe {
    override def tpe: Value = KernelObject
  }

  // Represents max(var1 + k1, var2 + k2... , c)
  // Invariant: c is either 0 or c > k1...kn
  case class Level(atoms: Map[VarId, Int], c: Int) extends Value {
    override val tpe: Value = LevelTpe

    override val synDeps: BitSet = BitSet(atoms.keys.toList: _*)
  }
  object Level {
    def addOffset(l: Level, offset: Int): Level = {
      if (offset == 0) l
      else {
        val newAtoms = l.atoms.map { case (varId, k) => (varId, k + offset) }
        val newC = if (l.c > 0 || l.atoms.isEmpty) l.c + offset else 0
        Level(newAtoms, newC)
      }
    }

    def succ(l: Level): Level = addOffset(l, 1)

    def max(xs: Vector[Level]): Level = {
      val flatAtoms = xs.flatMap(_.atoms)
      val nextAtoms = flatAtoms.foldLeft(Map.empty[VarId, Int]) { case (curMap, (varId, k)) =>
        val curK = curMap.getOrElse(varId, 0)
        curMap + (varId -> math.max(curK, k))
      }
      val cMax = xs.map(_.c).max
      val kMax = if (nextAtoms.nonEmpty) nextAtoms.values.max else 0
      val nextC = if (cMax > kMax) cMax else 0
      Level(nextAtoms, nextC)
    }

    def leq(l1: Level, l2: Level): Boolean = {
      (l1.c <= l2.c || l2.atoms.values.exists(_ >= l1.c)) &&
      l1.atoms.forall { case (varId, k) => k <= l2.atoms.getOrElse(varId, -1) }
    }

    def mk(varId: VarId): Level = Level(Map(varId -> 0), 0)

    val zero = Level(Map.empty, 0)

  }

  case class VSort(level: Level) extends Universe {
    override def tpe: Value = VSort(Level.succ(level))

    override def synDeps: BitSet = level.synDeps
  }

  // Env must be mutable in order to allow recursion - lambdas and envs must be able to point to each other
  case class VPi(
      env: Env,
      binders: NEL[Binder],
      codomain: (Env, EqStore) => Value,
      outSyntax: Option[TypeTerm],
      synDeps: BitSet,
      id: LamId,
      tpe: Universe
  ) extends Value
    with UpdatableType {
    override def toString: String = "VPi"

    override def withTpe(tpe: Value): Value = tpe match {
      case u: Universe => this.copy(tpe = u)
      case _           => throw WTF(s"Cannot update Pi type to $tpe")
    }
  }

  case class VConst(name: String, constType: ConstType, tpe: Value) extends Value with UpdatableType {
    override val synDeps: BitSet = tpe.synDeps

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  sealed trait AppliedValue extends Value {
    def head: Value

    def args: NEL[Value]

    def tpe: Value

    override lazy val synDeps: BitSet = {
      val res = collection.mutable.BitSet()
      res |= head.synDeps
      args.foreach(v => res |= v.synDeps)
      res |= tpe.synDeps
      res.toImmutable
    }
  }

  case class VApp(head: VConst, args: NEL[Value], tpe: Value) extends AppliedValue with UpdatableType {
    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  case class VBlockedApp(head: Value, args: NEL[Value], tpe: Value, blockerId: VarId)
    extends AppliedValue
    with Blocked
    with UpdatableType {
    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  case class Var(name: String, id: VarId, tpe: Value) extends Value with Blocker with UpdatableType {
    override val synDeps: BitSet = tpe.synDeps + id

    override val blockerId: VarId = id

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  case class VLam(tpe: VPi, id: LamId, isStable: Boolean, run: (NEL[Value], EqStore) => Value) extends Value {
    override lazy val synDeps: BitSet = {
      id match {
        case LamId.Const(_) => tpe.synDeps
        case LamId.LocalId(_, params) =>
          if (params.isEmpty) tpe.synDeps
          else {
            val res = collection.mutable.BitSet()
            res |= tpe.synDeps
            params.foreach(v => res |= v.synDeps)
            res.toImmutable
          }
      }
    }
  }

  case class ConstructorHead(name: String, numParams: Int, totalArity: Int, tpe: Value)
    extends TopLevelValue
    with UpdatableType {
    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  // Fully applied constructor.
  case class VCtor(head: ConstructorHead, fields: Vector[Value], tpe: Value) extends Value with UpdatableType {
    override lazy val synDeps: BitSet = {
      val res = collection.mutable.BitSet()
      res |= head.synDeps
      fields.foreach(v => res |= v.synDeps)
      res |= tpe.synDeps
      res.toImmutable
    }

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  trait VMatch extends Value {
    def id: LamId.LocalId

    def scrut: Value

    def tpe: Value

    override def synDeps: BitSet = {
      val res = collection.mutable.BitSet()
      res |= tpe.synDeps
      res |= scrut.synDeps
      id.params.foreach(v => res |= v.synDeps)
      res.toImmutable
    }
  }

  // The scrutinee of the match is an opaque symbol, so match will never proceed
  case class StuckMatch(id: LamId.LocalId, scrut: Value, tpe: Value) extends VMatch with UpdatableType {
    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  case class BlockedMatch(id: LamId.LocalId, term: Term.Match, scrut: Value, env: Env, tpe: Value, blockerId: VarId)
    extends VMatch
    with Blocked
    with UpdatableType {
    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  object NormalizerType extends TopLevelValue {
    override def tpe: Value = VSort(Level.zero)
  }

  trait Normalizer extends TopLevelValue {
    def carrierKey: Normalizers.CarrierKey

    def normalize(v: Value, eqStore: EqStore): Value

    def name: String

    override val tpe: Value = NormalizerType
  }

}
