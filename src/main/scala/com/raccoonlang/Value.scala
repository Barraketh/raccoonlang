package com.raccoonlang

import com.raccoonlang.Value.ResolvedValue

/**
 * Represents a typechecked value representation - the values that live in an Env. Values can contain Vars(), which
 * represent unknown values. Vars have a unique id, which means they can participate in equality. Thus values could be
 * thought of as a typed, maximally reduced representation of CoreAst / ElabAst.
 *
 * Values are meant to be interpreted in the context of an EqStore, which carries Var assignments. When we discover a
 * solution (Var1 = Foo), we do not rewrite the entire value, but instead just add it to EqStore. When traversing a
 * Value, if we encounter any Var, we need to check whether it's been resolved to anything, which is done through
 * [[Interpreter.resolveInEqStore]]
 *
 * IMPORTANT: DO NOT DIRECTLY PATTERN MATCH Values, unless they have already been resolved, or you know EqStore to be
 * empty (such as during type-checking of globals). Either call [[Interpreter.resolveInEqStore]] directly, or use
 * value.caseOf, which calls it automatically
 *
 * Invariants:
 *   - Every value is typed correctly. Types are themselves Values, and so are Sorts and Levels
 *   - synDeps is the set of all VarIds that this Value contains, including in its type. It is extremely important to
 * maintain this correctly
 *   - key - a structural hash key of this value. Lazily computed by ValueKey.orderKey(). Used by defEq and Normalizers
 *   - needsStructuralDefEq: tracks values whose key may differ even when structural equality can still succeed
 */
sealed trait Value {
  def tpe: Value
  def synDeps: DepSet

  final lazy val key: ValueKey.Key = ValueKey.orderKey(this)
  final lazy val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)

  override def toString: String = PrettyPrinter.print(this)

  // Some convenience methods for resolving values
  def caseOf[B](f: PartialFunction[Value, B])(implicit eqStore: EqStore): B =
    Interpreter.resolveInEqStore(this).caseOf(f)

  def use[B](f: ResolvedValue => B)(implicit eqStore: EqStore): B =
    f(Interpreter.resolveInEqStore(this))
}

sealed trait TopLevelValue extends Value {
  override val synDeps: DepSet = DepSet.empty
}

object Value {
  def ascribe(value: Value, tpe: Value): Value =
    value match {
      case u: UpdatableType => u.withTpe(tpe)
      case _                => value
    }

  private def isKnownProof(value: Value): Boolean =
    value.tpe match {
      case PropTpe => false
      case tpe     => tpe.tpe == PropTpe
    }

  private[raccoonlang] def needsStructuralDefEq(value: Value): Boolean =
    isKnownProof(value) || (value match {
      case _: VPi | _: VLam      => true
      case app: AppliedValue     => app.head.needsStructuralDefEq || app.args.exists(_.needsStructuralDefEq)
      case VCtor(_, fields, tpe) => fields.exists(_.needsStructuralDefEq) || tpe.needsStructuralDefEq
      case _                     => false
    })

  // A value that will block a computation - specifically, when trying to either match or apply it.
  // Specifically, Var, VBlockedApp, or VBlockedThunk
  sealed trait Blocker extends Value {
    def blockerId: VarId
  }

  // A computation that is blocked but could proceed when blockerId is resolved. VBlockedApp or VBlockedThunk
  sealed trait Blocked extends Blocker

  sealed trait UpdatableType {
    def withTpe(tpe: Value): Value
  }

  type VarId = Int

  // Identifier for lambdas to shortcut equality when possible.
  sealed trait ValueId

  object ValueId {
    final case class Const(name: String) extends ValueId {
      override def toString: String = name
    }

    final case class LocalId(nodeId: AstNodeId, captures: Vector[Value]) extends ValueId
  }

  private[raccoonlang] def envDeps(env: RuntimeEnv): DepSet = {
    val res = DepSet.newBuilder
    env.locals.foreach(_.valueOption.foreach(value => res.unionInPlace(value.synDeps)))
    res.result()
  }

  sealed trait LamBody {
    def synDeps: DepSet
  }
  object LamBody {
    final case class Core(term: ElabAst.Term.Lam, env: RuntimeEnv) extends LamBody {
      override lazy val synDeps: DepSet = envDeps(env)
    }
    final case class Native(run: (Vector[Value], EqStore) => Value) extends LamBody {
      override val synDeps: DepSet = DepSet.empty
    }
  }

  sealed trait BlockedThunkBody {
    def synDeps: DepSet
  }
  object BlockedThunkBody {
    final case class Select(base: Value, field: String, env: RuntimeEnv, locationId: AstNodeId)
      extends BlockedThunkBody {
      override lazy val synDeps: DepSet = base.synDeps ++ envDeps(env)
    }

    final case class Match(term: ElabAst.Term.Match, env: RuntimeEnv) extends BlockedThunkBody {
      override lazy val synDeps: DepSet = envDeps(env)
    }
  }

  sealed trait Universe extends Value

  case object LevelTpe extends TopLevelValue {
    override def tpe: Value = TypeTpe
  }

  case object KernelObject extends TopLevelValue {
    override def tpe: Value = KernelObject
  }

  // Represents max(var1 + k1, var2 + k2... , c)
  // Invariant: all offsets are non-negative, c is non-negative, and c is either 0 or c > k1...kn.
  final class Level private (val atoms: Map[VarId, Int], val c: Int) extends Value {
    override val tpe: Value = LevelTpe

    override val synDeps: DepSet = DepSet.from(atoms.keys)

    override def equals(obj: Any): Boolean =
      obj match {
        case other: Level => atoms == other.atoms && c == other.c
        case _            => false
      }

    override def hashCode(): Int = 31 * atoms.hashCode() + c
  }
  object Level {
    def of(atoms: Map[VarId, Int], c: Int): Level = {
      require(c >= 0, s"Level constant must be non-negative: $c")
      require(atoms.values.forall(_ >= 0), s"Level atom offsets must be non-negative: $atoms")

      val nextC =
        if (atoms.nonEmpty && c <= atoms.values.max) 0
        else c
      new Level(atoms, nextC)
    }

    def const(c: Int): Level = of(Map.empty, c)

    def addOffset(l: Level, offset: Int): Level = {
      if (offset == 0) l
      else {
        val newAtoms = l.atoms.map { case (varId, k) => (varId, k + offset) }
        val newC = if (l.c > 0 || l.atoms.isEmpty) l.c + offset else 0
        of(newAtoms, newC)
      }
    }

    /**
     * Check if Level covers offset - that is, is it safe to subtract offset from level.
     */
    def geq(l: Level, offset: Int): Boolean =
      l.atoms.values.forall(k => k >= offset) && (l.c >= offset || (l.c == 0 && l.atoms.nonEmpty))

    def succ(l: Level): Level = addOffset(l, 1)

    def max(xs: Vector[Level]): Level = {
      require(xs.nonEmpty, "Level.max requires at least one level")

      val flatAtoms = xs.flatMap(_.atoms)
      val nextAtoms = flatAtoms.foldLeft(Map.empty[VarId, Int]) { case (curMap, (varId, k)) =>
        val curK = curMap.getOrElse(varId, 0)
        curMap + (varId -> math.max(curK, k))
      }
      val cMax = xs.map(_.c).max
      val kMax = if (nextAtoms.nonEmpty) nextAtoms.values.max else 0
      val nextC = if (cMax > kMax) cMax else 0
      of(nextAtoms, nextC)
    }

    def leq(l1: Level, l2: Level): Boolean = {
      (l1.c <= l2.c || l2.atoms.values.exists(_ >= l1.c)) &&
      l1.atoms.forall { case (varId, k) => k <= l2.atoms.getOrElse(varId, -1) }
    }

    def mk(varId: VarId): Level = of(Map(varId -> 0), 0)

    val zero = const(0)
    val one = const(1)

  }

  case class VSort(level: Level) extends Universe {
    override def tpe: Value = VSort(Level.succ(level))

    override def synDeps: DepSet = level.synDeps
  }

  final val PropTpe: VSort = VSort(Level.zero)
  final val TypeTpe: VSort = VSort(Level.one)

  sealed trait CaptureType
  case object StructuralCapture extends CaptureType
  case class LevelCapture(subtract: Int) extends CaptureType

  sealed trait CaptureRoot
  case object ActualType extends CaptureRoot
  case object ActualTypeClassifier extends CaptureRoot

  case class VCapture(
      localRef: CoreAst.LocalRef,
      path: List[Int],
      captureType: CaptureType,
      root: CaptureRoot = ActualType
  )

  case class VBinder(
      localRef: CoreAst.LocalRef,
      ty: ElabAst.BinderType,
      expectedTy: ElabAst.TypeTerm,
      captures: Vector[Value.VCapture],
      isInstance: Boolean = false
  ) {
    def name: String = localRef.name
  }

  case class VPi(
      env: RuntimeEnv,
      binders: Vector[VBinder],
      codomain: (RuntimeEnv, EqStore) => Value,
      synDeps: DepSet,
      id: ValueId,
      tpe: Universe
  ) extends Value
    with UpdatableType {
    require(binders.nonEmpty, "VPi requires at least one binder")

    override def toString: String = "VPi"

    override def withTpe(tpe: Value): Value = tpe match {
      case u: Universe => this.copy(tpe = u)
      case _           => throw WTF(s"Cannot update Pi type to $tpe")
    }
  }

  case class VConst(name: String, constType: ConstType, tpe: Value) extends Value with UpdatableType {
    override val synDeps: DepSet = tpe.synDeps

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  sealed trait AppliedValue extends Value {
    def head: Value

    def args: Seq[Value]

    def tpe: Value

    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(head.synDeps)
      args.foreach(v => res.unionInPlace(v.synDeps))
      res.unionInPlace(tpe.synDeps)
      res.result()
    }
  }

  case class VApp(head: VConst, args: Vector[Value], tpe: Value) extends AppliedValue with UpdatableType {
    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  case class VBlockedApp(head: Value, args: Vector[Value], tpe: Value, blockerId: VarId)
    extends AppliedValue
    with Blocked
    with UpdatableType {
    require(args.nonEmpty, "Blocked application requires at least one argument")
    require(synDeps.contains(blockerId), "Blocked application synDeps must include blockerId")

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  case class VBlockedThunk(body: BlockedThunkBody, id: ValueId.LocalId, tpe: Value, blockerId: VarId)
    extends Blocked
    with UpdatableType {
    require(synDeps.contains(blockerId), "Blocked thunk synDeps must include blockerId")

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)

    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(body.synDeps)
      res.unionInPlace(tpe.synDeps)
      id.captures.foreach(v => res.unionInPlace(v.synDeps))
      res.result()
    }
  }

  case class Var(name: String, id: VarId, tpe: Value) extends Value with Blocker with UpdatableType {
    override val synDeps: DepSet = tpe.synDeps + id

    override val blockerId: VarId = id

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  case class VLam(
      tpe: VPi,
      id: ValueId,
      isStable: Boolean,
      body: LamBody
  ) extends Value {
    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(tpe.synDeps)
      res.unionInPlace(body.synDeps)
      id match {
        case ValueId.Const(_) => res.result()
        case ValueId.LocalId(_, params) =>
          if (params.isEmpty) res.result()
          else {
            params.foreach(v => res.unionInPlace(v.synDeps))
            res.result()
          }
      }
    }
  }

  case class ConstructorHead(name: String, numErased: Int, totalArity: Int, tpe: Value, isStruct: Boolean)
    extends TopLevelValue
    with UpdatableType {
    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  // Runtime constructor value. `fields` contains only stored fields; erased constructor binders are not retained.
  case class VCtor(head: ConstructorHead, fields: Vector[Value], tpe: Value) extends Value with UpdatableType {
    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(head.synDeps)
      fields.foreach(v => res.unionInPlace(v.synDeps))
      res.unionInPlace(tpe.synDeps)
      res.result()
    }

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  object NormalizerType extends TopLevelValue {
    override def tpe: Value = TypeTpe
  }

  trait Normalizer extends TopLevelValue {
    def carrierKey: Normalizers.CarrierKey

    def normalize(v: Value, eqStore: EqStore): Value

    def name: String

    override val tpe: Value = NormalizerType
  }

  final case class ConstructorMeta(shortName: String, canonicalName: String)

  final case class InductiveMeta(
      constructors: Vector[ConstructorMeta],
      familyArity: Int,
      isStruct: Boolean
  ) {
    lazy val constructorNames: Vector[String] = constructors.map(_.canonicalName)
  }

  sealed trait ConstType
  case class Inductive(meta: InductiveMeta) extends ConstType
  case object Symbol extends ConstType

  case class ResolvedValue(value: Value) {
    def caseOf[B](f: PartialFunction[Value, B]): B = f(value)
  }

  implicit class RichValuePair(p: (Value, Value)) {
    def caseOf[B](f: PartialFunction[(Value, Value), B])(implicit eqStore: EqStore): B =
      f((Interpreter.resolveInEqStore(p._1).value, Interpreter.resolveInEqStore(p._2).value))
  }

}
