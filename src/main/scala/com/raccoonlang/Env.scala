package com.raccoonlang

import org.roaringbitmap.RoaringBitmap

import scala.collection.immutable.BitSet

trait Env {
  def locals: Vector[Binding]

  def apply(name: String): Value

  def apply(ref: CoreAst.LocalRef): Value = localBinding(ref).value

  lazy val allDeps: DepSet = {
    val res = DepSet.newBuilder
    locals.foreach(b => b.foreach(v => res.unionInPlace(v.synDeps)))
    res.result()
  }

  def putGlobal(name: String, value: Value, instanceKey: Option[String] = None): Env

  def putLazyGlobal(name: String, force: () => Value): Env

  /**
   * Bind the next local slot. `linear` records that the checker tracks the local (`Binding.linear`); only the checker's
   * binder sites set it, so evaluation never decides linearity. A tracked local's provenance is `alias`, for a `let` or
   * a match field, or, when there is none, the local itself as a root, for a parameter.
   */
  def putLocal(
      ref: CoreAst.LocalRef,
      value: Value,
      instanceKey: Option[String] = None,
      residualPolicy: LocalResidualPolicy = LocalResidualPolicy.Residualizable,
      linear: Boolean = false,
      alias: Option[Ledger.Provenance] = None
  ): Env

  /**
   * The tracked locals consumed on the checker's path to this point, which a tracked binding put here records as its
   * `deadBefore`. The checker adds a term's uses after checking it, before the next lets, arguments or branches.
   */
  def deadLocals: BitSet

  /** This environment with `ids` consumed as well. */
  def withDeadLocals(ids: BitSet): Env

  def localInstanceRefs(key: String): Vector[CoreAst.LocalRef]

  def globalInstanceValues(key: String): Vector[Value]

  def instanceSearchTiers(key: String): InstanceSearchTiers =
    InstanceSearchTiers(
      localInstanceRefs(key).map(ref => localBinding(ref).value),
      globalInstanceValues(key)
    )

  def localBinding(ref: CoreAst.LocalRef): Binding
}

object Env {
  val empty: Env =
    TypecheckEnv(
      globals = Map.empty,
      locals = Vector.empty,
      globalInstances = InstanceRegistry.empty,
      localInstances = Map.empty
    )
}

sealed trait GlobalBinding {
  def value(env: Env): Value
}

object GlobalBinding {
  final case class Strict(value0: Value) extends GlobalBinding {
    override def value(env: Env): Value = value0
  }

  final class Lazy(force: () => Value) extends GlobalBinding {
    private[this] var cached: Option[Value] = None

    override def value(env: Env): Value =
      cached match {
        case Some(value) => value
        case None =>
          val value = force()
          assert(value.synDeps.isEmpty)
          cached = Some(value)
          value
      }
  }
}

// Runtime/checking environment for resolved terms. Local references are dense slots in `locals`;
// source-name scoping is handled by the elaborator before terms reach this layer.
final case class TypecheckEnv(
    globals: Map[String, GlobalBinding],
    locals: Vector[Binding],
    globalInstances: InstanceRegistry,
    localInstances: Map[String, Vector[CoreAst.LocalRef]],
    deadLocals: BitSet = BitSet.empty
) extends Env {
  override def withDeadLocals(ids: BitSet): Env =
    if (ids.subsetOf(deadLocals)) this else copy(deadLocals = deadLocals | ids)

  override def apply(name: String): Value =
    globals.get(name).map(_.value(this)).getOrElse(throw NotFound(name))

  override def putGlobal(name: String, value: Value, instanceKey: Option[String]): Env = {
    assert(value.synDeps.isEmpty)

    if (globals.contains(name)) throw AlreadyDefined(name)
    else if (name == "_") throw WTF("Wildcards not allowed in global names")
    else {
      val nextInstances = instanceKey match {
        case Some(key) => globalInstances.add(key, value)
        case None      => globalInstances
      }
      copy(
        globals = globals + (name -> GlobalBinding.Strict(value)),
        globalInstances = nextInstances
      )
    }
  }

  override def putLazyGlobal(name: String, force: () => Value): Env = {
    if (globals.contains(name)) throw AlreadyDefined(name)
    else if (name == "_") throw WTF("Wildcards not allowed in global names")
    else copy(globals = globals + (name -> new GlobalBinding.Lazy(force)))
  }

  override def putLocal(
      ref: CoreAst.LocalRef,
      value: Value,
      instanceKey: Option[String],
      residualPolicy: LocalResidualPolicy,
      linear: Boolean,
      alias: Option[Ledger.Provenance]
  ): Env = {
    if (ref.id == locals.length) {
      // Only a root records what was dead when it was bound: joint liveness is decided on roots.
      val binding = (linear, alias) match {
        case (false, _) => Binding.live(ref, value, residualPolicy, linear, BitSet.empty, Ledger.Provenance.empty)
        case (true, Some(provenance)) => Binding.live(ref, value, residualPolicy, linear, BitSet.empty, provenance)
        case (true, None) =>
          Binding.live(ref, value, residualPolicy, linear, deadLocals, Ledger.Provenance.root(ref.id))
      }
      val nextLocalInstances = instanceKey match {
        case Some(key) =>
          localInstances + (key -> (ref +: localInstances.getOrElse(key, Vector.empty)))
        case None => localInstances
      }

      copy(
        locals = locals :+ binding,
        localInstances = nextLocalInstances
      )
    } else if (ref.id < locals.length)
      throw WTF(s"Local ref ${ref.name}#${ref.id} is already bound; env has ${locals.length} slots")
    else throw WTF(s"Non-dense local ref ${ref.name}#${ref.id}; env has ${locals.length} slots")
  }

  override def localInstanceRefs(key: String): Vector[CoreAst.LocalRef] =
    localInstances.getOrElse(key, Vector.empty)

  override def globalInstanceValues(key: String): Vector[Value] =
    globalInstances.get(key)

  override def localBinding(ref: CoreAst.LocalRef): Binding = {
    if (ref.id >= 0 && ref.id < locals.length) locals(ref.id)
    else throw NotFound(s"${ref.name}#${ref.id}")
  }
}

// Our wrappers will mostly deal with how we handle locals, in particular overwriting 'localBinding'
// This trait delegates all other functions to base
trait DelegatingEnv extends Env {
  def base: Env
  def updateBase(newBase: Env): Env

  override def apply(name: String): Value = base.apply(name)
  override def localInstanceRefs(key: String): Vector[CoreAst.LocalRef] = base.localInstanceRefs(key)
  override def globalInstanceValues(key: String): Vector[Value] = base.globalInstanceValues(key)

  override def putGlobal(name: String, value: Value, instanceKey: Option[String]): Env =
    updateBase(base.putGlobal(name, value, instanceKey))
  override def putLazyGlobal(name: String, force: () => Value): Env =
    updateBase(base.putLazyGlobal(name, force))
  override def putLocal(
      ref: CoreAst.LocalRef,
      value: Value,
      instanceKey: Option[String],
      residualPolicy: LocalResidualPolicy,
      linear: Boolean,
      alias: Option[Ledger.Provenance]
  ): Env =
    updateBase(base.putLocal(ref, value, instanceKey, residualPolicy, linear, alias))

  // A wrapper maps or prunes values but keeps every binding's `linear` flag and `deadBefore`.
  override def deadLocals: BitSet = base.deadLocals
  override def withDeadLocals(ids: BitSet): Env = updateBase(base.withDeadLocals(ids))

  override lazy val locals: Vector[Binding] = base.locals.map(b => localBinding(b.ref))
}

final case class RuntimeEnv(base: Env, prunedIndexes: RoaringBitmap) extends DelegatingEnv {
  override def updateBase(newBase: Env): Env = copy(base = newBase)

  override def localBinding(ref: CoreAst.LocalRef): Binding = {
    val baseLocal = base.localBinding(ref)
    if (prunedIndexes.contains(ref.id)) baseLocal.prune else baseLocal
  }
}

object RuntimeEnv {
  def closeForEval(env: Env): RuntimeEnv =
    closeForEval(env, new RoaringBitmap)

  def closeForEval(env: Env, capturedIndexes: RoaringBitmap): RuntimeEnv = {
    val it = capturedIndexes.getIntIterator
    while (it.hasNext) {
      val id = it.next()
      if (id < 0 || id >= env.locals.length)
        throw WTF(s"Captured local index #$id is outside env with ${env.locals.length} locals")
    }

    val pruned = new RoaringBitmap
    var idx = 0
    while (idx < env.locals.length) {
      if (!capturedIndexes.contains(idx)) pruned.add(idx)
      idx += 1
    }
    RuntimeEnv(env, pruned)
  }
}

sealed trait LocalResidualPolicy
object LocalResidualPolicy {
  case object Residualizable extends LocalResidualPolicy
  final case class AppHeadOnly(name: String) extends LocalResidualPolicy
}

/**
 * One local slot. `linear` is whether the checker tracks the local: a binder of linear type (docs/kernel.md, "Linear
 * types") sets it once, from the type at the binder, and mapping or pruning the value keeps it, so refinement never
 * changes it. In a checking environment every local of linear type is tracked: the checker's binders of parameters,
 * lets and fields set it, every other local it binds is a type-pattern capture, which L7 keeps unrestricted, or a
 * recursive self, and refinement never gives an unrestricted type a linear one.
 *
 * `deadBefore`, for a root, is the roots already consumed on the path when it was bound; joint liveness of reads tests
 * it (`Ledger.jointlyLive`). `provenance`, for a tracked local, is the regions its value is built from
 * (`Ledger.Provenance`): the local itself for a root, its value's for a `let`, and a region of its scrutinee for a
 * match field.
 */
final case class Binding(
    ref: CoreAst.LocalRef,
    state: Binding.State,
    residualPolicy: LocalResidualPolicy,
    linear: Boolean,
    deadBefore: BitSet,
    provenance: Ledger.Provenance
) {
  def id: Int = ref.id
  def name: String = ref.name

  def value: Value =
    state match {
      case Binding.Live(value) => value
      case Binding.Pruned      => throw WTF(s"Reading pruned local $name#$id")
    }

  def valueOption: Option[Value] =
    state match {
      case Binding.Live(value) => Some(value)
      case Binding.Pruned      => None
    }

  def mapValue(f: Value => Value): Binding =
    state match {
      case Binding.Live(value) => copy(state = Binding.Live(f(value)))
      case Binding.Pruned      => this
    }

  def foreach(f: Value => Unit): Unit = state match {
    case Binding.Live(value) => f(value)
    case _                   =>
  }

  def prune: Binding = copy(state = Binding.Pruned)
}

object Binding {
  sealed trait State
  final case class Live(value: Value) extends State
  case object Pruned extends State

  def live(
      ref: CoreAst.LocalRef,
      value: Value,
      residualPolicy: LocalResidualPolicy,
      linear: Boolean,
      deadBefore: BitSet,
      provenance: Ledger.Provenance
  ): Binding =
    Binding(ref, Live(value), residualPolicy, linear, deadBefore, provenance)
}

final case class InstanceSearchTiers(locals: Vector[Value], globals: Vector[Value])

final case class InstanceRegistry(buckets: Map[String, Vector[Value]]) {
  def add(key: String, value: Value): InstanceRegistry =
    copy(buckets = buckets + (key -> (buckets.getOrElse(key, Vector.empty) :+ value)))

  def get(key: String): Vector[Value] = buckets.getOrElse(key, Vector.empty)
}

object InstanceRegistry {
  val empty: InstanceRegistry = InstanceRegistry(Map.empty)
}
