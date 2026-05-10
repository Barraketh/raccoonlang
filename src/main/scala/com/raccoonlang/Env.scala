package com.raccoonlang

import org.roaringbitmap.RoaringBitmap

// Shared lookup/update surface for environments. Values close over RuntimeEnv;
// instance search takes TypecheckEnv explicitly so runtime closures cannot carry
// local instance search state.
trait EnvLike[E <: EnvLike[E]] {
  def globals: Map[String, Binding]
  def locals: Vector[Binding]

  def apply(name: String): Value = globals.getOrElse(name, throw NotFound(name)).value

  def find(name: String): Option[Value] = globals.get(name).map(_.value)

  def apply(ref: CoreAst.LocalRef): Value =
    findLocalBinding(ref).map(_.value).getOrElse(throw NotFound(s"${ref.name}#${ref.id}"))

  def findLocalBinding(ref: CoreAst.LocalRef): Option[Binding] =
    if (ref.id >= 0 && ref.id < locals.length) Some(locals(ref.id)) else None

  def getLocalsByIndexes(indexes: RoaringBitmap): Vector[Value] = {
    val values = Vector.newBuilder[Value]
    val limit = locals.length
    val it = indexes.getIntIterator
    while (it.hasNext) {
      val id = it.next()
      if (id < limit) values += locals(id).value
      else throw WTF(s"Captured local index #$id is outside env with $limit locals")
    }
    values.result()
  }

  lazy val allDeps: DepSet = {
    val res = DepSet.newBuilder
    locals.foreach(b => b.foreach(v => res.unionInPlace(v.synDeps)))
    res.result()
  }

  def putGlobal(
      name: String,
      value: Value,
      instanceKey: Option[String] = None,
      instanceTerm: Option[ElabAst.Term] = None
  ): E

  def putLocal(
      ref: CoreAst.LocalRef,
      value: Value,
      instanceKey: Option[String] = None,
      instanceTerm: Option[ElabAst.Term] = None
  ): E

  def closeForEval(capturedIndexes: Option[RoaringBitmap] = None): RuntimeEnv =
    RuntimeEnv(
      globals,
      locals.zipWithIndex.map { case (binding, idx) =>
        if (capturedIndexes.exists(_.contains(idx))) binding else Binding.pruned(binding.name)
      }
    )
}

final case class RuntimeEnv(
    globals: Map[String, Binding],
    locals: Vector[Binding]
) extends EnvLike[RuntimeEnv] {
  override def putGlobal(
      name: String,
      value: Value,
      instanceKey: Option[String] = None,
      instanceTerm: Option[ElabAst.Term] = None
  ): RuntimeEnv = {
    if (globals.contains(name))
      throw AlreadyDefined(name)
    else if (name == "_") this
    else copy(globals = globals + (name -> Binding.live(name, value)))
  }

  override def putLocal(
      ref: CoreAst.LocalRef,
      value: Value,
      instanceKey: Option[String] = None,
      instanceTerm: Option[ElabAst.Term] = None
  ): RuntimeEnv = {
    if (ref.id == locals.length) copy(locals = locals :+ Binding.live(ref.name, value))
    else if (ref.id < locals.length)
      throw WTF(s"Local ref ${ref.name}#${ref.id} is already bound; env has ${locals.length} slots")
    else throw WTF(s"Non-dense local ref ${ref.name}#${ref.id}; env has ${locals.length} slots")
  }
}

// Runtime/checking environment for resolved terms. Local references are dense slots in `locals`;
// source-name scoping is handled by the elaborator before terms reach this layer.
final case class TypecheckEnv(
    globals: Map[String, Binding],
    locals: Vector[Binding],
    globalInstances: InstanceRegistry,
    localInstances: Map[String, Vector[InstanceCandidate]]
) extends EnvLike[TypecheckEnv] {
  override def putGlobal(
      name: String,
      value: Value,
      instanceKey: Option[String] = None,
      instanceTerm: Option[ElabAst.Term] = None
  ): TypecheckEnv = {
    if (globals.contains(name))
      throw AlreadyDefined(name)
    else if (name == "_") this
    else {
      val term = instanceTerm.getOrElse(ElabAst.Term.GlobalRef(name, Span(0, 0)))
      val nextInstances = instanceKey match {
        case Some(key) => globalInstances.add(key, name, value, term)
        case None      => globalInstances
      }
      copy(
        globals = globals + (name -> Binding.live(name, value)),
        globalInstances = nextInstances
      )
    }
  }

  override def putLocal(
      ref: CoreAst.LocalRef,
      value: Value,
      instanceKey: Option[String] = None,
      instanceTerm: Option[ElabAst.Term] = None
  ): TypecheckEnv = {
    if (ref.id == locals.length) {
      val term = instanceTerm.getOrElse(ElabAst.Term.LocalRef(ref, Span(0, 0)))
      val binding = Binding.live(ref.name, value)

      val nextLocalInstances = instanceKey match {
        case Some(key) =>
          val candidate = InstanceCandidate(ref.name, value, term)
          localInstances + (key -> (candidate +: localInstances.getOrElse(key, Vector.empty)))
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

  def instanceSearchTiers(key: String): InstanceSearchTiers =
    InstanceSearchTiers(
      localInstances.getOrElse(key, Vector.empty),
      globalInstances.get(key)
    )

}

object TypecheckEnv {
  val empty: TypecheckEnv =
    TypecheckEnv(
      globals = Map.empty,
      locals = Vector.empty,
      globalInstances = InstanceRegistry.empty,
      localInstances = Map.empty
    )
}

final case class Binding(
    name: String,
    state: Binding.State
) {
  def value: Value =
    state match {
      case Binding.Live(value) => value
      case Binding.Pruned      => throw WTF(s"Accessed pruned local $name")
    }

  def valueOption: Option[Value] =
    state match {
      case Binding.Live(value) => Some(value)
      case Binding.Pruned      => None
    }

  def mapValue(f: Value => Value): Binding =
    state match {
      case Binding.Live(value) => Binding.live(name, f(value))
      case Binding.Pruned      => this
    }

  def foreach(f: Value => Unit): Unit = state match {
    case Binding.Live(value) => f(value)
    case _                   =>
  }
}

object Binding {
  sealed trait State
  final case class Live(value: Value) extends State
  case object Pruned extends State

  def live(name: String, value: Value): Binding = Binding(name, Live(value))

  def pruned(name: String): Binding = Binding(name, Pruned)
}

final case class InstanceCandidate(
    name: String,
    value: Value,
    term: ElabAst.Term
)

final case class InstanceSearchTiers(locals: Vector[InstanceCandidate], globals: Vector[InstanceCandidate])

final case class InstanceRegistry(buckets: Map[String, Vector[InstanceCandidate]]) {
  def add(key: String, name: String, value: Value, term: ElabAst.Term): InstanceRegistry =
    copy(buckets = buckets + (key -> (buckets.getOrElse(key, Vector.empty) :+ InstanceCandidate(name, value, term))))

  def get(key: String): Vector[InstanceCandidate] = buckets.getOrElse(key, Vector.empty)
}

object InstanceRegistry {
  val empty: InstanceRegistry = InstanceRegistry(Map.empty)
}

// Probably should live in Env, but I'll keep it separate for now
case class NormalizerMap(map: Map[Normalizers.CarrierKey, Value.Normalizer]) {
  def use(n: Value.Normalizer): NormalizerMap = {
    if (map.contains(n.carrierKey)) throw DuplicateNormalizer(n.carrierKey)

    NormalizerMap(map + (n.carrierKey -> n))
  }

  def get(key: Normalizers.CarrierKey): Option[Value.Normalizer] = map.get(key)
}

object NormalizerMap {
  val empty = NormalizerMap(Map.empty)
}
