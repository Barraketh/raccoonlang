package com.raccoonlang

// Runtime/checking environment for resolved terms. Local references are dense slots in `locals`;
// source-name scoping is handled by the elaborator before terms reach this layer.
final case class Env(
    globals: Map[String, Binding],
    locals: Vector[Binding],
    globalInstances: InstanceRegistry,
    localInstances: Map[String, Vector[InstanceCandidate]]
) {
  def apply(name: String): Value = globals.getOrElse(name, throw NotFound(name)).value

  def apply(ref: CoreAst.LocalRef): Value =
    findLocalBinding(ref).map(_.value).getOrElse(throw NotFound(s"${ref.name}#${ref.id}"))

  def find(name: String): Option[Value] = globals.get(name).map(_.value)

  def findLocalBinding(ref: CoreAst.LocalRef): Option[Binding] =
    if (ref.id >= 0 && ref.id < locals.length) Some(locals(ref.id)) else None

  def putGlobal(
      name: String,
      value: Value,
      instanceKey: Option[String] = None,
      instanceTerm: Option[CoreAst.CheckedTerm] = None
  ): Env = {
    if (globals.contains(name))
      throw AlreadyDefined(name)
    else if (name == "_") this
    else {
      val term = instanceTerm.getOrElse(CoreAst.Term.GlobalRef[CoreAst.Checked](name, Span(0, 0)))
      val nextInstances = instanceKey match {
        case Some(key) => globalInstances.add(key, name, value, term)
        case None      => globalInstances
      }
      copy(
        globals = globals + (name -> Binding(name, value)),
        globalInstances = nextInstances
      )
    }
  }

  def putLocal(
      ref: CoreAst.LocalRef,
      value: Value,
      instanceKey: Option[String] = None,
      instanceTerm: Option[CoreAst.CheckedTerm] = None
  ): Env = {
    if (ref.id == locals.length) {
      val term = instanceTerm.getOrElse(CoreAst.Term.LocalRef[CoreAst.Checked](ref, Span(0, 0)))
      val binding = Binding(ref.name, value)

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

object Env {
  val empty: Env =
    Env(
      globals = Map.empty,
      locals = Vector.empty,
      globalInstances = InstanceRegistry.empty,
      localInstances = Map.empty
    )
}

final case class Binding(
    name: String,
    value: Value
)

final case class InstanceCandidate(
    name: String,
    value: Value,
    term: CoreAst.CheckedTerm
)

final case class InstanceSearchTiers(locals: Vector[InstanceCandidate], globals: Vector[InstanceCandidate])

final case class InstanceRegistry(buckets: Map[String, Vector[InstanceCandidate]]) {
  def add(key: String, name: String, value: Value, term: CoreAst.CheckedTerm): InstanceRegistry =
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
