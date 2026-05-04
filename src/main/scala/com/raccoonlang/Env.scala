package com.raccoonlang

// Environment: tracks lexical scope
final case class Env(
    globals: Map[String, Value],
    locals: ScopedMap
) {
  def apply(name: String): Value = find(name).getOrElse(throw NotFound(name))

  def find(name: String): Option[Value] = locals.find(name).orElse(globals.get(name))

  def findLocal(name: String): Option[Value] = locals.find(name)

  def putGlobal(name: String, value: Value): Env = {
    if (globals.contains(name))
      throw AlreadyDefined(name)
    else if (name == "_") this
    else copy(globals = globals + (name -> value))
  }

  def putLocal(name: String, value: Value): Env = {
    if (globals.contains(name))
      throw AlreadyDefined(name)
    if (name == "_") this
    else copy(locals = locals.put(name, value))
  }

  def newScope: Env = copy(locals = locals.newScope)
}

object Env {
  val empty: Env = Env(globals = Map(), locals = ScopedMap.empty)
}

case class ScopedMap(map: Map[String, Value], parent: Option[ScopedMap]) {
  def find(name: String): Option[Value] = map.get(name).orElse(parent.flatMap(_.find(name)))

  def put(name: String, value: Value): ScopedMap = {
    if (map.contains(name))
      throw AlreadyDefined(name)
    ScopedMap(map + (name -> value), parent)
  }

  def newScope: ScopedMap = ScopedMap(Map.empty, Some(this))
}

object ScopedMap {
  val empty: ScopedMap = ScopedMap(Map.empty, None)
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
