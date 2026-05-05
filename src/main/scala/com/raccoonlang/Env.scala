package com.raccoonlang

// Runtime/checking environment for resolved CoreAst terms. Local references are dense slots in `locals`;
// source-name scoping is handled by the elaborator before terms reach this layer.
final case class Env(
    globals: Map[String, Value],
    locals: Vector[Value]
) {
  def apply(name: String): Value = globals.getOrElse(name, throw NotFound(name))

  def apply(ref: CoreAst.LocalRef): Value = locals(ref.id)

  def find(name: String): Option[Value] = globals.get(name)

  def putGlobal(name: String, value: Value): Env = {
    if (globals.contains(name))
      throw AlreadyDefined(name)
    else if (name == "_") this
    else copy(globals = globals + (name -> value))
  }

  def putLocal(ref: CoreAst.LocalRef, value: Value): Env = {
    if (ref.id == locals.length) copy(locals = locals :+ value)
    else if (ref.id < locals.length)
      throw WTF(s"Local ref ${ref.name}#${ref.id} is already bound; env has ${locals.length} slots")
    else throw WTF(s"Non-dense local ref ${ref.name}#${ref.id}; env has ${locals.length} slots")
  }

  def newScope: Env = this
}

object Env {
  val empty: Env = Env(globals = Map(), locals = Vector.empty)
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
