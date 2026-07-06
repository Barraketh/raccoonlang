package com.raccoonlang

final case class Instances(
    globals: InstanceRegistry,
    locals: Map[String, Vector[CoreAst.LocalRef]]
) {
  def addGlobal(key: String, value: Value): Instances = {
    assert(value.synDeps.isEmpty)
    copy(globals = globals.add(key, value))
  }

  def putGlobal(name: String, value: Value): Instances =
    addGlobal(InstanceSearch.instanceKey(name, value), value)

  def addLocal(key: String, ref: CoreAst.LocalRef): Instances =
    copy(locals = locals + (key -> (ref +: locals.getOrElse(key, Vector.empty))))

  def putLocal(ref: CoreAst.LocalRef, value: Value): Instances =
    addLocal(InstanceSearch.instanceKey(ref.name, value), ref)

  def searchTiers(key: String, env: Env[Value]): InstanceSearchTiers =
    InstanceSearchTiers(
      locals.getOrElse(key, Vector.empty).map(env.locals),
      globals.get(key)
    )
}

object Instances {
  val empty: Instances = Instances(InstanceRegistry.empty, Map.empty)
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
