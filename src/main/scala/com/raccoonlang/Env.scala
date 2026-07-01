package com.raccoonlang

import scala.collection.immutable.VectorMap

object Env {
  val empty: Env =
    Env(
      globals = Map.empty,
      locals = VectorMap.empty,
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

// Runtime/checking environment for resolved terms. Source-name scoping is handled by the elaborator before terms
// reach this layer; local lookup uses the resolved LocalRef as the map key.
final case class Env(
    globals: Map[String, GlobalBinding],
    locals: VectorMap[CoreAst.LocalRef, Value],
    globalInstances: InstanceRegistry,
    localInstances: Map[String, Vector[CoreAst.LocalRef]]
) {
  def apply(name: String): Value =
    globals.get(name).map(_.value(this)).getOrElse(throw NotFound(name))

  def apply(ref: CoreAst.LocalRef): Value =
    locals.getOrElse(ref, throw NotFound(ref.toString))

  def putGlobal(name: String, value: Value, instanceKey: Option[String] = None): Env = {
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

  def putLazyGlobal(name: String, force: () => Value): Env = {
    if (globals.contains(name)) throw AlreadyDefined(name)
    else if (name == "_") throw WTF("Wildcards not allowed in global names")
    else copy(globals = globals + (name -> new GlobalBinding.Lazy(force)))
  }

  def putLocal(
      ref: CoreAst.LocalRef,
      value: Value,
      instanceKey: Option[String] = None
  ): Env = {
    if (locals.contains(ref)) throw WTF(s"Local ref $ref is already bound")
    else {
      val nextLocalInstances = instanceKey match {
        case Some(key) =>
          localInstances + (key -> (ref +: localInstances.getOrElse(key, Vector.empty)))
        case None => localInstances
      }

      copy(
        locals = locals + (ref -> value),
        localInstances = nextLocalInstances
      )
    }
  }

  def instanceSearchTiers(key: String): InstanceSearchTiers =
    InstanceSearchTiers(
      localInstances.getOrElse(key, Vector.empty).flatMap(locals.get),
      globalInstances.get(key)
    )

  def closeForEval(capturedRefs: Set[CoreAst.LocalRef]): Env = {
    capturedRefs.foreach { ref =>
      if (!locals.contains(ref))
        throw WTF(s"Captured local $ref is outside env")
    }

    val capturedLocals = VectorMap.from(locals.iterator.filter { case (ref, _) => capturedRefs(ref) })
    val capturedLocalInstances =
      localInstances.iterator
        .map { case (key, refs) => key -> refs.filter(capturedRefs) }
        .filter { case (_, refs) => refs.nonEmpty }
        .toMap

    copy(
      locals = capturedLocals,
      localInstances = capturedLocalInstances
    )
  }
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
