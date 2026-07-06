package com.raccoonlang

import scala.collection.immutable.VectorMap

object Env {
  val empty: Env =
    Env(
      globals = Map.empty,
      locals = VectorMap.empty
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
    locals: VectorMap[CoreAst.LocalRef, Value]
) {
  def apply(name: String): Value =
    globals.get(name).map(_.value(this)).getOrElse(throw NotFound(name))

  def apply(ref: CoreAst.LocalRef): Value =
    locals.getOrElse(ref, throw NotFound(ref.toString))

  def putGlobal(name: String, value: Value): Env = {
    assert(value.synDeps.isEmpty)

    if (globals.contains(name)) throw AlreadyDefined(name)
    else if (name == "_") throw WTF("Wildcards not allowed in global names")
    else copy(globals = globals + (name -> GlobalBinding.Strict(value)))
  }

  def putLazyGlobal(name: String, force: () => Value): Env = {
    if (globals.contains(name)) throw AlreadyDefined(name)
    else if (name == "_") throw WTF("Wildcards not allowed in global names")
    else copy(globals = globals + (name -> new GlobalBinding.Lazy(force)))
  }

  def putLocal(
      ref: CoreAst.LocalRef,
      value: Value
  ): Env = {
    if (locals.contains(ref)) throw WTF(s"Local ref $ref is already bound")
    else copy(locals = locals + (ref -> value))
  }

  def closeForEval(capturedRefs: Set[CoreAst.LocalRef]): Env = {
    capturedRefs.foreach { ref =>
      if (!locals.contains(ref))
        throw WTF(s"Captured local $ref is outside env")
    }

    val capturedLocals = VectorMap.from(locals.iterator.filter { case (ref, _) => capturedRefs(ref) })

    copy(locals = capturedLocals)
  }
}
