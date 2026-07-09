package com.raccoonlang

import scala.collection.immutable.VectorMap

object Env {
  def empty[V]: Env[V] =
    Env(
      globals = Map.empty,
      locals = VectorMap.empty
    )

  private[raccoonlang] def assertClosedGlobal(value: Any): Unit =
    value match {
      case value: Value =>
        if (value.synDeps.nonEmpty)
          throw WTF(s"Global value must be closed, but has free vars ${value.synDeps}")
      case _ =>
    }

  // Collapse invariant (A), proof-collapse.md §3: every value of known-propositional type is a
  // VProof. Stated as "the value is a fixed point of collapseIfProof" so the exemption list
  // (refinable Vars, constructor heads, the raw-recursive self lambda) lives only in the collapse
  // helper itself. Every value enters an env through putLocal/putGlobal, so a missed collapse
  // site fails loudly here instead of silently re-enabling structured-proof reads downstream.
  private[raccoonlang] def assertCollapsed(value: Any): Unit =
    value match {
      case value: Value =>
        if (!(Value.collapseIfProof(value) eq value))
          throw WTF(s"Uncollapsed proof bound into env: value ${value} of type ${value.tpe}")
      case _ =>
    }
}

sealed trait GlobalBinding[V] {
  def value(env: Env[V]): V
}

object GlobalBinding {
  final case class Strict[V](value0: V) extends GlobalBinding[V] {
    override def value(env: Env[V]): V = value0
  }

  final class Lazy[V](force: () => V) extends GlobalBinding[V] {
    private[this] var cached: Option[V] = None

    override def value(env: Env[V]): V =
      cached match {
        case Some(value) => value
        case None =>
          val value = force()
          Env.assertClosedGlobal(value)
          Env.assertCollapsed(value)
          cached = Some(value)
          value
      }
  }
}

// Runtime/checking environment for resolved terms. Source-name scoping is handled by the elaborator before terms
// reach this layer; local lookup uses the resolved LocalRef as the map key.
final case class Env[V](
    globals: Map[String, GlobalBinding[V]],
    locals: VectorMap[CoreAst.LocalRef, V]
) {
  def apply(name: String): V =
    globals.get(name).map(_.value(this)).getOrElse(throw NotFound(name))

  def apply(ref: CoreAst.LocalRef): V =
    locals.getOrElse(ref, throw NotFound(ref.toString))

  def putGlobal(name: String, value: V): Env[V] = {
    Env.assertClosedGlobal(value)
    Env.assertCollapsed(value)

    if (globals.contains(name)) throw AlreadyDefined(name)
    else if (name == "_") throw WTF("Wildcards not allowed in global names")
    else copy(globals = globals + (name -> GlobalBinding.Strict(value)))
  }

  def putLazyGlobal(name: String, force: () => V): Env[V] = {
    if (globals.contains(name)) throw AlreadyDefined(name)
    else if (name == "_") throw WTF("Wildcards not allowed in global names")
    else copy(globals = globals + (name -> new GlobalBinding.Lazy(force)))
  }

  def putLocal(
      ref: CoreAst.LocalRef,
      value: V
  ): Env[V] = {
    Env.assertCollapsed(value)
    if (locals.contains(ref)) throw WTF(s"Local ref $ref is already bound")
    else copy(locals = locals + (ref -> value))
  }

  def closeForEval(capturedRefs: Set[CoreAst.LocalRef]): Env[V] = {
    capturedRefs.foreach { ref =>
      if (!locals.contains(ref))
        throw WTF(s"Captured local $ref is outside env")
    }

    val capturedLocals = VectorMap.from(locals.iterator.filter { case (ref, _) => capturedRefs(ref) })

    copy(locals = capturedLocals)
  }
}
