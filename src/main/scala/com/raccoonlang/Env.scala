package com.raccoonlang

import scala.collection.immutable.VectorMap

object Env {
  val empty: Env =
    Env(
      globals = Map.empty,
      locals = VectorMap.empty
    )

  // Internal-invariant assertions run on every env bind — the hottest path in the system — and
  // force synDeps/type computations. They are optional per the trust model; disable for
  // benchmarking with -Draccoon.envAssertions=false.
  private val assertionsEnabled: Boolean =
    java.lang.Boolean.parseBoolean(System.getProperty("raccoon.envAssertions", "true"))

  private[raccoonlang] def assertClosedGlobal(value: Value): Unit =
    if (assertionsEnabled && value.synDeps.nonEmpty)
      throw WTF(s"Global value must be closed, but has free vars ${value.synDeps}")

  // Collapse invariant (A), proof-collapse.md §3: every value of known-propositional type is a
  // VProof. Stated as "the value is a fixed point of collapseIfProof" so the exemption list
  // (refinable Vars, constructor heads, the raw-recursive self lambda) lives only in the collapse
  // helper itself. Every value enters an env through putLocal/putGlobal, so a missed collapse
  // site fails loudly here instead of silently re-enabling structured-proof reads downstream.
  private[raccoonlang] def assertCollapsed(value: Value): Unit =
    if (assertionsEnabled && !(Value.collapseIfProof(value) eq value))
      throw WTF(s"Uncollapsed proof bound into env: value ${value} of type ${value.tpe}")
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
          Env.assertClosedGlobal(value)
          Env.assertCollapsed(value)
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
    Env.assertClosedGlobal(value)
    Env.assertCollapsed(value)

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
    Env.assertCollapsed(value)
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
