package com.raccoonlang

import scala.collection.immutable.VectorMap

object Env {
  val empty: Env =
    Env(
      globals = Map.empty,
      locals = VectorMap.empty,
      nativeLiterals = NativeLiteralState.empty
    )

  // Internal-invariant assertions run on every env bind — the hottest path in the system — and
  // force synDeps/type computations. They are optional per the trust model; disable for
  // benchmarking with -Draccoon.envAssertions=false.
  private val assertionsEnabled: Boolean =
    java.lang.Boolean.parseBoolean(System.getProperty("raccoon.envAssertions", "true"))

  private[raccoonlang] def assertClosedGlobal(value: Value): Unit =
    if (assertionsEnabled && value.synDeps.nonEmpty)
      throw WTF(s"Global value must be closed, but has free vars ${value.synDeps}")

  // Proof-representation invariant (proof-collapse.md): every value of known-propositional type
  // is a fixed point of canonicalizeProof. This includes reconstructed constructors as well as
  // the helper's explicit exemptions. Every value enters an env through putLocal/putGlobal, so a
  // missed representation step fails loudly here.
  private[raccoonlang] def assertCanonicalProof(value: Value): Unit =
    if (assertionsEnabled && !(Value.canonicalizeProof(value) eq value))
      throw WTF(s"Non-canonical proof bound into env: value ${value} of type ${value.tpe}")
}

final case class NativeLiteralState private[raccoonlang] (
    natLayout: Option[Value.ValidatedNatLayout],
    stringLayout: Option[Value.ValidatedStringLayout]
)

object NativeLiteralState {
  private[raccoonlang] val empty: NativeLiteralState = NativeLiteralState(None, None)
}

sealed trait GlobalBinding {
  def value(env: Env): Value
  def projectionAlias: Option[CoreAst.ProjectionAlias]
}

object GlobalBinding {
  final case class Strict(value0: Value, projectionAlias: Option[CoreAst.ProjectionAlias]) extends GlobalBinding {
    override def value(env: Env): Value = value0
  }

  final class Lazy(force: () => Value) extends GlobalBinding {
    private[this] var cached: Option[Value] = None

    override val projectionAlias: Option[CoreAst.ProjectionAlias] = None

    override def value(env: Env): Value =
      cached match {
        case Some(value) => value
        case None =>
          val value = force()
          Env.assertClosedGlobal(value)
          Env.assertCanonicalProof(value)
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
    nativeLiterals: NativeLiteralState
) {
  def apply(name: String): Value =
    globals.get(name).map(_.value(this)).getOrElse(throw NotFound(name))

  def apply(ref: CoreAst.LocalRef): Value =
    locals.getOrElse(ref, throw NotFound(ref.toString))

  // Field notation reads this metadata without forcing the selector definition.
  def projectionAlias(name: String): Option[CoreAst.ProjectionAlias] =
    globals.get(name).flatMap(_.projectionAlias)

  def putGlobal(
      name: String,
      value: Value,
      projectionAlias: Option[CoreAst.ProjectionAlias] = None
  ): Env = {
    Env.assertClosedGlobal(value)
    Env.assertCanonicalProof(value)

    if (globals.contains(name)) throw AlreadyDefined(name)
    else if (name == "_") throw WTF("Wildcards not allowed in global names")
    else copy(globals = globals + (name -> GlobalBinding.Strict(value, projectionAlias)))
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
    Env.assertCanonicalProof(value)
    if (locals.contains(ref)) throw WTF(s"Local ref $ref is already bound")
    else copy(locals = locals + (ref -> value))
  }

  /**
   * Temporary constructor-instantiation environment used only by declaration-certified proof reconstruction. Stored
   * proof fields are intentionally reconstructed one layer at a time and may therefore be raw `VProof` s here.
   */
  private[raccoonlang] def putLocalUnchecked(ref: CoreAst.LocalRef, value: Value): Env = {
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

  private[raccoonlang] def installStringLayout(layout: Value.ValidatedStringLayout): Env =
    nativeLiterals.stringLayout match {
      case Some(_) => throw WTF("Validated String layout is already installed")
      case None    => copy(nativeLiterals = nativeLiterals.copy(stringLayout = Some(layout)))
    }

  private[raccoonlang] def installNatLayout(layout: Value.ValidatedNatLayout): Env =
    nativeLiterals.natLayout match {
      case Some(_) => throw WTF("Validated Nat layout is already installed")
      case None    => copy(nativeLiterals = nativeLiterals.copy(natLayout = Some(layout)))
    }
}
