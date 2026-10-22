package com.raccoonlang

import scala.collection.immutable.SeqMap

object Env {
  // One or two active groups are common and stay on the direct slot path. Beyond this depth, reads and membership use
  // the cumulative runtime lookup index, while ordered iteration remains lazy.
  private val directSlotLookupDepth = 4

  val empty: Env =
    Env(
      globals = Map.empty,
      baseLocals = SeqMap.empty,
      nativeLiterals = NativeLiteralState.empty,
      equality = Left("no prelude has finished loading"),
      sealedMembers = Map.empty,
      runtimeLocals = SeqMap.empty,
      runtimeFrames = Vector.empty,
      runtimeOrder = Vector.empty
    )

  // Internal-invariant assertions run on every env bind — the hottest path in the system — and
  // force synDeps/type computations. They are optional per the trust model; disable for
  // benchmarking with -Draccoon.envAssertions=false.
  private val assertionsEnabled: Boolean =
    java.lang.Boolean.parseBoolean(System.getProperty("raccoon.envAssertions", "true"))

  // Global values must not retain unresolved local variables.
  private[raccoonlang] def assertClosedGlobal(value: Value): Unit =
    if (assertionsEnabled && value.synDeps.nonEmpty)
      wtf(s"Global value must be closed, but has free vars ${value.synDeps}")

  // Proof-representation invariant (docs/kernel.md#proofs-and-elimination): every value of known-propositional type
  // is a fixed point of canonicalizeProof. This includes reconstructed constructors as well as
  // the helper's explicit exemptions. Every value enters an env through putLocal/putGlobal, so a
  // missed representation step fails loudly here.
  private[raccoonlang] def assertCanonicalProof(value: Value): Unit =
    if (assertionsEnabled && !(Value.canonicalizeProof(value) eq value))
      wtf(s"Non-canonical proof bound into env: value ${value} of type ${value.tpe}")
}

final case class NativeLiteralState private[raccoonlang] (
    natLayout: Option[Packed.ValidatedNatLayout],
    stringLayout: Option[Value.ValidatedStringLayout]
)

object NativeLiteralState {
  private[raccoonlang] val empty: NativeLiteralState = NativeLiteralState(None, None)
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
          Env.assertCanonicalProof(value)
          cached = Some(value)
          value
      }
  }

}

// Runtime/checking environment for resolved terms. Source-name scoping is handled by the elaborator before terms
// reach this layer; local lookup uses the resolved LocalRef as the map key.
//
// `sealedMembers` is checker-only too: each constructor and selector of a sealed family, by global name, with its
// family's seal, which the checker consults where a global name is resolved (Sealing).
//
// `equality` is the trusted prelude's `Eq`, validated at the end of prelude loading, which a match's equation is
// stated with, or why there is none (MatchEquation).
final case class Env(
    globals: Map[String, GlobalBinding],
    private[raccoonlang] val baseLocals: SeqMap[CoreAst.LocalRef, Value],
    nativeLiterals: NativeLiteralState,
    equality: Either[String, MatchEquation.ValidatedEquality],
    private[raccoonlang] val sealedMembers: Map[String, Sealing.Seal],
    private[raccoonlang] val runtimeLocals: SeqMap[CoreAst.LocalRef, Value] = SeqMap.empty,
    private[raccoonlang] val runtimeFrames: Vector[RuntimeSlotFrame] = Vector.empty,
    private[raccoonlang] val runtimeOrder: Vector[RuntimeLocalOrder] = Vector.empty
) {

  /** Ordered compatibility view; ordinary local access reads compact frames directly. */
  lazy val locals: SeqMap[CoreAst.LocalRef, Value] =
    if (runtimeFrames.isEmpty && runtimeLocals.isEmpty) baseLocals else SeqMap.from(localEntriesIterator)

  // Runtime binding groups own immutable arrays; checker-only environments retain their original persistent map.
  private[raccoonlang] lazy val localRefs: Set[CoreAst.LocalRef] =
    if (runtimeFrames.isEmpty && runtimeLocals.isEmpty) baseLocals.keySet
    else baseLocals.keySet ++ runtimeLocals.keySet ++ runtimeFrames.iterator.flatMap(_.layout.refsIterator)

  private[raccoonlang] def localEntriesIterator: Iterator[(CoreAst.LocalRef, Value)] =
    baseLocals.iterator ++ runtimeOrder.iterator.flatMap {
      case RuntimeLocalOrder.Frame(index)    => runtimeFrames(index).entriesIterator
      case RuntimeLocalOrder.Persistent(ref) => Iterator.single(ref -> runtimeLocals(ref))
    }

  private[raccoonlang] def localValuesIterator: Iterator[Value] =
    baseLocals.valuesIterator ++ runtimeLocals.valuesIterator ++ runtimeFrames.iterator.flatMap(_.valuesIterator)

  private[raccoonlang] def localValueOption(ref: CoreAst.LocalRef): Option[Value] = {
    val runtimeValue = runtimeValueOrNull(ref)
    if (runtimeValue ne null) Some(runtimeValue) else baseLocals.get(ref)
  }

  private def runtimeValueOrNull(ref: CoreAst.LocalRef): Value = {
    if (runtimeFrames.length > Env.directSlotLookupDepth) {
      val runtimeValue =
        runtimeFrames.last.lookupIndex.getOrElse(wtf("Deep runtime frames have no lookup index")).getOrElse(ref, null)
      if (runtimeValue ne null) return runtimeValue
      return runtimeLocals.getOrElse(ref, null)
    }

    var index = runtimeFrames.length - 1
    while (index >= 0) {
      val value = runtimeFrames(index).valueOrNull(ref)
      if (value ne null) return value
      index -= 1
    }
    runtimeLocals.getOrElse(ref, null)
  }

  private[raccoonlang] def containsLocal(ref: CoreAst.LocalRef): Boolean = {
    val runtimeFrameContains =
      if (runtimeFrames.length > Env.directSlotLookupDepth)
        runtimeFrames.last.lookupIndex.getOrElse(wtf("Deep runtime frames have no lookup index")).contains(ref)
      else {
        var index = runtimeFrames.length - 1
        var found = false
        while (index >= 0 && !found) {
          found = runtimeFrames(index).layout.indexOf(ref) >= 0
          index -= 1
        }
        found
      }
    runtimeFrameContains || runtimeLocals.contains(ref) || baseLocals.contains(ref)
  }

  def apply(name: String): Value =
    globals.getOrElse(name, fail(NotFound(name))).value(this)

  /** A local's value. An evidence parameter bound to deferred evidence is forced here, where it is first looked at. */
  def apply(ref: CoreAst.LocalRef): Value = {
    val runtimeValue = runtimeValueOrNull(ref)
    if (runtimeValue ne null) Value.forced(runtimeValue)
    else Value.forced(baseLocals.getOrElse(ref, fail(NotFound(ref.toString))))
  }

  def putGlobal(name: String, value: Value): Env = {
    Env.assertClosedGlobal(value)
    Env.assertCanonicalProof(value)

    if (globals.contains(name)) fail(AlreadyDefined(name))
    else if (name == "_") wtf("Wildcards not allowed in global names")
    else copy(globals = globals + (name -> GlobalBinding.Strict(value)))
  }

  /**
   * Publish a checked recursive group atomically. Every member is a lazy binding over one shared build of the whole
   * group, and the build runs in the environment that already contains the members' bindings (the runtime knot). No
   * member body is evaluated while the knot forms: recursive calls have already passed the structural judgment.
   */
  private[raccoonlang] def putRecursiveGroup(names: Vector[String], build: Env => Vector[Value.VLam]): Env = {
    if (names.isEmpty) wtf("Recursive group must not be empty")
    if (names.distinct.length != names.length) wtf("Recursive group names must be distinct")
    names.foreach { name =>
      if (globals.contains(name)) fail(AlreadyDefined(name))
      if (name == "_") wtf("Wildcards not allowed in global names")
    }
    var result: Env = null
    lazy val values: Vector[Value.VLam] = {
      val built = build(result)
      if (built.length != names.length)
        wtf(s"Recursive group built ${built.length} values for ${names.length} members")
      built
    }
    val bindings = names.zipWithIndex.map { case (name, index) => name -> new GlobalBinding.Lazy(() => values(index)) }
    result = copy(globals = globals ++ bindings)
    result
  }

  def putLocal(
      ref: CoreAst.LocalRef,
      value: Value
  ): Env = {
    Env.assertCanonicalProof(value)
    if (containsLocal(ref)) wtf(s"Local ref $ref is already bound")
    else if (runtimeOrder.isEmpty && runtimeFrames.isEmpty) copy(baseLocals = baseLocals.updated(ref, value))
    else
      copy(
        runtimeLocals = runtimeLocals.updated(ref, value),
        runtimeOrder = runtimeOrder :+ RuntimeLocalOrder.Persistent(ref)
      )
  }

  /** Bind one runtime group without rebuilding the persistent checker map. */
  private[raccoonlang] def bindRuntimeLocals(layout: RuntimeSlotLayout, values: Vector[Value]): Env = {
    if (layout.size != values.length) wtf("Runtime local binding group has inconsistent arity")
    if (layout.size == 0) return this

    val canonicalValues = new Array[Value](layout.size)
    var index = 0
    while (index < layout.size) {
      val ref = layout.refAt(index)
      val value = Value.canonicalizeProof(values(index))
      Env.assertCanonicalProof(value)
      if (containsLocal(ref)) wtf(s"Local ref $ref is already bound")
      canonicalValues(index) = value
      index += 1
    }
    val lookupIndex =
      if (runtimeFrames.length > Env.directSlotLookupDepth) {
        val prior = runtimeFrames.last.lookupIndex.getOrElse(wtf("Deep runtime frames have no lookup index"))
        Some(prior ++ layout.refsIterator.zip(canonicalValues.iterator))
      } else if (runtimeFrames.length + 1 > Env.directSlotLookupDepth) {
        val priorValues = runtimeFrames.iterator.flatMap(_.entriesIterator)
        Some((priorValues ++ layout.refsIterator.zip(canonicalValues.iterator)).toMap)
      } else {
        None
      }
    val frame = RuntimeSlotFrame.own(layout, canonicalValues, lookupIndex)
    copy(
      runtimeFrames = runtimeFrames :+ frame,
      runtimeOrder = runtimeOrder :+ RuntimeLocalOrder.Frame(runtimeFrames.length)
    )
  }

  /** Rebuild the cumulative deep lookup index after materializing its frame values. */
  private[raccoonlang] def rebuildRuntimeLookupIndex: Env = {
    if (runtimeFrames.length <= Env.directSlotLookupDepth) this
    else {
      val lookupIndex = runtimeFrames.iterator.flatMap(_.entriesIterator).toMap
      val lastIndex = runtimeFrames.length - 1
      copy(runtimeFrames = runtimeFrames.updated(lastIndex, runtimeFrames(lastIndex).withLookupIndex(lookupIndex)))
    }
  }

  /** Bind a whole argument or pattern group, canonicalizing each value, with one environment allocation. */
  private[raccoonlang] def bindLocals[A](
      binders: Vector[A],
      values: Vector[Value]
  )(refOf: A => CoreAst.LocalRef): Env = {
    if (binders.length != values.length) wtf("Local binding group has inconsistent arity")
    if (binders.isEmpty) return this
    if (runtimeOrder.nonEmpty || runtimeFrames.nonEmpty)
      return bindRuntimeLocals(RuntimeSlotLayout(binders.map(refOf)), values)

    var bound = baseLocals
    var index = 0
    while (index < binders.length) {
      val ref = refOf(binders(index))
      val value = Value.canonicalizeProof(values(index))
      Env.assertCanonicalProof(value)
      if (bound.contains(ref)) wtf(s"Local ref $ref is already bound")
      bound = bound.updated(ref, value)
      index += 1
    }
    copy(baseLocals = bound)
  }

  /**
   * Temporary constructor-instantiation environment used only by declaration-certified proof reconstruction. Stored
   * proof fields are intentionally reconstructed one layer at a time and may therefore be raw `VProof` values here.
   */
  private[raccoonlang] def putLocalUnchecked(ref: CoreAst.LocalRef, value: Value): Env = {
    if (containsLocal(ref)) wtf(s"Local ref $ref is already bound")
    else if (runtimeOrder.isEmpty && runtimeFrames.isEmpty) copy(baseLocals = baseLocals.updated(ref, value))
    else
      copy(
        runtimeLocals = runtimeLocals.updated(ref, value),
        runtimeOrder = runtimeOrder :+ RuntimeLocalOrder.Persistent(ref)
      )
  }

  /** The env a value closes over: the captured locals, each forced, since deferred evidence stays in no value. */
  def closeForEval(capturedRefs: Set[CoreAst.LocalRef]): Env = {
    if (capturedRefs.isEmpty)
      return copy(
        baseLocals = SeqMap.empty,
        runtimeLocals = SeqMap.empty,
        runtimeFrames = Vector.empty,
        runtimeOrder = Vector.empty
      )
    capturedRefs.foreach { ref =>
      if (!containsLocal(ref))
        wtf(s"Captured local $ref is outside env")
    }

    val capturedLocals =
      SeqMap.from(localEntriesIterator.collect { case (ref, value) if capturedRefs(ref) => ref -> Value.forced(value) })

    copy(
      baseLocals = capturedLocals,
      runtimeLocals = SeqMap.empty,
      runtimeFrames = Vector.empty,
      runtimeOrder = Vector.empty
    )
  }

  /** Record a published global as a constructor or selector of a family sealed by `seal`. */
  private[raccoonlang] def sealMember(name: String, seal: Sealing.Seal): Env = {
    if (!globals.contains(name)) wtf(s"Sealed member $name is not a global")
    copy(sealedMembers = sealedMembers + (name -> seal))
  }

  private[raccoonlang] def installStringLayout(layout: Value.ValidatedStringLayout): Env =
    nativeLiterals.stringLayout match {
      case Some(_) => wtf("Validated String layout is already installed")
      case None    => copy(nativeLiterals = nativeLiterals.copy(stringLayout = Some(layout)))
    }

  private[raccoonlang] def installEquality(validated: Either[String, MatchEquation.ValidatedEquality]): Env =
    equality match {
      case Right(_) => wtf("The validated equality family is already installed")
      case Left(_)  => copy(equality = validated)
    }

  private[raccoonlang] def installNatLayout(layout: Packed.ValidatedNatLayout): Env =
    nativeLiterals.natLayout match {
      case Some(_) => wtf("Validated Nat layout is already installed")
      case None    => copy(nativeLiterals = nativeLiterals.copy(natLayout = Some(layout)))
    }
}
