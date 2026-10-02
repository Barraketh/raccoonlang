package com.raccoonlang

/** A stable, precomputed mapping from resolved local refs to positions in one runtime binding group. */
private[raccoonlang] final class RuntimeSlotLayout private (
    private val refs: Vector[CoreAst.LocalRef],
    private val offsets: Map[CoreAst.LocalRef, Int],
    val size: Int
) {
  def indexOf(ref: CoreAst.LocalRef): Int = {
    val index = offsets.getOrElse(ref, -1)
    if (index >= 0 && index < size) index else -1
  }

  def refAt(index: Int): CoreAst.LocalRef = {
    if (index < 0 || index >= size) wtf(s"Runtime slot index $index is outside layout size $size")
    refs(index)
  }

  def refsIterator: Iterator[CoreAst.LocalRef] = refs.iterator.take(size)

  private[raccoonlang] def sharesIndexTable(other: RuntimeSlotLayout): Boolean = offsets eq other.offsets

  def prefix(length: Int): RuntimeSlotLayout = {
    if (length < 0 || length > size) wtf(s"Runtime slot prefix $length is outside layout size $size")
    if (length == size) this else new RuntimeSlotLayout(refs, offsets, length)
  }
}

private[raccoonlang] object RuntimeSlotLayout {
  def apply(refs: Vector[CoreAst.LocalRef]): RuntimeSlotLayout = {
    val offsets = refs.iterator.zipWithIndex.toMap
    if (offsets.size != refs.length) wtf("Runtime slot layout contains duplicate local refs")
    new RuntimeSlotLayout(refs, offsets, refs.length)
  }
}

/**
 * One immutable runtime binding group. The array is freshly allocated for the frame and never exposed or mutated after
 * publication; escaping closures and neutral thunks copy their selected values into a persistent Env first.
 */
private[raccoonlang] final class RuntimeSlotFrame private (
    val layout: RuntimeSlotLayout,
    private val values: Array[Value],
    private[raccoonlang] val lookupIndex: Option[Map[CoreAst.LocalRef, Value]]
) {

  /** Null marks a miss; a bound runtime local is never null. */
  def valueOrNull(ref: CoreAst.LocalRef): Value = {
    val index = layout.indexOf(ref)
    if (index < 0) null else values(index)
  }

  def entriesIterator: Iterator[(CoreAst.LocalRef, Value)] =
    layout.refsIterator.zip(values.iterator)

  def valuesIterator: Iterator[Value] = values.iterator

  /** Materialization replaces frame values, so the old cumulative index must not retain stale values. */
  def mapValues(f: Value => Value): RuntimeSlotFrame =
    new RuntimeSlotFrame(layout, values.map(f), None)

  /** Attach a freshly rebuilt cumulative index without copying the frame's already-owned values. */
  def withLookupIndex(index: Map[CoreAst.LocalRef, Value]): RuntimeSlotFrame =
    new RuntimeSlotFrame(layout, values, Some(index))
}

private[raccoonlang] object RuntimeSlotFrame {

  /** Takes ownership of a fresh private array which the caller will never mutate or retain. */
  def own(
      layout: RuntimeSlotLayout,
      values: Array[Value],
      lookupIndex: Option[Map[CoreAst.LocalRef, Value]]
  ): RuntimeSlotFrame = {
    if (layout.size != values.length) wtf(s"Runtime slot layout has ${layout.size} slots for ${values.length} values")
    new RuntimeSlotFrame(layout, values, lookupIndex)
  }
}

/** Concurrent cache of only the prefix views that have actually been requested. Prefixes share the full index map. */
private[raccoonlang] final class RuntimeSlotPrefixCache(full: RuntimeSlotLayout) {
  private[this] val requested = new java.util.concurrent.ConcurrentHashMap[Int, RuntimeSlotLayout]()

  private[raccoonlang] def cachedPrefixCount: Int = requested.size()

  def apply(length: Int): RuntimeSlotLayout = {
    if (length < 0 || length > full.size) wtf(s"Runtime slot prefix $length is outside layout size ${full.size}")
    if (length == full.size) full
    else {
      val cached = requested.get(length)
      if (cached ne null) cached
      else {
        val created = full.prefix(length)
        val winner = requested.putIfAbsent(length, created)
        if (winner eq null) created else winner
      }
    }
  }
}

/** Chronological pieces needed only when a closure asks for an ordered locals snapshot. */
private[raccoonlang] sealed trait RuntimeLocalOrder

private[raccoonlang] object RuntimeLocalOrder {
  final case class Frame(index: Int) extends RuntimeLocalOrder
  final case class Persistent(ref: CoreAst.LocalRef) extends RuntimeLocalOrder
}
