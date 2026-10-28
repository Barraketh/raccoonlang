package com.raccoonlang.packed

import com.raccoonlang.DepSet
import com.raccoonlang.Value
import com.raccoonlang.Value.{ConstructorHead, ListShape}
import com.raccoonlang.ValueKey.Key

import scala.collection.mutable

/**
 * A shared array of layers of one family instance `tpe`, whose cons constructor is `head`. Slots in `[front, back)` are
 * written once and never change; a claim moves `front` down or `back` up and the claimer then writes the claimed slots.
 * The chunk records nothing about what follows a slot, since different values can follow it in different words.
 * Metadata covers every written slot: whether any payload needs structural conversion, and a window containing every
 * slot whose payload has dependencies. Copying may overapproximate that window; queries still return exact sets. Chunks
 * are single-threaded, like the evaluator: claims, writes and the metadata are plain reads and writes.
 *
 * A chunk starts empty at `origin`. Cons construction starts it at `capacity`, so it grows down; a chunk filled from
 * its first slot up starts at 0.
 */
private[packed] final class Chunk(
    val head: ConstructorHead,
    val shape: ListShape,
    val tpe: Value,
    val capacity: Int,
    origin: Int
) {
  require(capacity > 0 && origin >= 0 && origin <= capacity, "Chunk origin must lie within its capacity")

  private val width = shape.payloadWidth
  private val payloads = new Array[Value](capacity * width)
  private var frontSlot = origin
  private var backSlot = origin

  private var anyStructural = false
  private var lowestDep = Int.MaxValue
  private var highestDep = -1

  // Dependency unions for aligned, power-of-two blocks of written slots, built on demand. A block's slots never
  // change, so its summary remains valid as either end of the chunk grows. There are fewer than two blocks per written
  // slot, shared by every queried range; no cache entry depends on a segment's particular start or end.
  private var dependencyBlocks: mutable.LongMap[DepSet] = null

  def front: Int = frontSlot

  def back: Int = backSlot

  def needsStructuralDefEq: Boolean = anyStructural

  /** Number of cached block summaries, for storage tests; an empty dependency window allocates none. */
  private[packed] def cachedDependencyBlocks: Int = if (dependencyBlocks == null) 0 else dependencyBlocks.size

  /**
   * Take the `count` free slots below `front`, if they fit. A caller that extends a segment checks first that the
   * segment starts at `front`.
   */
  def claimFront(count: Int): Boolean =
    frontSlot - count >= 0 && {
      frontSlot -= count
      true
    }

  /**
   * Take the `count` free slots from `back` up, if they fit. A caller that extends a segment checks first that the
   * segment ends at `back`.
   */
  def claimBack(count: Int): Boolean =
    backSlot + count <= capacity && {
      backSlot += count
      true
    }

  // Write one payload value of the claimed `slot` at `index` in the array, maintaining the metadata.
  private def store(slot: Int, index: Int, value: Value): Unit = {
    payloads(index) = value
    if (value.needsStructuralDefEq) anyStructural = true
    if (value.synDeps.nonEmpty) {
      if (slot < lowestDep) lowestDep = slot
      if (slot > highestDep) highestDep = slot
    }
  }

  /** Write a claimed slot from a cons application's stored fields, skipping the recursive one. */
  def writeLayer(slot: Int, fields: Vector[Value]): Unit = {
    var field = 0
    var index = slot * width
    while (field < fields.length) {
      if (field != shape.recursiveIndex) {
        store(slot, index, fields(field))
        index += 1
      }
      field += 1
    }
  }

  /** Write claimed slots from `slot` up with `layers`, payload-width values per layer in order. */
  def writePayloads(slot: Int, layers: Array[Value]): Unit = {
    var offset = 0
    while (offset < layers.length) {
      store(slot + offset / width, slot * width + offset, layers(offset))
      offset += 1
    }
  }

  /** Write claimed slots from `count` layers of `source`, a chunk of the same family, starting at slot `from`. */
  def copyLayers(slot: Int, source: Chunk, from: Int, count: Int): Unit = {
    System.arraycopy(source.payloads, from * width, payloads, slot * width, count * width)
    if (source.anyStructural) anyStructural = true
    val first = math.max(from, source.lowestDep)
    val last = math.min(from + count - 1, source.highestDep)
    if (first <= last) {
      lowestDep = math.min(lowestDep, slot + first - from)
      highestDep = math.max(highestDep, slot + last - from)
    }
  }

  def payload(slot: Int, index: Int): Value = payloads(slot * width + index)

  def letter(slot: Int): Key = PolynomialKeys.layerLetter(payloads, slot * width, width)

  /**
   * Dependencies of the payloads in `[from, until)`, a range of written slots. A range outside the dependency window
   * answers in O(1) and allocates nothing. Otherwise, split its intersection with the window into O(log capacity)
   * aligned, power-of-two blocks and union their summaries. Missing blocks are built once from their children, so
   * growing prefixes and decoded tails share O(n) cached summaries for n written slots, besides the space for the
   * dependency sets themselves. A first query may build all the blocks in its range; later queries reuse them.
   */
  def payloadDeps(from: Int, until: Int): DepSet = {
    val first = math.max(from, lowestDep)
    val last = math.min(until - 1, highestDep)
    if (first > last) DepSet.empty
    else {
      val stop = last + 1
      if (dependencyBlocks == null) dependencyBlocks = mutable.LongMap.empty
      val parts = mutable.ArrayBuffer.empty[DepSet]
      var start = first
      while (start < stop) {
        val fits = Integer.highestOneBit(stop - start)
        val size = if (start == 0) fits else math.min(Integer.lowestOneBit(start), fits)
        // This block is wholly inside the queried written range, so even a newly cached summary is permanent.
        parts += blockDeps(start, size)
        start += size
      }
      if (parts.length == 1) parts.head else DepSet.unionAll(parts)
    }
  }

  /**
   * Dependencies of `[start, start + size)`, all written, where size is a power of two and start is aligned to it. Only
   * complete blocks are cached, so new writes never invalidate one. Recursion depth is logarithmic in size.
   */
  private def blockDeps(start: Int, size: Int): DepSet = {
    val key = (start.toLong << 32) | size.toLong
    dependencyBlocks.getOrElse(key, null) match {
      case null =>
        val deps =
          if (size == 1) {
            if (width == 1) payloads(start).synDeps
            else DepSet.unionAll((0 until width).map(index => payload(start, index).synDeps))
          } else {
            val half = size / 2
            blockDeps(start, half) ++ blockDeps(start + half, half)
          }
        dependencyBlocks.update(key, deps)
        deps
      case known => known
    }
  }
}
