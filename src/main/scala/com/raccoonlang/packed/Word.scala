package com.raccoonlang.packed

import com.raccoonlang.DepSet
import com.raccoonlang.Value
import com.raccoonlang.Value.VWord
import com.raccoonlang.ValueKey.Key

/**
 * The representation behind a `VWord` (docs/packed_lists.md, "Words"): the layers stored in `chunk` at slots
 * `[start, end)`, followed by `next`, the rest of the word. A word is a chain of such segments ending in a terminator,
 * the first value along the chain that is not a word: an end-constructor value such as `nil`, or a stuck value of the
 * family, such as a variable or, for the kernel `List`, a stuck application of the native `append`. So every word is
 * constructor data. Only `Words` and `Strings` build words. Invariants:
 *   - `start < end`, and `[start, end)` lay inside the chunk's written range when this was built, so its slots never
 *     change.
 *   - `next` is a value of the same family in any representation.
 *   - `layers` counts the layers of the whole chain from this segment, and `terminator` is the chain's terminator; both
 *     are derived from `next` where the segment is built.
 *   - `phiHi`, `phiLo` are the chain's field key in each lane (`PolynomialKeys`), which is also its key.
 *   - `structural` over-approximates whether a layer, `next`, or the type needs structural conversion.
 */
private[raccoonlang] final class Word private[packed] (
    private[packed] val chunk: Chunk,
    private[packed] val start: Int,
    private[packed] val end: Int,
    private[packed] val next: Value,
    private[packed] val layers: Long,
    private[packed] val phiHi: Long,
    private[packed] val phiLo: Long,
    private[packed] val terminator: Value,
    structural: Boolean
) {
  // Exact, because occurs and scope checks read it; computed on demand and cached (see `Words.cacheDeps`). Single-
  // threaded, like chunks and the evaluator.
  private[packed] var cachedDeps: DepSet = null

  /** The dependencies of this segment's payloads and its type, without `next`. */
  private[packed] def ownDeps: DepSet = chunk.payloadDeps(start, end) ++ chunk.tpe.synDeps

  /** The type of the word: the family instance of its layers. */
  private[raccoonlang] def tpe: Value = chunk.tpe

  private[raccoonlang] def key: Key = Key(phiHi, phiLo)

  private[raccoonlang] def synDeps: DepSet = {
    if (cachedDeps == null) Words.cacheDeps(this)
    cachedDeps
  }

  private[raccoonlang] def needsStructuralDefEq: Boolean = structural
}

/**
 * A cursor at one token of a word, handed to the callbacks of `Words.foreach` and `Words.zip`, and valid only while the
 * callback runs. A token is a layer, one cons application's stored fields other than the recursive one, or the end, the
 * terminator. Each accessor applies to the kinds it names.
 */
private[raccoonlang] final class Token private[packed] (root: VWord) {
  // The rest at the current segment: its word, or the terminator at the end, where `segment` is null.
  private var current: Value = _
  private[packed] var segment: Word = _
  private[packed] var slot: Int = 0

  // The field key of the rest from `keySlot` of the current segment, advanced only when `rest` asks for it.
  private var keySlot: Int = 0
  private var key: Key = _

  moveTo(root)

  /** Layer: the cons constructor. */
  def head: Value.ConstructorHead = segment.chunk.head

  /** Layer: the index of the recursive field among the cons's stored fields. */
  def recursiveIndex: Int = segment.chunk.shape.recursiveIndex

  /** Layer: the number of stored fields other than the recursive one. */
  def payloadWidth: Int = segment.chunk.shape.payloadWidth

  /** Layer: the stored field at `index`, counting the fields other than the recursive one. */
  def payload(index: Int): Value = segment.chunk.payload(slot, index)

  /** The type of the rest of the word from this token: the layer's family instance, or the end's type. */
  def tpe: Value = if (segment == null) current.tpe else segment.tpe

  /** End: the terminator. */
  def value: Value =
    if (segment == null) current else throw new IllegalStateException("A layer token has no single value")

  /**
   * The rest of the word from this token: a word, or the terminator at the end. In the middle of a segment it builds
   * the suffix, whose key costs one step per layer since the last suffix this token built in that segment.
   */
  def rest: Value =
    if (segment != null && slot > segment.start) {
      while (keySlot < slot) {
        key = PolynomialKeys.tail(key, segment.chunk.letter(keySlot))
        keySlot += 1
      }
      Words.segment(segment.chunk, slot, segment.end, segment.next, key)
    } else current

  private[packed] def atEnd: Boolean = segment == null

  /** Whether the token is the first layer of its segment, where `rest` is a word that already exists. */
  private[packed] def atSegmentStart: Boolean = segment != null && slot == segment.start

  /** Move past `count` layers of the current segment, which must remain in it or end exactly at its end. */
  private[packed] def skip(count: Int): Unit =
    if (slot + count < segment.end) slot += count
    else moveTo(segment.next)

  private def moveTo(value: Value): Unit = {
    current = value
    value match {
      case word: VWord =>
        segment = word.repr
        slot = segment.start
        keySlot = segment.start
        key = segment.key
      case _ => segment = null
    }
  }
}

/** Where `Words.zip` stopped walking two words. */
private[raccoonlang] sealed trait Zipped

private[raccoonlang] object Zipped {

  /** The callback returned false. */
  case object Refused extends Zipped

  /**
   * The rests begin new segments and are the same value or have equal keys, so they convert (docs/packed_lists.md,
   * "Trust").
   */
  case object Agreed extends Zipped

  /**
   * A word reached its end. `left` and `right` are the rests from there, at least one of them a terminator, built on
   * demand, since a rest in the middle of a segment costs a step per layer to key.
   */
  final class Rests private[packed] (leftToken: Token, rightToken: Token) extends Zipped {
    lazy val left: Value = leftToken.rest
    lazy val right: Value = rightToken.rest
  }
}
