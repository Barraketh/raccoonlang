package com.raccoonlang.packed

import com.raccoonlang.Value
import com.raccoonlang.Value.VWord

/**
 * Test hook: read-only views of a word's storage, so that tests can check the storage rules the interface hides on
 * purpose (claims, chunk growth, the junction rule, sharing). The checker never uses it.
 */
private[raccoonlang] object Storage {
  val MinCapacity: Int = Words.MinCapacity
  val MaxCapacity: Int = Words.MaxCapacity

  /**
   * One segment `[start, end)` of a chunk: `word` is the word from this segment on, `next` the rest after it, and
   * `chunk` the chunk's identity, to compare with `eq`.
   */
  final case class SegmentView(
      word: VWord,
      chunk: AnyRef,
      start: Int,
      end: Int,
      capacity: Int,
      front: Int,
      back: Int,
      next: Value
  )

  /** The first segment of a word. */
  def segment(word: Value): SegmentView = {
    val vword = word.asInstanceOf[VWord]
    val segment = vword.repr
    val chunk = segment.chunk
    SegmentView(vword, chunk, segment.start, segment.end, chunk.capacity, chunk.front, chunk.back, segment.next)
  }

  /** The segments of a word in order; none for a value that is not a word. */
  def segments(value: Value): Vector[SegmentView] =
    value match {
      case word: VWord => Words.segments(word).map(segment).toVector
      case _           => Vector.empty
    }

  /** The number of layers of a word, 0 for another value. */
  def layers(value: Value): Long =
    value match {
      case word: VWord => word.repr.layers
      case _           => 0
    }
}
