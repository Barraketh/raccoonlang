package com.raccoonlang.packed

import com.raccoonlang.Value
import com.raccoonlang.Value.VWord
import com.raccoonlang.ValueKey
import com.raccoonlang.ValueKey.{Key, WordTag}

/**
 * Field keys of words (docs/packed_lists.md, "Keys"). For a word whose layers contribute the letters s0 .. s(n-1) and
 * whose terminator is t, in each lane,
 * {{{
 *   phi = s0 + s1 * B + ... + s(n-1) * B^(n-1) + B^n * symbol(t)
 * }}}
 * where a layer's letter is the symbol of its payload tuple. The phi of a value that is not a word is the symbol of its
 * ordinary key, tagged as a terminator. So phi depends only on the word's layers and terminator, never on how they are
 * divided into segments or stored. The key of a word is its phi in both lanes.
 *
 * A symbol maps a tagged 128-bit key into F by reducing each half. Both lanes use fixed bases, so keys are
 * deterministic. A word's key is trusted like every other key (see `ValueKey`): it guards against accidental
 * collisions, and the prime modulus avoids the structured collisions of polynomial hashing modulo 2^64.
 */
private[raccoonlang] object PolynomialKeys {
  import Field._

  private val BaseHi: Long = 0x0b5ad4eceda1ce2aL
  private val BaseHiInverse: Long = inverse(BaseHi)
  private val BaseLo: Long = 0x13c6ef372fe94f82L
  private val BaseLoInverse: Long = inverse(BaseLo)

  /** A tagged 128-bit key as a symbol in both lanes. */
  private def symbol(key: Key): Key = Key(reduce(key.hi), reduce(key.lo))

  /** The letter of the layer stored at `payloads(from until from + width)`: its payload tuple's key as a symbol. */
  private[packed] def layerLetter(payloads: Array[Value], from: Int, width: Int): Key = {
    val mixer = ValueKey.mixer(WordTag.Layer)
    var index = from
    while (index < from + width) {
      mixer.key(payloads(index).key)
      index += 1
    }
    mixer.long(width.toLong)
    symbol(mixer.result)
  }

  /** phi of any value: a word's key, or the ordinary key of another value as a terminator symbol. */
  private[packed] def phi(value: Value): Key =
    value match {
      case word: VWord => word.key
      case other =>
        val mixer = ValueKey.mixer(WordTag.Terminator)
        mixer.key(other.key)
        symbol(mixer.result)
    }

  /** phi of a layer contributing `letter` followed by a value whose phi is `rest`. */
  private[packed] def cons(letter: Key, rest: Key): Key =
    Key(add(letter.hi, mul(BaseHi, rest.hi)), add(letter.lo, mul(BaseLo, rest.lo)))

  /** phi of the rest of a word whose phi is `whole` and whose first letter is `letter`. */
  private[packed] def tail(whole: Key, letter: Key): Key =
    Key(mul(sub(whole.hi, letter.hi), BaseHiInverse), mul(sub(whole.lo, letter.lo), BaseLoInverse))

  /**
   * phi of a word whose phi is `whole` once its first `layers` layers are followed by a value with phi `replacement`
   * instead of one with phi `replaced`.
   */
  private[packed] def replaceSuffix(whole: Key, layers: Long, replaced: Key, replacement: Key): Key =
    Key(
      add(whole.hi, mul(pow(BaseHi, layers), sub(replacement.hi, replaced.hi))),
      add(whole.lo, mul(pow(BaseLo, layers), sub(replacement.lo, replaced.lo)))
    )

}
