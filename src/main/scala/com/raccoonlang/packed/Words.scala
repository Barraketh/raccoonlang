package com.raccoonlang.packed

import com.raccoonlang.{DepSet, Kernel, NatNormalForm, Value, WTF}
import com.raccoonlang.Value._
import com.raccoonlang.ValueKey.Key

import scala.collection.mutable.ArrayBuffer

/**
 * Words of list-shaped types (docs/packed_lists.md): the one interface to `VWord`. Every cons application of a
 * list-shaped type is a word; see `Word` for the representation, which no code outside this package reads. A word is
 * constructor data: one or more layers followed by a terminator that is not a word.
 *
 * A kernel `List` value is `nil`, a word, or a stuck value. `append` follows the source definition: it shares its left
 * operand's layers onto the right operand, and where the left operand ends in a stuck value `x`, the result ends in the
 * stuck application `List.append(x, r)` of the native, which generic code handles like any stuck application. `length`
 * is the one operation that looks through such applications.
 *
 * Consumers outside this package see a word through `foreach` and `zip`, which hand them tokens, `map`, which rebuilds
 * it, `isProperSuffix`, `sameLength`, and the operations `cons`, `uncons`, `append` and `length`.
 */
private[raccoonlang] object Words {
  private[packed] val MinCapacity = 8
  private[packed] val MaxCapacity = 4096

  /**
   * Debug assertion, off by default: every constructed word recomputes its counts and field key by walking its chain
   * and compares. The `raccoon.verifyPackedKeys` system property turns it on; tests may set it directly.
   */
  @volatile private[raccoonlang] var verifyKeys: Boolean = java.lang.Boolean.getBoolean("raccoon.verifyPackedKeys")

  // ------------ Segments ------------

  private def layersOf(value: Value): Long =
    value match {
      case word: VWord => word.repr.layers
      case _           => 0
    }

  private def terminatorOf(value: Value): Value =
    value match {
      case word: VWord => word.repr.terminator
      case other       => other
    }

  /** The segment `chunk[start, end)` followed by `next`, whose field key is `phi`. Every segment is built here. */
  private[packed] def segment(chunk: Chunk, start: Int, end: Int, next: Value, phi: Key): VWord = {
    val count = (end - start).toLong
    val structural = chunk.needsStructuralDefEq || next.needsStructuralDefEq || chunk.tpe.needsStructuralDefEq
    val word = new VWord(
      new Word(chunk, start, end, next, count + layersOf(next), phi.hi, phi.lo, terminatorOf(next), structural)
    )
    if (verifyKeys) verify(word)
    word
  }

  /** The segments of the chain from `word`, in order, each as its word. */
  private[packed] def segments(word: VWord): ArrayBuffer[VWord] = {
    val result = ArrayBuffer.empty[VWord]
    var current: Value = word
    while (current.isInstanceOf[VWord]) {
      val segment = current.asInstanceOf[VWord]
      result += segment
      current = segment.repr.next
    }
    result
  }

  /**
   * Fill `cachedDeps` along the chain from `word` up to the first value whose dependencies are known, from the back, so
   * a long chain does not recurse.
   */
  private[packed] def cacheDeps(word: Word): Unit = {
    val pending = ArrayBuffer.empty[Word]
    var segment = word
    var after: DepSet = null
    while (after == null) {
      pending += segment
      segment.next match {
        case next: VWord if next.repr.cachedDeps == null => segment = next.repr
        case next: VWord                                 => after = next.repr.cachedDeps
        case terminator                                  => after = terminator.synDeps
      }
    }
    var index = pending.length - 1
    while (index >= 0) {
      val segment = pending(index)
      after = segment.ownDeps ++ after
      segment.cachedDeps = after
      index -= 1
    }
  }

  // ------------ Layers ------------

  private def sameType(left: Chunk, right: Value): Boolean = (left.tpe eq right) || left.tpe.key == right.key

  /**
   * A cons application with stored `fields` and result type `tpe`, where `head` has `shape`. When the tail is a word
   * whose first segment starts at its chunk's front, with a type of the same key, this claims the slot before it in
   * O(1). Otherwise it starts a chunk, writing the layer at its end. The new chunk doubles the tail's capacity, up to
   * the maximum, only when the tail starts at slot 0, so the conses that filled that chunk continue into the next; any
   * other tail, such as one whose front slot another value claimed or one decoded mid-chunk, gets the minimum, so
   * replacing the head of a long list or branching onto a shared tail allocates little.
   */
  def cons(head: ConstructorHead, shape: ListShape, fields: Vector[Value], tpe: Value): Value = {
    require(fields.length == shape.payloadWidth + 1, s"Constructor ${head.name} stores ${fields.length} fields")
    val tail = fields(shape.recursiveIndex)
    val first = tail match {
      case word: VWord => word.repr
      case _           => null
    }
    if (
      first != null && first.start == first.chunk.front && sameType(first.chunk, tpe) &&
      first.chunk.claimFront(1)
    ) layer(first.chunk, first.start - 1, first.end, first.next, fields, tail)
    else {
      val capacity =
        if (first != null && first.start == 0) math.min(MaxCapacity, math.max(MinCapacity, first.chunk.capacity * 2))
        else MinCapacity
      val chunk = new Chunk(head, shape, tpe, capacity, capacity)
      chunk.claimFront(1) // a fresh chunk has every slot free
      layer(chunk, capacity - 1, capacity, tail, fields, tail)
    }
  }

  // The claimed `slot` holds the new layer, followed by `next` within the chain of `tail`, the cons's recursive field.
  private def layer(chunk: Chunk, slot: Int, end: Int, next: Value, fields: Vector[Value], tail: Value): VWord = {
    chunk.writeLayer(slot, fields)
    segment(chunk, slot, end, next, PolynomialKeys.cons(chunk.letter(slot), PolynomialKeys.phi(tail)))
  }

  /**
   * The word of cons `head` whose layers have the payloads `layers`, payload-width values per layer in order, followed
   * by `next`, a value of the family instance `tpe`: one segment filling a new chunk of exactly its size from slot 0,
   * the layout `attach` grows, so a later append copies beside it or grows it. The key is computed in one pass from the
   * back, and only one word is built.
   */
  private[packed] def filled(head: ConstructorHead, tpe: Value, layers: Array[Value], next: Value): VWord = {
    val shape = head.listShape.getOrElse(throw WTF(s"Constructor ${head.name} is not the cons of a list-shaped type"))
    require(shape.payloadWidth > 0 && layers.nonEmpty && layers.length % shape.payloadWidth == 0, "Malformed layers")
    val count = layers.length / shape.payloadWidth
    val chunk = new Chunk(head, shape, tpe, count, 0)
    chunk.claimBack(count) // a fresh chunk has every slot free
    chunk.writePayloads(0, layers)
    var phi = PolynomialKeys.phi(next)
    var slot = count - 1
    while (slot >= 0) {
      phi = PolynomialKeys.cons(chunk.letter(slot), phi)
      slot -= 1
    }
    segment(chunk, 0, count, next, phi)
  }

  /**
   * A word observed as a constructor: the cons head and its stored fields, the first layer's payload with the tail at
   * the recursive index. The tail is the rest of the segment, built in O(1), or `next`.
   */
  def uncons(word: VWord): (ConstructorHead, Vector[Value]) = {
    val segment = word.repr
    val chunk = segment.chunk
    val shape = chunk.shape
    val tail =
      if (segment.start + 1 < segment.end)
        this.segment(
          chunk,
          segment.start + 1,
          segment.end,
          segment.next,
          PolynomialKeys.tail(segment.key, chunk.letter(segment.start))
        )
      else segment.next
    val fields = Vector.newBuilder[Value]
    var index = 0
    while (index <= shape.payloadWidth) {
      if (index < shape.recursiveIndex) fields += chunk.payload(segment.start, index)
      else if (index == shape.recursiveIndex) fields += tail
      else fields += chunk.payload(segment.start, index - 1)
      index += 1
    }
    (chunk.head, fields.result())
  }

  /** The segment's layers followed by `next` instead, a value of the segment's family. */
  private def withNext(segment: Word, next: Value): VWord = {
    val count = (segment.end - segment.start).toLong
    val phi =
      PolynomialKeys.replaceSuffix(segment.key, count, PolynomialKeys.phi(segment.next), PolynomialKeys.phi(next))
    this.segment(segment.chunk, segment.start, segment.end, next, phi)
  }

  /**
   * The segment `last` followed by `next`, a value of its family, instead of `last.next`, joining storage when `next`
   * begins with a segment whose chunk type has the same key. Let A be the segment of `last` and C that of `next`. In
   * order:
   *   1. Copy the smaller of the two (C on a tie) into claimed free slots beside the larger: after A when A ends at its
   *      chunk's back, or before C when C starts at its chunk's front.
   *   2. Otherwise, when A is the larger and ends at its chunk's back but the slots after it do not fit C, copy both
   *      into a new chunk of twice their combined length, filled from slot 0, leaving free slots after them.
   *   3. Otherwise link: A's segment takes `next` as its `next`.
   * The result has the tokens, counts and key of the link in every case; only storage differs. At most 2 * |A| layers
   * are copied, and the copies after A, with growth, extend one segment like an array list.
   */
  private def attach(last: Word, next: Value): VWord = {
    val first = next match {
      case word: VWord if sameType(last.chunk, word.repr.chunk.tpe) => word.repr
      case _                                                        => null
    }
    if (first == null) withNext(last, next)
    else {
      val a = last.end - last.start
      val c = first.end - first.start
      val phi = PolynomialKeys.replaceSuffix(last.key, a.toLong, PolynomialKeys.phi(last.next), first.key)
      val chunk = last.chunk
      if (c <= a && last.end == chunk.back) {
        if (chunk.claimBack(c)) {
          chunk.copyLayers(last.end, first.chunk, first.start, c)
          segment(chunk, last.start, last.end + c, first.next, phi)
        } else {
          val grown = new Chunk(chunk.head, chunk.shape, chunk.tpe, math.multiplyExact(2, a + c), 0)
          grown.claimBack(a + c) // a fresh chunk has every slot free
          grown.copyLayers(0, chunk, last.start, a)
          grown.copyLayers(a, first.chunk, first.start, c)
          segment(grown, 0, a + c, first.next, phi)
        }
      } else if (c > a && first.start == first.chunk.front && first.chunk.claimFront(a)) {
        first.chunk.copyLayers(first.start - a, chunk, last.start, a)
        segment(first.chunk, first.start - a, first.end, first.next, phi)
      } else withNext(last, next)
    }
  }

  // ------------ Natives ------------

  /**
   * The stuck application `List.append(x, r)` of the native, for a stuck `x` and an `r` other than `nil`. It is blocked
   * on the changes that let it compute: `x` becoming `nil` or a word, and, when `r` is neither a word nor `nil`, `r`
   * becoming `nil`, so that re-running it applies the right unit. A word never becomes `nil`, so it adds no blockers.
   * Every such application is built here.
   */
  private def stuckAppend(x: Value, r: Value): Value = {
    val blockers = r match {
      case _: VWord => ReductionBlockers.of(x)
      case _        => ReductionBlockers.of(x) ++ ReductionBlockers.of(r)
    }
    VBlockedApp(Kernel.append, Vector(x, r), x.tpe, blockers)
  }

  /** The operands of a stuck application of the native `append` (`stuckAppend`). */
  private object StuckAppend {
    def unapply(value: Value): Option[(Value, Value)] =
      value match {
        case VApp(head, Vector(x, r), _, _) if head eq Kernel.append => Some((x, r))
        case _                                                       => None
      }
  }

  /**
   * The native `append` of two values of one `List` type, as the source definition computes it, with the right unit.
   * `nil` on either side returns the other. Otherwise the segments of `l` are rebuilt from the back onto its terminator
   * appended to `r`: that is `r` itself when the terminator is `nil`, and otherwise the terminator `x` is stuck and it
   * is `stuckAppend(x, r)`. A segment takes the rebuilt rest as its `next`, sharing its element storage, and when `l`
   * ends in `nil` its last segment joins storage with `r` (`attach`). Each rebuilt segment h gets the field key of
   * `h ++ r`, which is `phi(h) + B^layers(h) * (phi(rest) - phi(old rest))`. A stuck `l` is itself the terminator. The
   * cost is one segment per segment of `l`, plus any copying at the junction.
   */
  def append(l: Value, r: Value): Value =
    if (Kernel.isListNil(l)) r
    else if (Kernel.isListNil(r)) l
    else
      l match {
        case word: VWord =>
          val rebuilt = segments(word)
          val terminator = word.repr.terminator
          val endsInNil = Kernel.isListNil(terminator)
          val last = rebuilt.length - 1
          var result =
            if (endsInNil) attach(rebuilt(last).repr, r) else withNext(rebuilt(last).repr, stuckAppend(terminator, r))
          var index = last - 1
          while (index >= 0) {
            result = withNext(rebuilt(index).repr, result)
            index -= 1
          }
          result
        case stuck => stuckAppend(stuck, r)
      }

  /**
   * The native `length`, as a Nat form: the layers of every word along the list, plus a stuck `length(x)` for each
   * stuck value `x` that is not an application of the native `append`, blocked on `x` 's reduction blockers. It looks
   * through such applications, so `length(append(x, r)) = length(x) + length(r)` and `length(cons(h, t)) =
   * succ(length(t))` hold through Nat's normal forms. A word costs O(1), since it records its layers and terminator.
   *
   * The applications form a graph that a program can share, as repeated `let y := List.append(d, d)` does, so a list
   * can use one application exponentially many times. Each distinct application, by identity, is visited once: a work
   * list orders them so that every application comes before all that use it, and a second loop in the reverse order
   * counts the uses of each, adding its operands' layers and stuck lengths that many times. A stuck `length(x)` met m
   * times along the paths is added as `m * length(x)`, the normal form of its m-fold sum, and the parts are summed in
   * one balanced tree (`NatNormalForm.sum`). Neither loop recurses, so applications may nest as deep as a program
   * writes them, and the cost is linear in the distinct applications plus the sum.
   */
  def length(list: Value): Value = {
    val entered = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap[Value, java.lang.Boolean])
    val ordered = java.util.Collections.newSetFromMap(new java.util.IdentityHashMap[Value, java.lang.Boolean])
    // Each distinct application with its operands, before every application that uses it.
    val order = ArrayBuffer.empty[(Value, Value, Value)]
    val pending = ArrayBuffer(terminatorOf(list))
    while (pending.nonEmpty) {
      val end = pending.last
      end match {
        case StuckAppend(x, r) if entered.add(end) =>
          for (operand <- Seq(terminatorOf(r), terminatorOf(x)))
            if (StuckAppend.unapply(operand).isDefined && !entered.contains(operand)) pending += operand
        case StuckAppend(x, r) =>
          pending.remove(pending.length - 1)
          if (ordered.add(end)) order += ((end, x, r))
        case _ => pending.remove(pending.length - 1)
      }
    }
    val uses = new java.util.IdentityHashMap[Value, BigInt]
    val parts = ArrayBuffer.empty[Value]
    var layers = BigInt(layersOf(list))
    // Add `count` uses of `end`, a terminator or a value that is not a word.
    def use(end: Value, count: BigInt): Unit =
      end match {
        case StuckAppend(_, _)            => uses.put(end, uses.getOrDefault(end, BigInt(0)) + count)
        case nil if Kernel.isListNil(nil) =>
        case stuck =>
          val atom = VBlockedApp(Kernel.length, Vector(stuck), Kernel.natType, ReductionBlockers.of(stuck))
          parts += (if (count == 1) atom else NatNormalForm.mul(NatNormalForm.literal(count), atom))
      }
    use(terminatorOf(list), 1)
    var index = order.length - 1
    while (index >= 0) {
      val (application, x, r) = order(index)
      val count = uses.get(application)
      layers += count * (layersOf(x) + layersOf(r))
      use(terminatorOf(x), count)
      use(terminatorOf(r), count)
      index -= 1
    }
    parts += NatNormalForm.literal(layers)
    NatNormalForm.sum(parts)
  }

  // ------------ Tokens ------------

  /**
   * Hand the tokens of `word` to the callbacks in order, each layer to `layer` and then the end to `end`, in one loop,
   * stopping when a callback returns false. Returns whether none did.
   */
  def foreach(word: VWord)(layer: Token => Boolean, end: Token => Boolean): Boolean = {
    val token = new Token(word)
    while (!token.atEnd) {
      if (!layer(token)) return false
      token.skip(1)
    }
    end(token)
  }

  /**
   * Whether two words have the same number of layers before their terminators, in O(1). Convertible words agree layer
   * by layer and a terminator is never a word, so words that differ here never convert. Unification must not use this:
   * a stuck terminator of one word can still be solved to the other's remaining layers.
   */
  def sameLength(left: VWord, right: VWord): Boolean = left.repr.layers == right.repr.layers

  /**
   * Walk two words with two cursors, handing aligned pairs of layers to `layers`, in one loop, until the callback
   * returns false (`Refused`), the rests begin new segments and are the same value or have equal keys (`Agreed`), or a
   * word ends (`Rests`). Where both cursors are on the same chunk slot, the rest of the shared run holds the same
   * payloads, and is skipped in O(1) without a callback.
   */
  def zip(left: VWord, right: VWord)(layers: (Token, Token) => Boolean): Zipped = {
    val l = new Token(left)
    val r = new Token(right)
    while (!l.atEnd && !r.atEnd) {
      if ((l.segment.chunk eq r.segment.chunk) && l.slot == r.slot) {
        val shared = math.min(l.segment.end - l.slot, r.segment.end - r.slot)
        l.skip(shared)
        r.skip(shared)
      } else {
        if (!layers(l, r)) return Zipped.Refused
        l.skip(1)
        r.skip(1)
      }
      if (l.atSegmentStart && r.atSegmentStart) {
        val (a, b) = (l.rest, r.rest)
        if ((a eq b) || a.key == b.key) return Zipped.Agreed
      }
    }
    new Zipped.Rests(l, r)
  }

  /**
   * The word rebuilt with its parts mapped, in one loop from the back; `mayChange` tells, from a part's dependencies,
   * whether `mapValue` can change it. Segments are read from the front while `mayChange` holds of the rest's
   * dependencies; the rest after them is kept, or mapped when it is the terminator. Then, from the back, each segment
   * is rebuilt onto the rebuilt rest: one whose own payloads and type cannot change keeps its slots, taking the rest as
   * its `next` and joining storage as `append` does where its old `next` was the terminator (`attach`), and any other
   * is consed again layer by layer with its payloads and type mapped. A terminator mapped to `nil`, to a word, or to
   * another stuck value is thereby spliced in.
   */
  def map(word: VWord, mayChange: DepSet => Boolean, mapValue: Value => Value): Value = {
    val read = ArrayBuffer.empty[VWord]
    var current: Value = word
    var reading = true
    while (reading) current match {
      case segment: VWord if mayChange(segment.synDeps) =>
        read += segment
        current = segment.repr.next
      case _ => reading = false
    }
    var result = current match {
      case _: VWord                                    => current
      case terminator if mayChange(terminator.synDeps) => mapValue(terminator)
      case terminator                                  => terminator
    }
    var index = read.length - 1
    while (index >= 0) {
      val kept = read(index)
      val segment = kept.repr
      result = if (!mayChange(segment.ownDeps)) {
        if (result eq segment.next) kept
        else if (segment.next.isInstanceOf[VWord]) withNext(segment, result)
        else attach(segment, result)
      } else {
        val chunk = segment.chunk
        val shape = chunk.shape
        val tpe = mapValue(chunk.tpe)
        var layers = result
        var slot = segment.end - 1
        while (slot >= segment.start) {
          val fields = Vector.tabulate(shape.payloadWidth + 1) { field =>
            if (field < shape.recursiveIndex) mapValue(chunk.payload(slot, field))
            else if (field == shape.recursiveIndex) layers
            else mapValue(chunk.payload(slot, field - 1))
          }
          layers = cons(chunk.head, shape, fields, tpe)
          slot -= 1
        }
        layers
      }
      index -= 1
    }
    result
  }

  /**
   * Whether `candidate` is stored as a proper suffix of `root`: a later part of one of its segments, followed by the
   * same rest. Every such suffix is a structural subterm.
   */
  def isProperSuffix(candidate: Value, root: VWord): Boolean =
    candidate match {
      case word: VWord =>
        val suffix = word.repr
        var current: Value = root
        while (current.isInstanceOf[VWord]) {
          val segment = current.asInstanceOf[VWord].repr
          if (
            (suffix.chunk eq segment.chunk) && suffix.end == segment.end && (suffix.next eq segment.next) &&
            (if (segment eq root.repr) suffix.start > segment.start else suffix.start >= segment.start)
          ) return true
          current = segment.next
        }
        false
      case _ => false
    }

  // ------------ Verification ------------

  private def verify(word: VWord): Unit = {
    val letters = ArrayBuffer.empty[Key]
    segments(word).foreach { rest =>
      val segment = rest.repr
      var slot = segment.start
      while (slot < segment.end) {
        letters += segment.chunk.letter(slot)
        slot += 1
      }
    }
    var phi = PolynomialKeys.phi(word.repr.terminator)
    var index = letters.length - 1
    while (index >= 0) {
      phi = PolynomialKeys.cons(letters(index), phi)
      index -= 1
    }
    if (letters.length.toLong != word.repr.layers || phi != word.repr.key)
      throw new AssertionError(s"Word counts or key disagree with its chain: $word")
  }
}
