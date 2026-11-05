package com.raccoonlang

import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value.{MatchCode, Universe}
import org.roaringbitmap.RoaringBitmap

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicLong
import scala.collection.mutable

/**
 * The code half of a stuck match's identity (docs/kernel.md, "Stuck matches"; `Value.MatchId`): the checked match read
 * at its cutoff, the length of the environment it is evaluated in. Slots are dense, so a local below the cutoff is
 * free, read from that environment, and every other one is bound inside the match, at the depth of its binder
 * (`CapturedIndexes`).
 *
 * The canonical code keeps everything that decides what the match computes, exactly: every node and its order, global
 * and constructor names, literals, projections, binders' instance markers, cases' fields and equations, lambdas' names
 * and recursive slots, and each function type's universe; so the motive and every argument the checker inserted are
 * part of it, being checked code. It leaves out what evaluation does not read: source positions, the names of locals
 * and binders, and the node identities of the function types, lambdas and matches inside it, which name nodes, not code
 * (`NodeId`): the values two nodes of one code build convert by opening, or by their own code. It renames every local,
 * bound or mentioned: a free one by the order of its first mention, and a bound one by its offset from the cutoff. So
 * two matches have one `MatchCode` exactly when one is the other with its free locals renamed one to one, in order of
 * first mention, and its bound slots shifted together, which evaluates to the same result once each free local holds
 * the same value; `MatchId` pairs the code with those values.
 */
object MatchIdentity {

  /**
   * A match's code read at `cutoff`: its interned canonical code, and its free locals, the slots below the cutoff that
   * it mentions, each once, in the order the canonical code first mentions them, which is the order of a match's
   * captures.
   */
  final class Layout private[MatchIdentity] (val cutoff: Int, val code: MatchCode, freeSlots: Array[Int]) {
    def freeCount: Int = freeSlots.length

    def freeSlot(index: Int): Int = freeSlots(index)

    /** The values of the free locals in `env`, an environment of length `cutoff`, in order. */
    def captures(env: Env): Vector[Value] = {
      val values = Vector.newBuilder[Value]
      var index = 0
      while (index < freeSlots.length) {
        val slot = freeSlots(index)
        values += env(CoreAst.LocalRef(slot, s"#$slot"))
        index += 1
      }
      values.result()
    }

    /** The free locals as the set of slots a closed environment keeps (`RuntimeEnv.closeForEval`); a new bitmap. */
    def capturedIndexes: RoaringBitmap = RoaringBitmap.bitmapOf(freeSlots: _*)
  }

  /**
   * The layout of `m` at `cutoff`, computed once per match node and cutoff: a node is evaluated at one depth, its
   * binders' slots, so the node keeps the last layout and recomputes only for another cutoff.
   */
  def layout(m: ETerm.Match, cutoff: Int): Layout = {
    val cached = m.layoutCache
    if (cached != null && cached.cutoff == cutoff) cached
    else {
      val encoder = new Encoder(cutoff)
      encoder.term(m)
      val computed = new Layout(cutoff, intern(encoder.shape), encoder.freeSlots)
      m.layoutCache = computed
      computed
    }
  }

  /**
   * A canonical code: its tokens and, in order, the atoms its `Atom` tokens stand for, strings, numbers and universes,
   * compared by their own structural equality. Equal shapes are equal canonical codes: every node is a tag followed by
   * its fields in a fixed order, each sequence by its length and each option by a tag, so the tokens are a prefix code
   * for the tree.
   */
  private final class Shape(val tokens: Array[Long], val atoms: Array[AnyRef]) {
    override val hashCode: Int = 31 * java.util.Arrays.hashCode(tokens) + java.util.Arrays.hashCode(atoms)

    override def equals(other: Any): Boolean =
      other match {
        case that: Shape =>
          hashCode == that.hashCode && java.util.Arrays.equals(tokens, that.tokens) &&
          java.util.Arrays.equals(atoms, that.atoms)
        case _ => false
      }
  }

  // One code per shape in the process; serials are never reused, so one serial is one shape.
  private val interned = new ConcurrentHashMap[Shape, MatchCode]
  private val nextSerial = new AtomicLong(0L)

  private def intern(shape: Shape): MatchCode =
    interned.computeIfAbsent(shape, _ => new MatchCode(nextSerial.incrementAndGet()))

  private object Tag {
    val Atom = 1L
    val Free = 2L
    val Bound = 3L
    val None = 4L
    val Some = 5L
    val GlobalRef = 10L
    val LocalRef = 11L
    val App = 12L
    val Proj = 13L
    val NatLit = 14L
    val StrLit = 15L
    val Word = 16L
    val Layer = 17L
    val Splice = 18L
    val Pi = 19L
    val Body = 20L
    val Lam = 21L
    val Match = 22L
    val PatternType = 23L
    val PatternApp = 24L
    val PatternCapture = 25L
    val BinderPattern = 26L
    val BinderConstrained = 27L
  }

  /** Encodes one match at `cutoff`, numbering its free locals as it meets them. */
  private final class Encoder(cutoff: Int) {
    private val tokens = mutable.ArrayBuilder.make[Long]
    private val atoms = mutable.ArrayBuilder.make[AnyRef]
    private val freeIndex = mutable.HashMap.empty[Int, Int]
    private val free = mutable.ArrayBuilder.make[Int]

    def shape: Shape = new Shape(tokens.result(), atoms.result())

    def freeSlots: Array[Int] = free.result()

    private def long(value: Long): Unit = tokens += value

    private def atom(value: AnyRef): Unit = {
      long(Tag.Atom)
      atoms += value
    }

    // Every local, binding or mentioned: below the cutoff it is free, else bound at its offset.
    private def local(ref: CoreAst.LocalRef): Unit =
      if (ref.id < cutoff) {
        long(Tag.Free)
        long(freeIndex.getOrElseUpdate(ref.id, { free += ref.id; freeIndex.size }).toLong)
      } else {
        long(Tag.Bound)
        long((ref.id - cutoff).toLong)
      }

    private def flag(value: Boolean): Unit = long(if (value) 1L else 0L)

    private def option[A](value: Option[A])(encode: A => Unit): Unit =
      value match {
        case scala.None => long(Tag.None)
        case scala.Some(present) =>
          long(Tag.Some)
          encode(present)
      }

    private def sequence[A](values: Iterable[A])(encode: A => Unit): Unit = {
      long(values.size.toLong)
      values.foreach(encode)
    }

    def term(t: ElabAst.Term): Unit =
      t match {
        case ETerm.GlobalRef(name, _) =>
          long(Tag.GlobalRef)
          atom(name)
        case ETerm.LocalRef(ref, _) =>
          long(Tag.LocalRef)
          local(ref)
        case ETerm.App(fn, args, _) =>
          long(Tag.App)
          term(fn)
          sequence(args)(term)
        case ETerm.Proj(base, family, field, index, _) =>
          long(Tag.Proj)
          term(base)
          atom(family)
          atom(field)
          long(index.toLong)
        case ETerm.NatLit(number, _) =>
          long(Tag.NatLit)
          atom(number)
        case ETerm.StrLit(text, _) =>
          long(Tag.StrLit)
          atom(text)
        case ETerm.Word(consHead, pieces, _) =>
          long(Tag.Word)
          term(consHead)
          sequence(pieces) {
            case ETerm.WordPiece.Layer(before, after) =>
              long(Tag.Layer)
              sequence(before)(term)
              sequence(after)(term)
            case ETerm.WordPiece.Splice(list) =>
              long(Tag.Splice)
              term(list)
          }
        case pi: ETerm.Pi => this.pi(pi)
        case ETerm.Body(lets, res, _) =>
          long(Tag.Body)
          sequence(lets) { let =>
            local(let.localRef)
            option(let.ty)(term)
            term(let.value)
            flag(let.isInstance)
          }
          term(res)
        case ETerm.Lam(ty, body, _, name, recursiveSelf, _, recursivePeers) =>
          long(Tag.Lam)
          pi(ty)
          term(body)
          // A named lambda's value is the global of that name (`Interpreter.evalLam`).
          option(name)(atom)
          option(recursiveSelf)(local)
          sequence(recursivePeers) { case (ref, peer) =>
            local(ref)
            atom(peer)
          }
        case ETerm.Match(scrut, motive, cases, _, _) =>
          long(Tag.Match)
          term(scrut)
          option(motive)(term)
          sequence(cases) { c =>
            atom(c.ctorName)
            sequence(c.argRefs)(field => option(field)(local))
            option(c.equation)(local)
            term(c.body)
          }
      }

    private def pi(p: ETerm.Pi): Unit = {
      long(Tag.Pi)
      sequence(p.binders) { binder =>
        local(binder.localRef)
        binderType(binder.ty)
        flag(binder.isInstance)
      }
      term(p.out)
      atom(p.classifier: Universe)
    }

    private def binderType(ty: ElabAst.BinderType): Unit =
      ty match {
        case ElabAst.BinderType.TypePattern(tp, _) =>
          long(Tag.BinderPattern)
          pattern(tp)
        case ElabAst.BinderType.ConstrainedCapture(ref, constraint, _) =>
          long(Tag.BinderConstrained)
          local(ref)
          pattern(constraint)
      }

    private def pattern(tp: ElabAst.TypePattern): Unit =
      tp match {
        case ElabAst.TypePattern.Type(t) =>
          long(Tag.PatternType)
          term(t)
        case ElabAst.TypePattern.App(fn, args, _) =>
          long(Tag.PatternApp)
          term(fn)
          sequence(args)(pattern)
        case ElabAst.TypePattern.Capture(ref, _, constraint) =>
          long(Tag.PatternCapture)
          local(ref)
          option(constraint)(pattern)
      }
  }
}
