package com.raccoonlang

import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value.MatchCode
import org.roaringbitmap.RoaringBitmap

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicLong
import scala.collection.mutable

/**
 * The code half of a stuck match's identity (docs/kernel.md, "Stuck matches"; `Value.MatchId`), and of an anonymous
 * lambda's and a function type's (`Value.ValueId.LocalId`): the checked node read at its cutoff, the length of the
 * environment it is evaluated in. What follows says "match" for any of the three. Slots are dense, so a local below
 * the cutoff is free, read from that environment, and every other one is bound inside the match, at the depth of its
 * binder (`CapturedIndexes`).
 *
 * The canonical code keeps everything that decides what the match computes, exactly: every node and its order, global
 * and constructor names, literals, projections, binders' instance markers, cases' fields and equations, lambdas' names
 * and recursive slots; so the motive and every argument the checker inserted are part of it, being checked code. It
 * leaves out what evaluation does not read: source positions, the names of locals and binders, and the node identities
 * of the function types, lambdas and matches inside it, which name nodes, not code (`NodeId`): the values two nodes of
 * one code build convert by opening, or by their own code. It also leaves out a match's `proofIntoProp`, which decides
 * only whether a suspended scrutinee is forced, not what the match computes, and a function type's universe, which the
 * checker computes from the binders' and codomain's types the code holds (`TypeChecker.checkPi`), up to the fresh
 * variables of its captures' levels, which differ between two checks of one type. It
 * renames every local, bound or mentioned: a free one by the order of its first mention, and a bound one by its offset from the cutoff. So
 * two matches have one `MatchCode` exactly when one is the other with its free locals renamed one to one, in order of
 * first mention, and its bound slots shifted together, which evaluates to the same result once each free local holds
 * the same value; `MatchId` pairs the code with those values.
 *
 * A free local the code reads only as the root of field projection chains (`r.a`, `r.x.a`) is captured as those
 * chains' values, not whole, each chain one capture in the code (`Tag.FreePath`): two copies of a match over records
 * that agree on the fields it reads compute the same and have one identity. A local read in any other way is captured
 * whole. The closed environment a stuck match resumes in keeps the whole local either way (`Layout.capturedIndexes`).
 *
 * A stuck match's code leaves out one thing more: its own scrutinee, the root match's, which is a hole in its code.
 * The match reads the scrutinee only through its value, which `MatchId` holds instead (docs/kernel.md, "Stuck
 * matches"), so the scrutinee's locals are free locals of the code only where the rest of it mentions them. A match
 * nested in the code keeps its scrutinee, which is code that the outer match evaluates.
 */
object MatchIdentity {

  /**
   * A match's code read at `cutoff`: its interned canonical code, and its free locals, the slots below the cutoff that
   * it mentions, each once, in the order the canonical code first mentions them, which is the order of a match's
   * captures. A match's own scrutinee is no part of its code, so the scrutinee's locals are among its free locals only
   * where the rest of the match mentions them.
   */
  final class Layout private[MatchIdentity] (
      val cutoff: Int,
      val code: MatchCode,
      freeSlots: Array[Int],
      captureSlots: Array[Int],
      capturePaths: Array[List[(String, Int)]]
  ) {
    def freeCount: Int = freeSlots.length

    def freeSlot(index: Int): Int = freeSlots(index)

    /**
     * The values the code reads of `env`, an environment of length `cutoff`, in order: each a free local's value, or,
     * for a local the code reads only through field projections, each projection it reads, read as evaluation reads it
     * (`StructEta.project`).
     */
    def captures(env: Env): Vector[Value] = {
      val values = Vector.newBuilder[Value]
      var fellBack = BigInt(0)
      var paths = false
      var index = 0
      while (index < captureSlots.length) {
        val slot = captureSlots(index)
        val whole = env(CoreAst.LocalRef(slot, s"#$slot"))
        val path = capturePaths(index)
        if (path.isEmpty) values += whole
        else {
          paths = true
          // A projection the code reads in a case may be typed only under that case's refinement, its local's type
          // not yet a record here, or another record (`projectPath`): then the local is captured whole, and the
          // identity says so (`fellBack`), so a whole capture is never compared with a projected one.
          projectPath(whole, path) match {
            case Some(projected) => values += projected
            case None =>
              values += whole
              fellBack = fellBack.setBit(index)
          }
        }
        index += 1
      }
      if (paths) values += NatNormalForm.literal(fellBack)
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
      val computed = compute(m, cutoff)
      m.layoutCache = computed
      computed
    }
  }

  /**
   * The layout of a function type at `cutoff`, as for a match: its values are identified by its code and captures
   * (`Value.ValueId.LocalId`), the code read as a match's is. A function type's code and a match's or lambda's never
   * coincide, since each starts with its own tag.
   */
  def layout(p: ETerm.Pi, cutoff: Int): Layout = {
    val cached = p.layoutCache
    if (cached != null && cached.cutoff == cutoff) cached
    else {
      val computed = compute(p, cutoff)
      p.layoutCache = computed
      computed
    }
  }

  /** The layout of an anonymous lambda at `cutoff`, as for a function type. */
  def layout(l: ETerm.Lam, cutoff: Int): Layout = {
    val cached = l.layoutCache
    if (cached != null && cached.cutoff == cutoff) cached
    else {
      val computed = compute(l, cutoff)
      l.layoutCache = computed
      computed
    }
  }

  private def compute(t: ElabAst.Term, cutoff: Int): Layout = {
    val bare = new Bare(cutoff)
    t match {
      case m: ETerm.Match => bare.matchRest(m)
      case other          => bare.term(other)
    }
    val encoder = new Encoder(cutoff, bare.slots)
    t match {
      case m: ETerm.Match => encoder.stuckMatch(m)
      case other          => encoder.term(other)
    }
    new Layout(cutoff, intern(encoder.shape), encoder.freeSlots, encoder.captureSlots, encoder.capturePaths)
  }

  /**
   * The value at `path` of `v`, projected as evaluation does (`StructEta.project`), or `None` where it cannot be. Each
   * step projects a value of the record family the code's projection names, as the checker typed it, and no other: the
   * case that reads the projection may refine the local's type to that record from another family's value, or from
   * another record's, as `Every(xs, f)` is `And(…)` at a cons and `True`, a record of no fields, at `nil`. A value of
   * another record has no such field, or one the code does not read.
   */
  private def projectPath(v: Value, path: List[(String, Int)]): Option[Value] =
    path.foldLeft(Option(v)) { case (cur, (family, field)) =>
      cur.flatMap { base =>
        base.tpe match {
          case Value.InductiveFamilyValue(instance) if instance.head.name == family && instance.meta.record.isDefined =>
            Some(StructEta.project(base, field))
          case _ => None
        }
      }
    }

  /**
   * A projection chain `r.f.g`: its root local and its steps, each a field's family and index, outermost last; `None`
   * for a term that is no projection of a local.
   */
  private def chain(t: ElabAst.Term): Option[(CoreAst.LocalRef, List[(String, Int)])] =
    t match {
      case ETerm.Proj(base, family, _, index, _) =>
        base match {
          case ETerm.LocalRef(ref, _) => Some((ref, List((family, index))))
          case _                      => chain(base).map { case (ref, path) => (ref, path :+ ((family, index))) }
        }
      case _ => None
    }

  /**
   * The free locals a code reads other than through field projections: those it captures whole. A free local read
   * only as the root of projection chains is captured as the values of those chains (`Encoder`), so two copies of a
   * code over records that agree on the fields it reads have one identity.
   */
  private final class Bare(cutoff: Int) {
    val slots: mutable.BitSet = mutable.BitSet.empty

    private def local(ref: CoreAst.LocalRef): Unit = if (ref.id < cutoff) slots += ref.id

    def term(t: ElabAst.Term): Unit =
      t match {
        case proj: ETerm.Proj =>
          chain(proj) match {
            case Some((ref, _)) if ref.id < cutoff => ()
            case _                                 => term(proj.base)
          }
        case ETerm.GlobalRef(_, _) | ETerm.NatLit(_, _) | ETerm.StrLit(_, _) => ()
        case ETerm.LocalRef(ref, _) => local(ref)
        case ETerm.App(fn, args, _) =>
          term(fn)
          args.foreach(term)
        case ETerm.Word(consHead, pieces, _) =>
          term(consHead)
          pieces.foreach {
            case ETerm.WordPiece.Layer(before, after) => (before ++ after).foreach(term)
            case ETerm.WordPiece.Splice(list)         => term(list)
          }
        case p: ETerm.Pi => pi(p)
        case ETerm.Body(lets, res, _) =>
          lets.foreach { let =>
            let.ty.foreach(term)
            term(let.value)
          }
          term(res)
        case ETerm.Lam(ty, body, _, _, _, _, _) =>
          pi(ty)
          term(body)
        case m: ETerm.Match =>
          term(m.scrut)
          matchRest(m)
      }

    def matchRest(m: ETerm.Match): Unit = {
      m.motive.foreach(term)
      m.cases.foreach(c => term(c.body))
    }

    private def pi(p: ETerm.Pi): Unit = {
      p.binders.foreach(b => binderType(b.ty))
      term(p.out)
    }

    private def binderType(ty: ElabAst.BinderType): Unit =
      ty match {
        case ElabAst.BinderType.TypePattern(tp, _)            => pattern(tp)
        case ElabAst.BinderType.ConstrainedCapture(ref, c, _) => local(ref); pattern(c)
      }

    private def pattern(tp: ElabAst.TypePattern): Unit =
      tp match {
        case ElabAst.TypePattern.Type(t) => term(t)
        case ElabAst.TypePattern.App(fn, args, _) =>
          term(fn)
          args.foreach(pattern)
        case ElabAst.TypePattern.Capture(ref, _, constraint) =>
          local(ref)
          constraint.foreach(pattern)
      }
  }

  /**
   * A canonical code: its tokens and, in order, the atoms its `Atom` tokens stand for, strings and numbers,
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
    val Hole = 6L
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
    val FreePath = 28L
  }

  /** Encodes one match at `cutoff`, numbering its free locals as it meets them. */
  private final class Encoder(cutoff: Int, bare: collection.BitSet) {
    private val tokens = mutable.ArrayBuilder.make[Long]
    private val atoms = mutable.ArrayBuilder.make[AnyRef]
    // The free locals the code mentions, each once in order of first mention: what a closed environment keeps.
    private val slotSeen = mutable.HashSet.empty[Int]
    private val free = mutable.ArrayBuilder.make[Int]
    // What the code reads of them, each once in order of first mention: a whole local, or a projection chain of one.
    private val captureIndex = mutable.HashMap.empty[(Int, List[(String, Int)]), Int]
    private val capSlots = mutable.ArrayBuilder.make[Int]
    private val capPaths = mutable.ArrayBuilder.make[List[(String, Int)]]

    def shape: Shape = new Shape(tokens.result(), atoms.result())

    def freeSlots: Array[Int] = free.result()

    def captureSlots: Array[Int] = capSlots.result()

    def capturePaths: Array[List[(String, Int)]] = capPaths.result()

    private def capture(slot: Int, path: List[(String, Int)]): Int = {
      if (slotSeen.add(slot)) free += slot
      captureIndex.getOrElseUpdate((slot, path), {
        capSlots += slot
        capPaths += path
        captureIndex.size
      })
    }

    private def long(value: Long): Unit = tokens += value

    private def atom(value: AnyRef): Unit = {
      long(Tag.Atom)
      atoms += value
    }

    // Every local, binding or mentioned: below the cutoff it is free, else bound at its offset.
    private def local(ref: CoreAst.LocalRef): Unit =
      if (ref.id < cutoff) {
        long(Tag.Free)
        long(capture(ref.id, Nil).toLong)
      } else {
        long(Tag.Bound)
        long((ref.id - cutoff).toLong)
      }

    private def flag(value: Boolean): Unit = long(if (value) 1L else 0L)

    private def projected(proj: ETerm.Proj): Option[(CoreAst.LocalRef, List[(String, Int)])] =
      chain(proj).filter { case (ref, _) => ref.id < cutoff && !bare.contains(ref.id) }

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
        case proj @ ETerm.Proj(base, family, field, index, _) if projected(proj).isDefined =>
          // A projection chain of a free local the code reads only so: one capture, the chain's value.
          val (ref, path) = projected(proj).get
          long(Tag.FreePath)
          long(capture(ref.id, path).toLong)
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
        case m: ETerm.Match =>
          long(Tag.Match)
          term(m.scrut)
          matchRest(m)
      }

    /**
     * A stuck match's own code: its scrutinee a hole, which its identity holds the value of instead (`Value.MatchId`),
     * so that the scrutinee's locals are numbered only where the rest mentions them.
     */
    def stuckMatch(m: ETerm.Match): Unit = {
      long(Tag.Match)
      long(Tag.Hole)
      matchRest(m)
    }

    /** A match after its scrutinee: its motive, then each case. */
    private def matchRest(m: ETerm.Match): Unit = {
      option(m.motive)(term)
      sequence(m.cases) { c =>
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
      // Not its universe: the checker computes that from the binders' and the codomain's types (`TypeChecker.checkPi`),
      // which the code holds, so it adds only the fresh variables a capture's level gets, which differ between two
      // checks of one function type.
      term(p.out)
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
