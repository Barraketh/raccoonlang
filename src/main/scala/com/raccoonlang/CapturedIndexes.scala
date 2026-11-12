package com.raccoonlang

import com.raccoonlang.ElabAst.Term
import com.raccoonlang.ElabAst.Term.Match
import org.roaringbitmap.RoaringBitmap

object CapturedIndexes {
  // This is not lexical free-variable analysis. Core local ids are allocated densely and monotonically, so when a
  // closure is built, every ref to the current environment has id < env.locals.length. Locals introduced inside the
  // term being closed over have ids >= that cutoff and are intentionally ignored here.

  private def addRef(ref: CoreAst.LocalRef, cutoff: Int, refs: RoaringBitmap): Unit = {
    if (ref.id < cutoff) refs.add(ref.id)
  }

  private def goTerms(terms: IterableOnce[ElabAst.Term], cutoff: Int, refs: RoaringBitmap): Unit =
    terms.iterator.foreach(goTerm(_, cutoff, refs))

  private def goPatterns(terms: IterableOnce[ElabAst.TypePattern], cutoff: Int, refs: RoaringBitmap): Unit =
    terms.iterator.foreach(goPattern(_, cutoff, refs))

  private def goPattern(pattern: ElabAst.TypePattern, cutoff: Int, refs: RoaringBitmap): Unit =
    pattern match {
      case ElabAst.TypePattern.Capture(ref, _, constraint) =>
        addRef(ref, cutoff, refs)
        constraint.foreach(goPattern(_, cutoff, refs))

      case ElabAst.TypePattern.App(fn, args, _) =>
        goTerm(fn, cutoff, refs)
        goPatterns(args, cutoff, refs)

      case ElabAst.TypePattern.Type(term) =>
        goTerm(term, cutoff, refs)
    }

  private def goBinderType(binderType: ElabAst.BinderType, cutoff: Int, refs: RoaringBitmap): Unit =
    binderType match {
      case ElabAst.BinderType.TypePattern(tp, _) =>
        goPattern(tp, cutoff, refs)

      case ElabAst.BinderType.ConstrainedCapture(ref, constraint, _) =>
        addRef(ref, cutoff, refs)
        goPattern(constraint, cutoff, refs)
    }

  private def goTerm(term: ElabAst.Term, cutoff: Int, refs: RoaringBitmap): Unit =
    term match {
      case Term.GlobalRef(_, _) =>

      case Term.LocalRef(ref, _) =>
        addRef(ref, cutoff, refs)

      case Term.NatLit(_, _) =>

      case Term.StrLit(_, _) =>

      case Term.Word(_, pieces, _) =>
        pieces.foreach {
          case Term.WordPiece.Layer(before, after) => goTerms(before ++ after, cutoff, refs)
          case Term.WordPiece.Splice(list)         => goTerm(list, cutoff, refs)
        }

      case Term.Pi(binders, out, _, _, _) =>
        binders.foreach { b =>
          goBinderType(b.ty, cutoff, refs)
        }
        goTerm(out, cutoff, refs)

      case Term.App(fn, args, _) => goTerms(fn +: args, cutoff, refs)

      case Term.Proj(base, _, _, _, _) => goTerm(base, cutoff, refs)

      case Term.Body(lets, res, _) =>
        lets.foreach { l =>
          goTerm(l.value, cutoff, refs)
          l.ty.foreach(t => goTerm(t, cutoff, refs))
        }
        goTerm(res, cutoff, refs)

      case Term.Lam(ty, body, _, _, _, _, _) =>
        goTerm(ty, cutoff, refs)
        goTerm(body, cutoff, refs)

      case Match(scrut, motive, cases, _, _, _) =>
        goTerm(scrut, cutoff, refs)
        motive.foreach(goTerm(_, cutoff, refs))
        cases.foreach { c =>
          goTerm(c.body, cutoff, refs)
        }
    }

  /**
   * `term`, syntax numbered for a scope shorter than one of `depth` locals, renumbered for that scope (`MatchChecker`):
   * every local a binder inside it binds moves up by one shift, which takes the lowest of them to `depth`, so that none
   * is bound again over a live local of the longer scope. Slots are dense, so every local it reads at or above that
   * lowest one is one it binds, and the locals below are the shorter scope's, which the longer one extends: they keep
   * their slots. Only bound locals are renamed, so it evaluates as it did; each Pi, lambda and match it rebuilds gets a
   * fresh `NodeId`, as quotation's do (`ValueQuote`). Syntax that binds nothing below `depth` is returned as it is.
   */
  def rebase(term: ElabAst.TypeTerm, depth: Int): ElabAst.TypeTerm = {
    val lowest = lowestBound(term)
    if (lowest >= depth) term
    else new Shift(lowest, depth - lowest).typeTerm(term)
  }

  /** The lowest slot a binder inside `term` binds, or `Int.MaxValue` where none binds one. */
  private def lowestBound(term: ElabAst.Term): Int = {
    var lowest = Int.MaxValue
    def ref(r: CoreAst.LocalRef): Unit = lowest = math.min(lowest, r.id)
    def pattern(p: ElabAst.TypePattern): Unit =
      p match {
        case ElabAst.TypePattern.Capture(r, _, constraint) => ref(r); constraint.foreach(pattern)
        case ElabAst.TypePattern.App(fn, args, _)          => go(fn); args.foreach(pattern)
        case ElabAst.TypePattern.Type(t)                   => go(t)
      }
    def binderType(bt: ElabAst.BinderType): Unit =
      bt match {
        case ElabAst.BinderType.TypePattern(tp, _)          => pattern(tp)
        case ElabAst.BinderType.ConstrainedCapture(r, c, _) => ref(r); pattern(c)
      }
    def go(t: ElabAst.Term): Unit =
      t match {
        case Term.GlobalRef(_, _) | Term.LocalRef(_, _) | Term.NatLit(_, _) | Term.StrLit(_, _) =>
        case Term.Word(_, pieces, _) =>
          pieces.foreach {
            case Term.WordPiece.Layer(before, after) => (before ++ after).foreach(go)
            case Term.WordPiece.Splice(list)         => go(list)
          }
        case Term.Pi(binders, out, _, _, _) => binders.foreach(b => { ref(b.localRef); binderType(b.ty) }); go(out)
        case Term.App(fn, args, _)          => go(fn); args.foreach(go)
        case Term.Proj(base, _, _, _, _)    => go(base)
        case Term.Body(lets, res, _)        => lets.foreach(l => { ref(l.localRef); go(l.value); l.ty.foreach(go) }); go(res)
        case Term.Lam(ty, body, _, _, self, _, peers) =>
          self.foreach(ref); peers.foreach(p => ref(p._1)); go(ty); go(body)
        case Match(scrut, motive, cases, _, _, _) =>
          go(scrut); motive.foreach(go)
          cases.foreach(c => { c.argRefs.foreach(_.foreach(ref)); c.equation.foreach(ref); go(c.body) })
      }
    go(term)
    lowest
  }

  /** Syntax with every local at or above `from`, bound or read, moved up by `by`. */
  private final class Shift(from: Int, by: Int) {
    private def ref(r: CoreAst.LocalRef): CoreAst.LocalRef = if (r.id >= from) r.copy(id = r.id + by) else r

    def term(t: ElabAst.Term): ElabAst.Term =
      t match {
        case tt: ElabAst.TypeTerm => typeTerm(tt)
        case Term.Body(lets, res, span) =>
          Term.Body(lets.map(l => l.copy(localRef = ref(l.localRef), ty = l.ty.map(typeTerm), value = term(l.value))), term(res), span)
        case m: Match =>
          m.copy(
            scrut = term(m.scrut),
            motive = m.motive.map(typeTerm),
            cases = m.cases.map(c => c.copy(argRefs = c.argRefs.map(_.map(ref)), body = term(c.body), equation = c.equation.map(ref))),
            nodeId = NodeId.fresh()
          )
      }

    def typeTerm(t: ElabAst.TypeTerm): ElabAst.TypeTerm =
      t match {
        case Term.LocalRef(r, span)                                       => Term.LocalRef(ref(r), span)
        case Term.GlobalRef(_, _) | Term.NatLit(_, _) | Term.StrLit(_, _) => t
        case Term.App(fn, args, span)                                     => Term.App(term(fn), args.map(term), span)
        case p: Term.Proj                                                 => p.copy(base = term(p.base))
        case Term.Word(head, pieces, span) =>
          Term.Word(
            head,
            pieces.map {
              case Term.WordPiece.Layer(before, after) => Term.WordPiece.Layer(before.map(term), after.map(term))
              case Term.WordPiece.Splice(list)         => Term.WordPiece.Splice(term(list))
            },
            span
          )
        case p: Term.Pi => pi(p)
        case l: Term.Lam =>
          l.copy(
            ty = pi(l.ty),
            body = term(l.body),
            recursiveSelf = l.recursiveSelf.map(ref),
            nodeId = NodeId.fresh(),
            recursivePeers = l.recursivePeers.map { case (r, peer) => (ref(r), peer) }
          )
      }

    private def pi(p: Term.Pi): Term.Pi =
      p.copy(binders = p.binders.map(b => b.copy(localRef = ref(b.localRef), ty = binderType(b.ty))), out = typeTerm(p.out), nodeId = NodeId.fresh())

    private def binderType(t: ElabAst.BinderType): ElabAst.BinderType =
      t match {
        case ElabAst.BinderType.TypePattern(tp, span) => ElabAst.BinderType.TypePattern(topLevel(tp), span)
        case ElabAst.BinderType.ConstrainedCapture(r, constraint, span) =>
          ElabAst.BinderType.ConstrainedCapture(ref(r), topLevel(constraint), span)
      }

    private def topLevel(tp: ElabAst.TopLevelTP): ElabAst.TopLevelTP =
      tp match {
        case ElabAst.TypePattern.Type(tt) => ElabAst.TypePattern.Type(typeTerm(tt))
        case ElabAst.TypePattern.App(fn, args, span) =>
          val head = fn match {
            case Term.LocalRef(r, sp)   => Term.LocalRef(ref(r), sp)
            case global: Term.GlobalRef => global
          }
          ElabAst.TypePattern.App(head, args.map(pattern), span)
      }

    private def pattern(tp: ElabAst.TypePattern): ElabAst.TypePattern =
      tp match {
        case top: ElabAst.TopLevelTP => topLevel(top)
        case ElabAst.TypePattern.Capture(r, span, constraint) =>
          ElabAst.TypePattern.Capture(ref(r), span, constraint.map(topLevel))
      }
  }

  /** Whether `term` names the local `id`, one that no binder inside `term` binds, as ids grow with depth. */
  def mentions(term: ElabAst.Term, id: Int): Boolean = {
    val refs = new RoaringBitmap
    goTerm(term, id + 1, refs)
    refs.contains(id)
  }

  def getCapturedIndexes(term: ElabAst.Term, env: Env): RoaringBitmap = {
    val indexes = new RoaringBitmap
    if (env.locals.nonEmpty) {
      goTerm(term, env.locals.length, indexes)
    }
    indexes
  }
}
