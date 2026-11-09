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
   * Whether a binder inside `term` binds a local below `cutoff`: syntax numbered for a scope shorter than the one of
   * `cutoff` locals, whose binders would collide with that scope's locals if evaluated there (`MatchChecker`).
   */
  def bindsBelow(term: ElabAst.Term, cutoff: Int): Boolean = {
    def ref(r: CoreAst.LocalRef): Boolean = r.id < cutoff
    def pattern(p: ElabAst.TypePattern): Boolean =
      p match {
        case ElabAst.TypePattern.Capture(r, _, constraint) => ref(r) || constraint.exists(pattern)
        case ElabAst.TypePattern.App(fn, args, _)          => go(fn) || args.exists(pattern)
        case ElabAst.TypePattern.Type(t)                   => go(t)
      }
    def binderType(bt: ElabAst.BinderType): Boolean =
      bt match {
        case ElabAst.BinderType.TypePattern(tp, _)            => pattern(tp)
        case ElabAst.BinderType.ConstrainedCapture(r, c, _) => ref(r) || pattern(c)
      }
    def go(t: ElabAst.Term): Boolean =
      t match {
        case Term.GlobalRef(_, _) | Term.LocalRef(_, _) | Term.NatLit(_, _) | Term.StrLit(_, _) => false
        case Term.Word(_, pieces, _) =>
          pieces.exists {
            case Term.WordPiece.Layer(before, after) => (before ++ after).exists(go)
            case Term.WordPiece.Splice(list)         => go(list)
          }
        case Term.Pi(binders, out, _, _, _) => binders.exists(b => ref(b.localRef) || binderType(b.ty)) || go(out)
        case Term.App(fn, args, _)          => go(fn) || args.exists(go)
        case Term.Proj(base, _, _, _, _)    => go(base)
        case Term.Body(lets, res, _)        => lets.exists(l => ref(l.localRef) || go(l.value) || l.ty.exists(go)) || go(res)
        case Term.Lam(ty, body, _, _, self, _, peers) =>
          self.exists(ref) || peers.exists(p => ref(p._1)) || go(ty) || go(body)
        case Match(scrut, motive, cases, _, _, _) =>
          go(scrut) || motive.exists(go) ||
            cases.exists(c => c.argRefs.exists(_.exists(ref)) || c.equation.exists(ref) || go(c.body))
      }
    go(term)
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
