package com.raccoonlang

import com.raccoonlang.CoreAst.Term
import com.raccoonlang.CoreAst.Term.Match
import org.roaringbitmap.RoaringBitmap

object CapturedIndexes {
  // This is not lexical free-variable analysis. Core local ids are allocated densely and monotonically, so when a
  // closure is built, every ref to the current environment has id < env.locals.length. Locals introduced inside the
  // term being closed over have ids >= that cutoff and are intentionally ignored here.

  private def addRef(ref: CoreAst.LocalRef, cutoff: Int, refs: RoaringBitmap): Unit = {
    if (ref.id < cutoff) refs.add(ref.id)
  }

  private def goTerms(terms: IterableOnce[CoreAst.Term[_]], cutoff: Int, refs: RoaringBitmap): Unit =
    terms.iterator.foreach(goTerm(_, cutoff, refs))

  private def goPatterns(terms: IterableOnce[CoreAst.TypePattern[_]], cutoff: Int, refs: RoaringBitmap): Unit =
    terms.iterator.foreach(goPattern(_, cutoff, refs))

  private def goPattern(pattern: CoreAst.TypePattern[_], cutoff: Int, refs: RoaringBitmap): Unit =
    pattern match {
      case CoreAst.TypePattern.Capture(ref, _) =>
        addRef(ref, cutoff, refs)

      case CoreAst.TypePattern.App(fn, args, _) =>
        goTerm(fn, cutoff, refs)
        goPatterns(args, cutoff, refs)

      case CoreAst.TypePattern.Type(term) =>
        goTerm(term, cutoff, refs)
    }

  private def goTerm(term: CoreAst.Term[_], cutoff: Int, refs: RoaringBitmap): Unit =
    term match {
      case Term.GlobalRef(_, _) =>

      case Term.LocalRef(ref, _) =>
        addRef(ref, cutoff, refs)

      case Term.TApp(fn, args, _)   => goTerms(fn +: args, cutoff, refs)
      case Term.TSelect(base, _, _) => goTerm(base, cutoff, refs)

      case Term.Pi(binders, out, _) =>
        binders.foreach { b =>
          goPattern(b.ty, cutoff, refs)
        }
        goTerm(out, cutoff, refs)

      case Term.App(fn, args, _)   => goTerms(fn +: args, cutoff, refs)
      case Term.Select(base, _, _) => goTerm(base, cutoff, refs)

      case Term.Body(lets, res, _) =>
        lets.foreach { l =>
          goTerm(l.value, cutoff, refs)
          l.ty.foreach(t => goTerm(t, cutoff, refs))
        }
        goTerm(res, cutoff, refs)

      case Term.Lam(ty, _, body, _, _, _) =>
        goTerm(ty, cutoff, refs)
        goTerm(body, cutoff, refs)

      case Match(scrut, motive, cases, _) =>
        goTerm(scrut, cutoff, refs)
        motive.foreach(goTerm(_, cutoff, refs))
        cases.foreach { c =>
          goTerm(c.body, cutoff, refs)
        }
    }

  def getCapturedIndexes(term: CoreAst.Term[_], env: EnvLike[_]): RoaringBitmap = {
    val indexes = new RoaringBitmap
    if (env.locals.nonEmpty) {
      goTerm(term, env.locals.length, indexes)
    }
    indexes
  }
}
