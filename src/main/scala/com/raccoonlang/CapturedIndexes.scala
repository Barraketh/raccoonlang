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
      case ElabAst.TypePattern.Capture(ref, _) =>
        addRef(ref, cutoff, refs)

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

      case Term.Pi(binders, out, _, _) =>
        binders.foreach { b =>
          goBinderType(b.ty, cutoff, refs)
        }
        goTerm(out, cutoff, refs)

      case Term.App(fn, args, _) => goTerms(fn +: args, cutoff, refs)

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

  def getCapturedIndexes(term: ElabAst.Term, env: Env): RoaringBitmap = {
    val indexes = new RoaringBitmap
    if (env.locals.nonEmpty) {
      goTerm(term, env.locals.length, indexes)
    }
    indexes
  }
}
