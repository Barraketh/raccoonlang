package com.raccoonlang

import com.raccoonlang.CoreAst.Term.Match
import com.raccoonlang.CoreAst.Term
import org.roaringbitmap.RoaringBitmap

object FreeNames {

  final class LocalRefs private[FreeNames] (private[FreeNames] val bitmap: RoaringBitmap) {
    def isEmpty: Boolean = bitmap.isEmpty

    def foreachValueIn(env: Env)(f: Value => Unit): Unit = {
      val locals = env.locals
      val limit = locals.length
      val it = bitmap.getIntIterator
      var keepGoing = true
      while (keepGoing && it.hasNext) {
        val id = it.next()
        if (id < limit) f(locals(id).value)
        else keepGoing = false
      }
    }

    def valuesIn(env: Env): Vector[Value] = {
      val values = Vector.newBuilder[Value]
      foreachValueIn(env)(values += _)
      values.result()
    }
  }

  object LocalRefs {
    val empty: LocalRefs = new LocalRefs(new RoaringBitmap)
  }

  private def goTerms(terms: IterableOnce[CoreAst.Term[_]], bound: RoaringBitmap, free: RoaringBitmap): Unit =
    terms.iterator.foreach(goTerm(_, bound, free))

  private def goPatterns(terms: IterableOnce[CoreAst.TypePattern[_]], bound: RoaringBitmap, free: RoaringBitmap): Unit =
    terms.iterator.foreach(goPattern(_, bound, free))

  private def goPattern(pattern: CoreAst.TypePattern[_], bound: RoaringBitmap, free: RoaringBitmap): Unit =
    pattern match {
      case CoreAst.TypePattern.Capture(ref, _) =>
        bound.add(ref.id)

      case CoreAst.TypePattern.App(fn, args, _) =>
        goTerm(fn, bound, free)
        goPatterns(args, bound, free)

      case CoreAst.TypePattern.Type(term) =>
        goTerm(term, bound, free)
    }

  private def goTerm(term: CoreAst.Term[_], bound: RoaringBitmap, free: RoaringBitmap): Unit =
    term match {
      case Term.GlobalRef(_, _) =>

      case Term.LocalRef(ref, _) =>
        if (!bound.contains(ref.id)) free.add(ref.id)

      case Term.TApp(fn, args, _)   => goTerms(fn +: args, bound, free)
      case Term.TSelect(base, _, _) => goTerm(base, bound, free)

      case Term.Pi(binders, out, _) =>
        binders.foreach { b =>
          goPattern(b.ty, bound, free)
          bound.add(b.localRef.id)
        }
        goTerm(out, bound, free)

      case Term.App(fn, args, _)   => goTerms(fn +: args, bound, free)
      case Term.Select(base, _, _) => goTerm(base, bound, free)

      case Term.Body(lets, res, _) =>
        lets.foreach { l =>
          val typeBound = bound.clone()
          goTerm(l.value, bound, free)
          l.ty.foreach(t => goTerm(t, typeBound, free))
          bound.add(l.localRef.id)
        }
        goTerm(res, bound, free)

      case Term.Lam(ty, _, body, _, _, _) =>
        goTerm(ty, bound, free)
        goTerm(body, bound, free)

      case Match(scrut, motive, cases, _) =>
        goTerm(scrut, bound, free)
        val caseBound = bound.clone()
        motive.foreach(goTerm(_, bound, free))
        cases.foreach { c =>
          val nextBound = caseBound.clone()
          c.argRefs.flatten.foreach(ref => nextBound.add(ref.id))
          goTerm(c.body, nextBound, free)
        }
    }

  def getFreeRefs(term: CoreAst.Term[_], bound: LocalRefs = LocalRefs.empty): LocalRefs = {
    val free = new RoaringBitmap
    goTerm(term, bound.bitmap.clone(), free)
    new LocalRefs(free)
  }

  def getDeps(term: CoreAst.Term[_], env: Env, bound: LocalRefs = LocalRefs.empty): DepSet = {
    val deps = DepSet.newBuilder
    getFreeRefs(term, bound).foreachValueIn(env) { v =>
      deps.unionInPlace(v.synDeps)
    }
    deps.result()
  }
}
