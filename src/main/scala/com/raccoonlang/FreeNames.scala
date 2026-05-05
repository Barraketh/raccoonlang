package com.raccoonlang

import com.raccoonlang.CoreAst.Term.Match
import com.raccoonlang.CoreAst.{Ast, Term}
import org.roaringbitmap.RoaringBitmap

object FreeNames {

  final class LocalRefs private[FreeNames] (private[FreeNames] val bitmap: RoaringBitmap) {
    def foreachValueIn(env: Env)(f: Value => Unit): Unit = {
      val locals = env.locals
      val limit = locals.length
      val it = bitmap.getIntIterator
      var keepGoing = true
      while (keepGoing && it.hasNext) {
        val id = it.next()
        if (id < limit) f(locals(id))
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

  private def goList(terms: List[Ast], bound: RoaringBitmap, free: RoaringBitmap): Unit =
    terms.foreach(go(_, bound, free))

  private def go(term: CoreAst.Ast, bound: RoaringBitmap, free: RoaringBitmap): Unit =
    term match {
      case Term.GlobalRef(_, _) =>

      case Term.LocalRef(ref, _) =>
        if (!bound.contains(ref.id)) free.add(ref.id)

      case Term.Capture(_, ref, _) =>
        bound.add(ref.id)

      case Term.TApp(fn, args, _)   => goList((fn :: args).toList, bound, free)
      case Term.TSelect(base, _, _) => go(base, bound, free)

      case Term.PatternApp(fn, args, _) => goList((fn :: args).toList, bound, free)

      case Term.Pi(binders, out, _) =>
        binders.foreach { b =>
          go(b.ty, bound, free)
          b.localRef.foreach(r => bound.add(r.id))
        }
        go(out, bound, free)

      case Term.App(fn, args, _)   => goList((fn :: args).toList, bound, free)
      case Term.Select(base, _, _) => go(base, bound, free)

      case Term.Body(lets, res, _) =>
        lets.foreach { l =>
          val typeBound = bound.clone()
          go(l.value, bound, free)
          l.ty.foreach(t => go(t, typeBound, free))
          bound.add(l.localRef.id)
        }
        go(res, bound, free)

      case Term.Lam(ty, _, body, _, _, _) =>
        go(ty, bound, free)
        go(body, bound, free)

      case Match(scrut, motive, cases, _) =>
        go(scrut, bound, free)
        val caseBound = bound.clone()
        motive.foreach(go(_, bound, free))
        cases.foreach { c =>
          val nextBound = caseBound.clone()
          c.argRefs.flatten.foreach(ref => nextBound.add(ref.id))
          go(c.body, nextBound, free)
        }
    }

  def getFreeRefs(term: CoreAst.Ast, bound: LocalRefs = LocalRefs.empty): LocalRefs = {
    val free = new RoaringBitmap
    go(term, bound.bitmap.clone(), free)
    new LocalRefs(free)
  }

  def getDeps(term: Ast, env: Env, bound: LocalRefs = LocalRefs.empty): DepSet = {
    val deps = DepSet.newBuilder
    getFreeRefs(term, bound).foreachValueIn(env) { v =>
      deps.unionInPlace(v.synDeps)
    }
    deps.result()
  }
}
