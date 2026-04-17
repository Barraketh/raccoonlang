package com.raccoonlang

import com.raccoonlang.CoreAst.Term.Match
import com.raccoonlang.CoreAst.{Ast, Term}

import scala.collection.immutable.BitSet

object FreeNames {

  // Threaded traversal: returns (freeNames, updatedBound)
  private def goList(terms: List[Ast], bound0: Set[String]): (Set[String], Set[String]) = {
    terms.foldLeft((Set.empty[String], bound0)) { case ((curFree, curBound), t) =>
      val (f, b) = go(t, curBound)
      (curFree union f, b)
    }
  }

  private def go(term: CoreAst.Ast, bound: Set[String]): (Set[String], Set[String]) = {
    term match {
      case Term.Ident(name, _) =>
        (if (bound.contains(name)) Set.empty else Set(name), bound)

      case Term.Capture(name, _) =>
        // Captures introduce a bound variable for the remainder of the traversal
        (Set.empty, bound + name)

      case Term.TApp(fn, args, _)   => goList(fn :: args.toList.map(_.value), bound)
      case Term.TSelect(base, _, _) => go(base, bound)

      case Term.PatternApp(fn, args, _) => goList(fn :: args.toList.map(_.value), bound)

      case Term.Pi(binders, out, _) =>
        // Each binder: evaluate its type with current bound; then add binder name to bound
        val (freeFromBinders, boundAfterBinders) = binders.toList.foldLeft((Set.empty[String], bound)) {
          case ((curFree, curBound), b) =>
            val (fTy, bAfterTy) = go(b.ty, curBound)
            (curFree union fTy, bAfterTy + b.name)
        }
        val (freeOut, boundAfterOut) = go(out, boundAfterBinders)
        (freeFromBinders union freeOut, boundAfterOut)

      case Term.App(fn, args, _)   => goList(fn :: args.toList.map(_.value), bound)
      case Term.Select(base, _, _) => go(base, bound)

      case Term.Body(lets, res, _) =>
        val (freeLets, boundAfterLets) = lets.toList.foldLeft((Set.empty[String], bound)) {
          case ((curFree, curBound), l) =>
            val (fVal, b1) = go(l.value, curBound)
            val fTy = l.ty.map(t => go(t, curBound)._1).getOrElse(Set.empty[String])
            (curFree union fVal union fTy, b1 + l.name)
        }
        val (freeRes, boundAfterRes) = go(res, boundAfterLets)
        (freeLets union freeRes, boundAfterRes)

      case Term.Lam(ty, _, body, _, _, _) =>
        val (freeTy, boundAfterTy) = go(ty, bound)
        val (freeBody, boundAfterBody) = go(body, boundAfterTy)
        (freeTy union freeBody, boundAfterBody)

      case Match(scrut, motive, cases, _) =>
        val (freeScrut, b1) = go(scrut, bound)
        val (freeMotive, b2) = motive.map(go(_, b1)).getOrElse((Set.empty[String], b1))
        val freeCases = cases.foldLeft(Set.empty[String]) { case (curFree, c) =>
          val (fCase, _) = go(c.body, b1 ++ c.argNames)
          curFree union fCase
        }
        (freeScrut union freeMotive union freeCases, b2)
    }
  }

  def getFreeNames(term: CoreAst.Ast, bound: Set[String]): Set[String] = go(term, bound)._1

  def getDeps(term: Ast, env: Env, bound: Set[String]): BitSet = {
    val freeNames = FreeNames.getFreeNames(term, bound)
    val deps = collection.mutable.BitSet()
    freeNames.foreach { name =>
      env.findLocal(name).foreach { v =>
        deps |= v.synDeps
      }
    }
    deps.toImmutable
  }

}
