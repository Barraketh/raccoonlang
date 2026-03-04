package com.raccoonlang

import com.raccoonlang.CoreAst.Term
import com.raccoonlang.CoreAst.Term.Match
import com.raccoonlang.Interpreter.Env

import scala.collection.immutable.BitSet

object FreeNames {

  private def getFreeNames(terms: List[Term], bound: Set[String]): Set[String] = {
    val l: List[Set[String]] = terms.map(tt => getFreeNames(tt, bound))
    l.reduce[Set[String]] { case (s1, s2) => s1.union(s2) }
  }

  private def getFreeNames(
      binders: List[(String, Term, Option[Term])],
      out: Term,
      bound: Set[String]
  ): Set[String] = {
    val (nextNames, nextBound) = binders.foldLeft((Set.empty[String], bound)) {
      case ((curNames, curBound), (name, t1, t2)) =>
        val n1 = getFreeNames(t1, curBound)
        val n2 = t2 match {
          case Some(t) => n1.union(getFreeNames(t, curBound))
          case None    => n1
        }
        (curNames.union(n2), curBound + name)
    }
    nextNames.union(getFreeNames(out, nextBound))
  }

  def getFreeNames(term: Term, bound: Set[String]): Set[String] = {
    term match {
      case Term.Ident(name, _)      => if (bound.contains(name)) Set.empty else Set(name)
      case Term.SortType(_, _)      => Set.empty
      case Term.SortProp(_)         => Set.empty
      case Term.TApp(fn, args, _)   => getFreeNames((fn :: args).toList, bound)
      case Term.Pi(binders, out, _) => getFreeNames(binders.toList.map(b => (b.name, b.ty, None)), out, bound)
      case Term.App(fn, args, _)    => getFreeNames((fn :: args).toList, bound)
      case Term.Body(lets, res, _)  => getFreeNames(lets.toList.map(l => (l.name, l.value, l.ty)), res, bound)
      case Term.Lam(ty, body, _, _) =>
        val tyNames = getFreeNames(ty, bound)
        val bodyBound = bound ++ ty.binders.map(_.name).toList
        tyNames.union(getFreeNames(body, bodyBound))
      case Match(scrut, scrutName, motive, cases, _) =>
        val n1 = getFreeNames(scrut, bound)
        val b1 = bound + scrutName
        val n2 = getFreeNames(motive, b1)
        val caseNames = cases.map(c => getFreeNames(c.body, b1 ++ c.argNames))
        (caseNames :+ n1 :+ n2).reduce[Set[String]] { case (s1, s2) => s1.union(s2) }
    }
  }

  def getDeps(term: Term, env: Env, bound: Set[String]): BitSet = {
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
