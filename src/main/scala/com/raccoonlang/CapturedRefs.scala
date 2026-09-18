package com.raccoonlang

import com.raccoonlang.CoreAst.Term

object CapturedRefs {
  // This is not lexical free-variable analysis. When a closure is built, refs that are present in the current
  // environment are captures. Refs introduced inside the term being closed over are not present yet and are ignored.

  private def goTerm(
      term: CoreAst.Term,
      candidates: Set[CoreAst.LocalRef],
      refs: Set[CoreAst.LocalRef]
  ): Set[CoreAst.LocalRef] =
    term match {
      case Term.LocalRef(ref, _) => if (candidates(ref)) refs + ref else refs

      case other =>
        CoreAst.children(other).foldLeft(refs) { case (curRefs, child) => goTerm(child, candidates, curRefs) }
    }

  /**
   * The refs of `term` that the env already binds.
   *
   * Closure-creating nodes (Pi, Lam, Match) cache the set of refs they mention, so their captures are one intersection
   * rather than a fresh walk of the whole body per closure built — the same term is closed over on every evaluation of
   * its enclosing function. Any other node still walks, since nothing caches it.
   */
  def getCapturedRefs(term: CoreAst.Term, env: Env): Set[CoreAst.LocalRef] =
    if (env.locals.isEmpty) Set.empty
    else
      term match {
        case pi: Term.Pi   => pi.refs intersect env.localRefs
        case lam: Term.Lam => lam.refs intersect env.localRefs
        case m: Term.Match => m.refs intersect env.localRefs
        case other         => goTerm(other, env.localRefs, Set.empty)
      }
}
