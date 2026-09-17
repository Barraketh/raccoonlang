package com.raccoonlang

object CapturedRefs {
  private def goTerm(
      term: CoreAst.Term,
      candidates: Set[CoreAst.LocalRef],
      refs: Set[CoreAst.LocalRef]
  ): Set[CoreAst.LocalRef] =
    term match {
      case CoreAst.Term.LocalRef(ref, _) => if (candidates(ref)) refs + ref else refs
      case other =>
        CoreAst.children(other).foldLeft(refs) { case (current, child) => goTerm(child, candidates, current) }
    }

  def getCapturedRefs(term: CoreAst.Term, env: Env): Set[CoreAst.LocalRef] =
    if (env.locals.isEmpty) Set.empty
    else
      term match {
        case pi: CoreAst.Term.Pi   => pi.refs intersect env.localRefs
        case lam: CoreAst.Term.Lam => lam.refs intersect env.localRefs
        case m: CoreAst.Term.Match => m.refs intersect env.localRefs
        case other                 => goTerm(other, env.localRefs, Set.empty)
      }
}
