package com.raccoonlang

object CapturedRefs {

  /**
   * The refs of `term` that the env already binds.
   *
   * `mentionedRefs` uses the cached ref sets on closure-creating nodes and walks other nodes through the shared AST
   * traversal. Refs introduced inside the term are not in the env yet, so intersecting with its locals gives exactly
   * the captures.
   */
  def getCapturedRefs(term: CoreAst.Term, env: Env): Set[CoreAst.LocalRef] =
    if (env.localRefs.isEmpty) Set.empty
    else CoreAst.mentionedRefs(term) intersect env.localRefs
}
