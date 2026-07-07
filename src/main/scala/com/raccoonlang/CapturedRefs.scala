package com.raccoonlang

import com.raccoonlang.ElabAst.Term
import com.raccoonlang.ElabAst.Term.Match

object CapturedRefs {
  // This is not lexical free-variable analysis. When a closure is built, refs that are present in the current
  // environment are captures. Refs introduced inside the term being closed over are not present yet and are ignored.

  private def addRef(ref: CoreAst.LocalRef, env: Env[Value], refs: Set[CoreAst.LocalRef]): Set[CoreAst.LocalRef] =
    if (env.locals.contains(ref)) refs + ref else refs

  private def goTerms(
      terms: IterableOnce[ElabAst.Term],
      env: Env[Value],
      refs: Set[CoreAst.LocalRef]
  ): Set[CoreAst.LocalRef] =
    terms.iterator.foldLeft(refs) { case (curRefs, term) => goTerm(term, env, curRefs) }

  private def goTerm(term: ElabAst.Term, env: Env[Value], refs: Set[CoreAst.LocalRef]): Set[CoreAst.LocalRef] =
    term match {
      case Term.GlobalRef(_, _) =>
        refs

      case Term.LocalRef(ref, _) =>
        addRef(ref, env, refs)

      case Term.Pi(binders, out, _, _, _) =>
        val refsWithBinders = binders.foldLeft(refs) { case (curRefs, b) => goTerm(b.ty, env, curRefs) }
        goTerm(out, env, refsWithBinders)

      case Term.App(fn, args, _) =>
        goTerms(fn +: args, env, refs)

      case Term.Body(lets, res, _) =>
        val refsWithLets = lets.foldLeft(refs) { case (curRefs, l) =>
          val refsWithValue = goTerm(l.value, env, curRefs)
          l.ty.fold(refsWithValue)(goTerm(_, env, refsWithValue))
        }
        goTerm(res, env, refsWithLets)

      case Term.Lam(ty, body, _, _, _) =>
        goTerm(body, env, goTerm(ty, env, refs))

      case Match(scrut, motive, cases, _) =>
        val refsWithScrut = goTerm(scrut, env, refs)
        val refsWithMotive = motive.fold(refsWithScrut)(goTerm(_, env, refsWithScrut))
        cases.foldLeft(refsWithMotive) { case (curRefs, c) => goTerm(c.body, env, curRefs) }
    }

  def getCapturedRefs(term: ElabAst.Term, env: Env[Value]): Set[CoreAst.LocalRef] =
    if (env.locals.isEmpty) Set.empty else goTerm(term, env, Set.empty)
}
