package com.raccoonlang

import com.raccoonlang.ElabAst.Term
import com.raccoonlang.ElabAst.Term.Match

object CapturedRefs {
  // This is not lexical free-variable analysis. When a closure is built, refs that are present in the current
  // environment are captures. Refs introduced inside the term being closed over are not present yet and are ignored.

  /**
   * Whether the term mentions any of the given refs. Same non-lexical convention as capture analysis: refs shadowed
   * inside the term still count, which is conservative for callers asking "is this type evaluable yet".
   */
  def mentions(term: ElabAst.Term, candidates: Set[CoreAst.LocalRef]): Boolean = {
    val env = candidates.foldLeft(Env.empty) { case (curEnv, ref) =>
      curEnv.putLocal(ref, Value.PropTpe)
    }
    goTerm(term, env, Set.empty).nonEmpty
  }

  private def addRef(ref: CoreAst.LocalRef, env: Env, refs: Set[CoreAst.LocalRef]): Set[CoreAst.LocalRef] =
    if (env.locals.contains(ref)) refs + ref else refs

  private def goTerms(
      terms: IterableOnce[ElabAst.Term],
      env: Env,
      refs: Set[CoreAst.LocalRef]
  ): Set[CoreAst.LocalRef] =
    terms.iterator.foldLeft(refs) { case (curRefs, term) => goTerm(term, env, curRefs) }

  private def goTerm(term: ElabAst.Term, env: Env, refs: Set[CoreAst.LocalRef]): Set[CoreAst.LocalRef] =
    term match {
      case _: Term.NatLit =>
        refs

      case Term.GlobalRef(_, _) =>
        refs

      case Term.LocalRef(ref, _) =>
        addRef(ref, env, refs)

      case Term.Pi(binders, out, _, _) =>
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

      case Term.Lam(ty, body, _, _, _, _) =>
        goTerm(body, env, goTerm(ty, env, refs))

      case Match(scrut, motive, cases, _, _) =>
        val refsWithScrut = goTerm(scrut, env, refs)
        val refsWithMotive = motive.fold(refsWithScrut)(goTerm(_, env, refsWithScrut))
        cases.foldLeft(refsWithMotive) { case (curRefs, c) => goTerm(c.body, env, curRefs) }
    }

  def getCapturedRefs(term: ElabAst.Term, env: Env): Set[CoreAst.LocalRef] =
    if (env.locals.isEmpty) Set.empty else goTerm(term, env, Set.empty)
}
