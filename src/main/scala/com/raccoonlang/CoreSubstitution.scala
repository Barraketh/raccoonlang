package com.raccoonlang

import com.raccoonlang.CoreAst.Term

private[raccoonlang] object CoreSubstitution {
  def substitute(term: Term, replacements: Map[CoreAst.LocalRef, Term]): Term = {
    def loop(current: Term, subst: Map[CoreAst.LocalRef, Term]): Term = current match {
      case ref @ Term.LocalRef(local, _) => subst.getOrElse(local, ref)
      case ref: Term.GlobalRef => ref
      case lit: Term.NatLit => lit
      case lit: Term.StrLit => lit
      case Term.Select(base, field, span) => Term.Select(loop(base, subst), field, span)
      case Term.Proj(family, index, base, span) => Term.Proj(family, index, loop(base, subst), span)
      case Term.App(fn, args, span) => Term.App(loop(fn, subst), args.map(loop(_, subst)), span)
      case Term.Pi(binders, out, span) =>
        var active = subst
        val nextBinders = binders.map { binder =>
          val next = binder.copy(ty = loop(binder.ty, active))
          active -= binder.localRef
          next
        }
        Term.Pi(nextBinders, loop(out, active), span)
      case Term.Lam(ty, body, span, name, recursion) =>
        val nextTy = loop(ty, subst).asInstanceOf[Term.Pi]
        val bound = ty.binders.iterator.map(_.localRef).toSet ++ recursion.iterator.map(_.selfRef)
        Term.Lam(nextTy, loop(body, subst -- bound), span, name, recursion)
      case Term.Body(lets, res, span) =>
        var active = subst
        val nextLets = lets.map { let =>
          val next = let.copy(ty = let.ty.map(loop(_, active)), value = loop(let.value, active))
          active -= let.localRef
          next
        }
        Term.Body(nextLets, loop(res, active), span)
      case Term.Match(scrut, motive, cases, span) =>
        Term.Match(
          loop(scrut, subst),
          motive.map(loop(_, subst)),
          cases.map { c =>
            val bound = c.argRefs.flatten.toSet
            c.copy(body = loop(c.body, subst -- bound))
          },
          span
        )
    }
    loop(term, replacements)
  }
}
