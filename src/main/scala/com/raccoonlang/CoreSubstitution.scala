package com.raccoonlang

import com.raccoonlang.CoreAst.Term

private[raccoonlang] object CoreSubstitution {
  def substitute(term: Term, replacements: Map[CoreAst.LocalRef, Term]): Term = {
    def freeRefs(current: Term, bound: Set[CoreAst.LocalRef] = Set.empty): Set[CoreAst.LocalRef] = current match {
      case Term.LocalRef(local, _)                             => if (bound(local)) Set.empty else Set(local)
      case _: Term.GlobalRef | _: Term.NatLit | _: Term.StrLit => Set.empty
      case Term.Select(base, _, _)                             => freeRefs(base, bound)
      case Term.Proj(_, _, base, _)                            => freeRefs(base, bound)
      case Term.App(fn, args, _) =>
        args.foldLeft(freeRefs(fn, bound)) { case (refs, arg) => refs ++ freeRefs(arg, bound) }
      case Term.Pi(binders, out, _) =>
        var currentBound = bound
        val inBinders = binders.foldLeft(Set.empty[CoreAst.LocalRef]) { case (refs, binder) =>
          val next = refs ++ freeRefs(binder.ty, currentBound)
          currentBound += binder.localRef
          next
        }
        inBinders ++ freeRefs(out, currentBound)
      case Term.Lam(ty, body, _, _, recursion) =>
        val lambdaBound = bound ++ ty.binders.map(_.localRef) ++ recursion.map(_.selfRef)
        freeRefs(ty, bound) ++ freeRefs(body, lambdaBound)
      case Term.Body(lets, res, _) =>
        var currentBound = bound
        val inLets = lets.foldLeft(Set.empty[CoreAst.LocalRef]) { case (refs, let) =>
          val next = refs ++ let.ty.fold(Set.empty[CoreAst.LocalRef])(ty => freeRefs(ty, currentBound)) ++
            freeRefs(let.value, currentBound)
          currentBound += let.localRef
          next
        }
        inLets ++ freeRefs(res, currentBound)
      case Term.Match(scrut, motive, cases, _) =>
        val roots = freeRefs(scrut, bound) ++ motive.fold(Set.empty[CoreAst.LocalRef])(term => freeRefs(term, bound))
        cases.foldLeft(roots) { case (refs, branch) =>
          refs ++ freeRefs(branch.body, bound ++ branch.argRefs.flatten)
        }
    }

    def assertNoCapture(bound: Iterable[CoreAst.LocalRef], active: Map[CoreAst.LocalRef, Term]): Unit = {
      val free = active.valuesIterator.flatMap(term => freeRefs(term)).toSet
      bound.find(ref => free(ref)).foreach { ref =>
        throw new IllegalArgumentException(s"substitution would capture local ref $ref")
      }
    }

    def loop(current: Term, subst: Map[CoreAst.LocalRef, Term]): Term = current match {
      case ref @ Term.LocalRef(local, _)        => subst.getOrElse(local, ref)
      case ref: Term.GlobalRef                  => ref
      case lit: Term.NatLit                     => lit
      case lit: Term.StrLit                     => lit
      case Term.Select(base, field, span)       => Term.Select(loop(base, subst), field, span)
      case Term.Proj(family, index, base, span) => Term.Proj(family, index, loop(base, subst), span)
      case Term.App(fn, args, span)             => Term.App(loop(fn, subst), args.map(loop(_, subst)), span)
      case Term.Pi(binders, out, span) =>
        var active = subst
        val nextBinders = binders.map { binder =>
          val next = binder.copy(ty = loop(binder.ty, active))
          active -= binder.localRef
          assertNoCapture(Vector(binder.localRef), active)
          next
        }
        Term.Pi(nextBinders, loop(out, active), span)
      case Term.Lam(ty, body, span, name, recursion) =>
        val nextTy = loop(ty, subst).asInstanceOf[Term.Pi]
        val bound = ty.binders.iterator.map(_.localRef).toSet ++ recursion.iterator.map(_.selfRef)
        val active = subst -- bound
        assertNoCapture(bound, active)
        Term.Lam(nextTy, loop(body, active), span, name, recursion)
      case Term.Body(lets, res, span) =>
        var active = subst
        val nextLets = lets.map { let =>
          val next = let.copy(ty = let.ty.map(loop(_, active)), value = loop(let.value, active))
          active -= let.localRef
          assertNoCapture(Vector(let.localRef), active)
          next
        }
        Term.Body(nextLets, loop(res, active), span)
      case Term.Match(scrut, motive, cases, span) =>
        Term.Match(
          loop(scrut, subst),
          motive.map(loop(_, subst)),
          cases.map { c =>
            val bound = c.argRefs.flatten.toSet
            val active = subst -- bound
            assertNoCapture(bound, active)
            c.copy(body = loop(c.body, active))
          },
          span
        )
    }
    loop(term, replacements)
  }
}
