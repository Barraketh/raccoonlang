package com.raccoonlang

import com.raccoonlang.CoreAst.Term

private[raccoonlang] object CoreSubstitution {
  def substitute(term: Term, replacements: Map[CoreAst.LocalRef, Term]): Term = {
    def freeRefs(root: Term): Set[CoreAst.LocalRef] = {
      val result = scala.collection.mutable.HashSet.empty[CoreAst.LocalRef]
      val pending = scala.collection.mutable.ArrayDeque((root, Set.empty[CoreAst.LocalRef]))
      while (pending.nonEmpty) {
        val (current, bound) = pending.removeLast()
        current match {
          case Term.LocalRef(local, _)                             => if (!bound(local)) result += local
          case _: Term.GlobalRef | _: Term.NatLit | _: Term.StrLit =>
          case Term.Select(base, _, _)                             => pending.append((base, bound))
          case Term.Proj(_, _, base, _)                            => pending.append((base, bound))
          case Term.App(fn, args, _) =>
            pending.append((fn, bound))
            args.foreach(arg => pending.append((arg, bound)))
          case Term.Pi(binders, out, _) =>
            var currentBound = bound
            binders.foreach { binder =>
              pending.append((binder.ty, currentBound))
              currentBound += binder.localRef
            }
            pending.append((out, currentBound))
          case Term.Lam(ty, body, _, _, recursion) =>
            pending.append((ty, bound))
            pending.append((body, bound ++ ty.binders.map(_.localRef) ++ recursion.map(_.selfRef)))
          case Term.Body(lets, res, _) =>
            var currentBound = bound
            lets.foreach { let =>
              let.ty.foreach(tpe => pending.append((tpe, currentBound)))
              pending.append((let.value, currentBound))
              currentBound += let.localRef
            }
            pending.append((res, currentBound))
          case Term.Match(scrut, motive, cases, _) =>
            pending.append((scrut, bound))
            motive.foreach(value => pending.append((value, bound)))
            cases.foreach(branch => pending.append((branch.body, bound ++ branch.argRefs.flatten)))
        }
      }
      result.toSet
    }

    val replacementFreeRefs = replacements.iterator.map { case (ref, replacement) =>
      ref -> freeRefs(replacement)
    }.toMap

    final case class Active(
        terms: Map[CoreAst.LocalRef, Term],
        freeRefCounts: Map[CoreAst.LocalRef, Int]
    ) {
      def without(refs: Iterable[CoreAst.LocalRef]): Active = {
        var nextTerms = terms
        var nextCounts = freeRefCounts
        refs.foreach { ref =>
          if (nextTerms.contains(ref)) {
            nextTerms -= ref
            replacementFreeRefs(ref).foreach { free =>
              val count = nextCounts(free)
              if (count == 1) nextCounts -= free else nextCounts += free -> (count - 1)
            }
          }
        }
        Active(nextTerms, nextCounts)
      }
    }

    val initialCounts = replacementFreeRefs.valuesIterator.flatten.foldLeft(Map.empty[CoreAst.LocalRef, Int]) {
      case (counts, ref) => counts.updated(ref, counts.getOrElse(ref, 0) + 1)
    }
    val initial = Active(replacements, initialCounts)

    def assertNoCapture(bound: Iterable[CoreAst.LocalRef], active: Active): Unit = {
      bound.find(active.freeRefCounts.contains).foreach { ref =>
        throw WTF(s"substitution would capture local ref $ref")
      }
    }

    def loop(current: Term, subst: Active): Term = current match {
      case ref @ Term.LocalRef(local, _)        => subst.terms.getOrElse(local, ref)
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
          active = active.without(Vector(binder.localRef))
          assertNoCapture(Vector(binder.localRef), active)
          next
        }
        Term.Pi(nextBinders, loop(out, active), span)
      case Term.Lam(ty, body, span, name, recursion) =>
        val nextTy = loop(ty, subst).asInstanceOf[Term.Pi]
        val bound = ty.binders.iterator.map(_.localRef).toSet ++ recursion.iterator.map(_.selfRef)
        val active = subst.without(bound)
        assertNoCapture(bound, active)
        Term.Lam(nextTy, loop(body, active), span, name, recursion)
      case Term.Body(lets, res, span) =>
        var active = subst
        val nextLets = lets.map { let =>
          val next = let.copy(ty = let.ty.map(loop(_, active)), value = loop(let.value, active))
          active = active.without(Vector(let.localRef))
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
            val active = subst.without(bound)
            assertNoCapture(bound, active)
            c.copy(body = loop(c.body, active))
          },
          span
        )
    }
    loop(term, initial)
  }
}
