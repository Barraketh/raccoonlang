package com.raccoonlang

import com.raccoonlang.{CoreAst => CA}

/**
 * The ledger (spec §3.2): a local of linear type is used exactly once within the extent of its binder, whether a
 * lambda, a definition's parameters, a `let` or a match pattern binds it, `_` included. Uses are counted along each
 * path through the extent that takes one branch at every `match`, and a use is any occurrence. A lambda's body lies on
 * those paths at the lambda's position, so a use of an outer local inside a lambda is one use, by the lambda, there
 * (spec §3.3). A `match` with no branch ends every path through it, so it uses every linear local live at it.
 *
 * The checker hands the ledger each binder's residual extent once that extent has checked, and the ledger walks it only
 * for a binder of linear type; evaluation makes none of its checks. Whether a local is tracked is decided from its type
 * at its binder, so refinement in a branch never changes it. The walk is one exhaustive match over Core terms with no
 * wildcard arm, so a new term is a compile error here until it is counted.
 */
object Ledger {

  /**
   * What the paths through a term do with one local: whether some path that continues past the term does not use it,
   * its first use in source order, and the first use that is a second use on some path. Every use lies on some path; a
   * path that a branchless `match` ends does not continue past it.
   */
  private final case class Uses(unused: Boolean, first: Option[Span], reuse: Option[Span]) {

    /** This term, then `next`, on one path: each path through the one continues through each path through the other. */
    def andThen(next: Uses): Uses =
      Uses(
        unused && next.unused,
        first.orElse(next.first),
        reuse.orElse(if (first.isDefined) next.first else next.reuse)
      )

    /** The paths of two branches of one `match`. */
    def or(other: Uses): Uses = Uses(unused || other.unused, first.orElse(other.first), reuse.orElse(other.reuse))
  }

  private val none = Uses(unused = true, None, None)

  private val ended = Uses(unused = false, None, None)

  /**
   * Require `ref`, of type `tpe` at its binder, to be used exactly once along every path through `extent`, the terms
   * its binder scopes over in source order: a second use on some path is `LinearReused` there, and otherwise no use on
   * some path is `LinearUnused` at the binder (G8). A local of unrestricted type is not tracked, which is the fast
   * path.
   */
  def requireUsedOnce(ref: CA.LocalRef, tpe: Value, binderSpan: Span, extent: => Vector[CA.Term]): Unit =
    if (Linearity.isLinear(tpe)) {
      val paths = sequence(ref, extent)
      paths.reuse.foreach(span => at(span)(fail(LinearReused(ref.name))))
      if (paths.unused) at(binderSpan)(fail(LinearUnused(ref.name)))
    }

  private def sequence(ref: CA.LocalRef, terms: Vector[CA.Term]): Uses =
    terms.foldLeft(none)((paths, term) => paths.andThen(uses(ref, term)))

  private def uses(ref: CA.LocalRef, term: CA.Term): Uses =
    term match {
      case CA.Term.LocalRef(local, span) =>
        if (local == ref) Uses(unused = false, Some(span), None) else none
      // A lambda's children are its type and body: its `decreases` clause is not a use (spec §3.2).
      case _: CA.Term.GlobalRef | _: CA.Term.NatLit | _: CA.Term.StrLit | _: CA.Term.Select | _: CA.Term.Sort |
          _: CA.Term.FormOp | _: CA.Term.App | _: CA.Term.Pi | _: CA.Term.Body | _: CA.Term.Lam | _: CA.Term.Scope =>
        sequence(ref, CA.children(term))
      case CA.Term.Match(scrut, motive, cases, _) =>
        val branches = if (cases.isEmpty) ended else cases.map(c => uses(ref, c.body)).reduceLeft(_ or _)
        uses(ref, scrut).andThen(uses(ref, motive)).andThen(branches)
    }
}
