package com.raccoonlang

import com.raccoonlang.{CoreAst => CA}

/**
 * The ledger (spec §3.2): a local of linear type is used exactly once within the extent of its binder, whether a
 * lambda, a definition's parameters, a `let` or a match pattern binds it, `_` included. Uses are counted along each
 * path through the extent that takes one branch at every `match`, and a use is any occurrence. A `match` with no branch
 * ends every path through it, so it uses every linear local live at it, and nothing after it lies on those paths.
 *
 * A lambda or function type is a boundary: its body runs, if ever, when it is applied, so a path through its body
 * neither continues nor ends a path through the enclosing extent. One that mentions a local is one use of it, by the
 * lambda, at the lambda's position (spec §3.3), and its body must use the local on every path through it that
 * continues, and never twice on one path.
 *
 * The checker hands the ledger each binder's residual extent once that extent has checked, and the ledger walks it only
 * for a binder of linear type; evaluation makes none of its checks. Whether a local is tracked is decided from its type
 * at its binder, so refinement in a branch never changes it. The walk is one exhaustive match over Core terms with no
 * wildcard arm, so a new term is a compile error here until it is counted.
 */
object Ledger {

  /**
   * What the paths through a term do with one local: whether some path that continues past the term does not use it,
   * its first use on a path that continues, its first use on any path, and the first use that is a second use on some
   * path, each in source order. A path that a branchless `match` ends does not continue past it.
   */
  private final case class Uses(unused: Boolean, continuing: Option[Span], first: Option[Span], reuse: Option[Span]) {

    /** Whether some path continues past the term, since each such path either uses the local or does not. */
    def continues: Boolean = unused || continuing.isDefined

    /**
     * This term, then `next`, on one path: each path through this term that continues goes on through each path through
     * `next`, and the paths it ends reach nothing of `next`.
     */
    def andThen(next: Uses): Uses =
      if (!continues) this
      else
        Uses(
          unused && next.unused,
          continuing.filter(_ => next.continues).orElse(next.continuing),
          first.orElse(next.first),
          reuse.orElse(if (continuing.isDefined) next.first else None).orElse(next.reuse)
        )

    /** The paths of two branches of one `match`. */
    def or(other: Uses): Uses =
      Uses(
        unused || other.unused,
        continuing.orElse(other.continuing),
        first.orElse(other.first),
        reuse.orElse(other.reuse)
      )
  }

  private val none = Uses(unused = true, None, None, None)

  private val ended = Uses(unused = false, None, None, None)

  private def use(span: Span): Uses = Uses(unused = false, Some(span), Some(span), None)

  /**
   * Require `ref`, of type `tpe` at its binder, to be used exactly once along every path through `extent`, the terms
   * its binder scopes over in source order: a second use on some path is `LinearReused` there, and otherwise no use on
   * some path is `LinearUnused` at the binder. A local of unrestricted type is not tracked, which is the fast path.
   */
  def requireUsedOnce(ref: CA.LocalRef, tpe: Value, binderSpan: Span, extent: => Vector[CA.Term]): Unit =
    if (Linearity.isLinear(tpe)) {
      val paths = sequence(ref, extent)
      paths.reuse.foreach(span => at(span)(fail(LinearReused(ref.name))))
      if (paths.unused) at(binderSpan)(fail(LinearUnused(ref.name)))
    }

  private def sequence(ref: CA.LocalRef, terms: Vector[CA.Term]): Uses =
    terms.foldLeft(none)((paths, term) => paths.andThen(uses(ref, term)))

  /**
   * A lambda or function type `term`, with its cached `refs`, as the one path it is where it stands: no use when it
   * does not mention `ref`, and otherwise one use at its position. A path through its body that continues without using
   * `ref` still leaves it unused, and a second use on a path through its body is still a second use.
   */
  private def boundary(ref: CA.LocalRef, term: CA.Term, refs: Set[CA.LocalRef]): Uses =
    if (!refs(ref)) none
    else {
      val body = sequence(ref, CA.children(term))
      Uses(body.unused, Some(term.span), Some(term.span), body.reuse)
    }

  private def uses(ref: CA.LocalRef, term: CA.Term): Uses =
    term match {
      case CA.Term.LocalRef(local, span) => if (local == ref) use(span) else none
      case _: CA.Term.GlobalRef | _: CA.Term.NatLit | _: CA.Term.StrLit | _: CA.Term.Select | _: CA.Term.Sort |
          _: CA.Term.FormOp | _: CA.Term.App | _: CA.Term.Body | _: CA.Term.Scope =>
        sequence(ref, CA.children(term))
      case pi: CA.Term.Pi => boundary(ref, pi, pi.refs)
      // A lambda's children are its type and body: its `decreases` clause is not a use (spec §3.2).
      case lam: CA.Term.Lam                                    => boundary(ref, lam, lam.refs)
      case CA.Term.Match(scrut, motive, cases, wildcard, _, _) =>
        // The ledger reads residuals, and checking expands a wildcard into the cases it stands for.
        wildcard.foreach(w => wtf(s"An unexpanded wildcard case at ${w.span} reached the ledger"))
        val branches = if (cases.isEmpty) ended else cases.map(c => uses(ref, c.body)).reduceLeft(_ or _)
        uses(ref, scrut).andThen(uses(ref, motive)).andThen(branches)
    }
}
