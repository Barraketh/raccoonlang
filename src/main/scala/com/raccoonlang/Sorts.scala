package com.raccoonlang

import com.raccoonlang.Value.{Kind, Level, Lifetime, VPi, VSort}

/**
 * The one place sorts are built and classified (docs/kernel.md#universes-and-function-types). `VSort` is constructed
 * only here, read through its fields, and compared only by conversion. Whether a sort is `Prop`, and whether a type is
 * a proposition, is answered here and nowhere else, so proof irrelevance and the checker cannot disagree about it.
 */
object Sorts {

  /**
   * A sort. The checker has already refused a kind other than `Kind.unr` at a level that may be zero (`LinearProp`,
   * spec §2.3); substitution preserves both a level that is never zero and the kind `Kind.unr`, so no sort built later
   * breaks it either.
   */
  def sort(level: Level, kind: Kind, scope: Lifetime): VSort = {
    if (!admitsKind(level, kind)) wtf(s"Sort at level $level cannot have the kind $kind")
    new VSort(level, kind, scope)
  }

  val Prop: VSort = sort(Level.zero, Kind.unr, Lifetime.empty)
  val Type: VSort = sort(Level.one, Kind.unr, Lifetime.empty)

  /** A sort of a kind other than `Kind.unr` needs a level that is never zero, since proofs are unrestricted. */
  def admitsKind(level: Level, kind: Kind): Boolean = kind.isUnr || Level.isNeverZero(level)

  def isProp(sort: VSort): Boolean = sort.level == Level.zero

  /**
   * The type is a proposition: its values are proofs. A type in `Prop` is one, and so is a large function type into a
   * proposition (spec §2.4), whose instances are all propositions. A sort never qualifies, `Prop` included (`Prop :
   * Sort 1`): predicates are data, not proofs.
   */
  def isProposition(tpe: Value): Boolean =
    tpe match {
      case _: VSort => false
      // Impredicativity: a Pi is a proposition exactly when its codomain is Prop-valued, large or not. Answered
      // via the dedicated lazy val so proof canonicalization checks skip the full classifier computation.
      case pi: VPi => pi.isPropValued
      case tpe =>
        tpe.tpe match {
          case sort: VSort => isProp(sort)
          case _           => false
        }
    }
}
