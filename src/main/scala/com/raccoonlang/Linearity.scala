package com.raccoonlang

import com.raccoonlang.Value.{Kind, VPi, VSort}

/**
 * Which types are linear (spec §3.1): the one answer, read off a type's sort as its scope is, never off a family's
 * fields. The ledger (Ledger) and every later linearity rule ask here.
 */
object Linearity {

  /**
   * A type is linear when its kind is not `Kind.unr`: `Kind.lin`, or a kind involving a variable, which some
   * instantiation makes `lin`. A function type's kind is its closure kind, read without forcing its classifier; any
   * other type's is its sort's. Sorts and propositions are at `Kind.unr`, and a sort parameter is not a type. Until a
   * kind other than `Kind.unr` has been built no type is linear, which is the fast path of every linearity rule.
   */
  def isLinear(tpe: Value): Boolean =
    Kind.anyNonUnr && (tpe match {
      case pi: VPi  => !pi.closureKind.isUnr
      case _: VSort => false
      case other    => Sorts.sortOf(other).exists(!_.kind.isUnr)
    })
}
