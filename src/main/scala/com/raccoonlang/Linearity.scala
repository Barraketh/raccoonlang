package com.raccoonlang

import com.raccoonlang.Value.{Large, SortParameter, VPi, VSort}

/**
 * Which types are linear (spec §3.1): the one answer, read off a type's sort as its scope is, never off a family's
 * fields. The ledger (Ledger) and every later linearity rule ask here.
 */
object Linearity {

  /**
   * A type is linear when its kind is not `Kind.unr`: `Kind.lin`, or a kind involving a variable, which some
   * instantiation makes `lin`. A function type's kind is its closure kind, read without forcing its classifier; any
   * other type's is its sort's. Sorts and propositions are at `Kind.unr`, and a sort parameter is not a type.
   */
  def isLinear(tpe: Value): Boolean =
    tpe match {
      case pi: VPi => !pi.closureKind.isUnr
      case other =>
        other.tpe match {
          case sort: VSort           => !sort.kind.isUnr
          case Large | SortParameter => false
          case classifier            => wtf(s"The type $other is classified by $classifier, which is no classifier")
        }
    }
}
