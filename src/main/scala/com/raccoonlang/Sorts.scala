package com.raccoonlang

import com.raccoonlang.Value.{Large, Level, SortParameter, VPi, VSort}

/** Construction and classification of universe sorts. */
object Sorts {
  def sort(level: Level): VSort = new VSort(false, level)

  val Prop: VSort = new VSort(true, Level.zero)
  val Type: VSort = sort(Level.zero)

  def isProp(sort: VSort): Boolean = sort.isProp

  def sortOf(tpe: Value): Option[VSort] =
    tpe.tpe match {
      case sort: VSort           => Some(sort)
      case Large | SortParameter => None
      case classifier            => wtf(s"The type $tpe is classified by $classifier, which is no classifier")
    }

  def isProposition(tpe: Value): Boolean =
    tpe match {
      case _: VSort => false
      case pi: VPi  => pi.isPropValued
      case other    => sortOf(other).exists(isProp)
    }
}
