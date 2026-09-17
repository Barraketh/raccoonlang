package com.raccoonlang.telescope

object Projection {
  sealed trait Step
  object Step {
    case object Tpe extends Step
    case class SpineArg(head: String, idx: Int) extends Step
    case class CtorField(ctor: String, idx: Int) extends Step
    case object SortLevel extends Step
    case class LevelOffset(k: Int) extends Step
    case class PiDomain(idx: Int) extends Step
    case object PiCodomain extends Step
    case object PiResult extends Step
  }
  final case class Spec(rootArgIdx: Int, steps: Vector[Step])
}
