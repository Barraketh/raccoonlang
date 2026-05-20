package com.raccoonlang

import com.raccoonlang.Value.{VApp, VBlockedApp, VConst, VarId}

object Normalizers {

  // Key to select a normalizer for a carrier type
  sealed trait CarrierKey
  object CarrierKey {
    final case class Head(name: String) extends CarrierKey
    final case class VarKey(id: VarId) extends CarrierKey
  }

  type NormalizerMap = Map[CarrierKey, Value.Normalizer]

  def getCarrierKey(v: Value): Option[CarrierKey] = v match {
    case VConst(name, _, _)             => Some(CarrierKey.Head(name))
    case VApp(VConst(name, _, _), _, _) => Some(CarrierKey.Head(name))
    case Value.Var(_, id, _)            => Some(CarrierKey.VarKey(id))
    case _                              => None
  }

  def add_normalizer(args: Vector[Value]): Value = {
    val ck = getCarrierKey(args(0)).get
    val zero = args(1)
    val addFn = args(2)

    new Value.Normalizer {
      override def name: String = "add_normalizer"

      override val dependencies: Vector[Value] = args

      override def carrierKey: CarrierKey = ck

      private def flatten(v: Value): List[Value] = v match {
        case VBlockedApp(head, args, _, _) if head == addFn =>
          val l0 = flatten(args.head)
          val l1 = flatten(args.tail.head)
          l0 ++ l1
        case _ => List(v)
      }

      private def applyAdd(v1: Value, v2: Value)(implicit eqStore: EqStore): Value =
        Interpreter.evalApply(addFn, Vector(v1, v2))

      override def normalize(v: Value, eqStore: EqStore): Value = {
        val flattened = flatten(v).filter(v => v != zero).sortBy(_.key)
        flattened match {
          case Nil         => zero
          case head :: Nil => head
          case h1 :: h2 :: tail =>
            tail.foldLeft(applyAdd(h1, h2)(eqStore)) { case (curVal, nextVal) =>
              applyAdd(curVal, nextVal)(eqStore)
            }
        }
      }
    }
  }
}
