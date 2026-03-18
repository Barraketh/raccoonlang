package com.raccoonlang

import com.raccoonlang.Util.NEL
import com.raccoonlang.Value.{VApp, VBlockedApp, VConst, VarId}

object Normalizers {

  private def orderKey(v: Value): String = v match {
    case Value.VUniverse                  => "U"
    case Value.VConst(n, _, _)            => s"C:$n"
    case Value.Var(_, id, _)              => s"V:$id"
    case Value.VApp(h, args, _)           => s"A(${orderKey(h)};${args.toList.map(orderKey).mkString(",")})"
    case Value.VBlockedApp(h, args, _, _) => s"A(${orderKey(h)};${args.toList.map(orderKey).mkString(",")})"
    case Value.VLam(_, id, _, _) =>
      id match {
        case Value.LamId.Const(n)            => s"L:$n"
        case Value.LamId.LocalId(nodeId, ps) => s"L:$nodeId:${ps.map(orderKey).mkString(",")}"
      }
    case m: Value.VMatch => s"M:${m.id.nodeId}:${orderKey(m.scrut)}:${m.id.params.map(orderKey).mkString(",")}"
    case p: Value.VPi =>
      p.id match {
        case Value.LamId.Const(n)            => s"P:${p.binders.length}:$n"
        case Value.LamId.LocalId(nodeId, ps) => s"P:${p.binders.length}:$nodeId:${ps.map(orderKey).mkString(",")}"
      }
    case av: Value.AppliedValue =>
      s"A(${orderKey(av.head)};${av.args.toList.map(orderKey).mkString(",")})"
    case Value.NormalizerType => "NormalizerType"
    case n: Value.Normalizer  => s"Normalizer:${n.name}"
  }

  // Key to select a normalizer for a carrier type
  sealed trait CarrierKey
  object CarrierKey {
    final case class Head(name: String) extends CarrierKey
    final case class VarKey(id: VarId) extends CarrierKey
  }

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

      override def carrierKey: CarrierKey = ck

      private def flatten(v: Value): List[Value] = v match {
        case VBlockedApp(head, args, _, _) if head == addFn =>
          val l0 = flatten(args.head)
          val l1 = flatten(args.tail.head)
          l0 ++ l1
        case _ => List(v)
      }

      private def applyAdd(v1: Value, v2: Value)(implicit eqStore: EqStore): Value =
        Interpreter.evalApply(addFn, NEL(v1, v2 :: Nil))

      override def normalize(v: Value, eqStore: EqStore): Value = {
        val flattened = flatten(v).filter(v => v != zero).sortBy(v => orderKey(v))
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
