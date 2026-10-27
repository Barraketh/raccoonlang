package com.raccoonlang

import com.raccoonlang.Value._

/** Semantic construction and observation of data, independent of its stored representation. */
private[raccoonlang] object ConstructorValue {

  /**
   * Construct a checked constructor application: fields are its stored (non-erased) arguments and tpe is its result
   * type. Evaluation, branch freshening, and materialization establish those relationships before calling here. A Nat
   * successor is folded into compact form, so successors are never stored as constructors.
   */
  def apply(head: ConstructorHead, fields: Vector[Value], tpe: Value): Value =
    if (fields.length == 1 && head.name == Kernel.SuccName) NatNormalForm.successor(fields.head)
    else VCtor(head, fields, tpe)

  /**
   * Observe a constructor and its stored fields; a Nat form with a positive constant is a successor. Constructor
   * applications are never blocked, so any application of a constructor head is a constructor value.
   */
  def unapply(value: Value): Option[(ConstructorHead, Vector[Value])] =
    value match {
      case VApp(head: ConstructorHead, fields, _, _) => Some((head, fields))
      case poly: VNatPoly => NatNormalForm.predecessor(poly).map(predecessor => (Kernel.succ, Vector(predecessor)))
      case _              => None
    }
}
