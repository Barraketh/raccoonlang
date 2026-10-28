package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.packed.{Strings, Words}

/** Semantic construction and observation of data, independent of its stored representation. */
private[raccoonlang] object ConstructorValue {

  /**
   * Construct a checked constructor application: fields are its stored (non-erased) arguments and tpe is its result
   * type. Evaluation, branch freshening, and materialization establish those relationships before calling here. A cons
   * of a list-shaped type is a word, and a Nat successor is folded into compact form, so neither is stored as a `VApp`.
   * A closed character is interned, so equal closed characters are one value (see `Strings`).
   */
  def apply(head: ConstructorHead, fields: Vector[Value], tpe: Value): Value =
    head.listShape match {
      case Some(shape) => Words.cons(head, shape, fields, tpe)
      case None =>
        if (fields.length == 1 && head.name == Kernel.SuccName) NatNormalForm.successor(fields.head)
        else if (fields.length == 1 && head.name == Kernel.CharMkName) Strings.char(head, fields.head, tpe)
        else VCtor(head, fields, tpe)
    }

  /**
   * Observe a constructor and its stored fields; a word is its first layer with its tail, and a Nat form with a
   * positive constant is a successor. Constructor applications are never blocked, so any application of a constructor
   * head is a constructor value.
   */
  def unapply(value: Value): Option[(ConstructorHead, Vector[Value])] =
    value match {
      case VApp(head: ConstructorHead, fields, _, _) => Some((head, fields))
      case word: VWord                               => Some(Words.uncons(word))
      case poly: VNatPoly => NatNormalForm.predecessor(poly).map(predecessor => (Kernel.succ, Vector(predecessor)))
      case _              => None
    }
}
