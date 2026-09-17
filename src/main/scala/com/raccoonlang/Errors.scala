package com.raccoonlang

sealed trait TypeError extends RuntimeException { def msg: String; override def getMessage: String = msg }
final case class NotFound(name: String) extends TypeError { val msg = s"$name not found" }
final case class AlreadyDefined(name: String) extends TypeError { val msg = s"$name already defined" }
final case class TypeMismatch(expected: Value, actual: Value) extends TypeError {
  val msg = s"Type mismatch: expected $expected, actual $actual"
}
final case class NotAType(value: Value) extends TypeError { val msg = s"$value is not a type" }
final case class CannotApplyNonFunction(got: Value) extends TypeError {
  val msg = s"Cannot apply non-function type $got"
}
final case class ArityMismatch(expected: Int, got: Int) extends TypeError {
  val msg = s"Expected $expected arguments, got $got"
}
final case class CoreInvariant(msg: String) extends TypeError
final case class WTF(msg: String) extends TypeError
