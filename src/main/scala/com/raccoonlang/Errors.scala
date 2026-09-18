package com.raccoonlang

sealed trait TypeError extends RuntimeException {
  def msg: String
  def span: Option[Span]
  def withSpan(sp: Span): TypeError
  override def getMessage: String = msg
}
final case class NotFound(name: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"$name not found"
}
final case class AlreadyDefined(name: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"$name already defined"
}
final case class TypeMismatch(expected: Value, actual: Value, override val span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Type mismatch: expected $expected, actual $actual"
}
final case class NotAType(value: Value, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"$value is not a type"
}
final case class CannotApplyNonFunction(got: Value, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Cannot apply non-function type $got"
}
final case class ArityMismatch(expected: Int, got: Int, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Expected $expected arguments, got $got"
}
final case class CoreInvariant(msg: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
}
final case class WTF(msg: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
}

final case class UnknownConstructor(ctor: String, inductive: String, override val span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Constructor $ctor does not belong to $inductive"
}
final case class DuplicateCase(ctor: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Duplicate case for constructor $ctor"
}
final case class UnreachableCase(ctor: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Unreachable case for constructor $ctor"
}
final case class MissingCase(ctor: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Missing case: $ctor"
}
final case class NonInductiveMatch(tpe: Value, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Cannot match on non-inductive type $tpe"
}
final case class MissingReturningClause(reason: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Match requires a returning clause: $reason"
}
final case class AmbiguousName(name: String, candidates: Vector[String], override val span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"$name is ambiguous: ${candidates.mkString(", ")}"
}
