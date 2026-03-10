package com.raccoonlang

sealed trait TypeError extends RuntimeException {
  def msg: String
  def span: Option[Span]
  override def getMessage: String = msg
}

object TypeError {
  def withSpan(err: TypeError, sp: Span): TypeError = err match {
    case e: UnificationFailed      => e.copy(span = Some(sp))
    case e: OccursCheckFailed      => e.copy(span = Some(sp))
    case e: CannotApplyNonFunction => e.copy(span = Some(sp))
    case e: ArityMismatch          => e.copy(span = Some(sp))
    case e: UnknownConstructor     => e.copy(span = Some(sp))
    case e: DuplicateCase          => e.copy(span = Some(sp))
    case e: UnreachableCase        => e.copy(span = Some(sp))
    case e: MissingCase            => e.copy(span = Some(sp))
    case e: NotAType               => e.copy(span = Some(sp))
    case e: NonInductiveMatch      => e.copy(span = Some(sp))
    case e: NotFound               => e.copy(span = Some(sp))
    case e: AlreadyDefined         => e.copy(span = Some(sp))
    case e: GenericTypeError       => e.copy(span = Some(sp))
    case e: CannotLinkToBottom     => e.copy(span = Some(sp))
    case e: VarAlreadyLinked       => e.copy(span = Some(sp))
    case e: TypeMismatch           => e.copy(span = Some(sp))
    case e: BindEval               => e.copy(span = Some(sp))
  }
}

final case class UnificationFailed(v1: Interpreter.Value, v2: Interpreter.Value, span: Option[Span] = None)
  extends TypeError {
  val msg: String = s"Failed to unify $v1 and $v2"
}

final case class OccursCheckFailed(id: Long, inVal: Interpreter.Value, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Occurs check failed: $id in $inVal"
}

final case class CannotApplyNonFunction(got: Interpreter.Value, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Cannot apply non-fn type ${got}"
}

final case class ArityMismatch(expected: Int, got: Int, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Cannot apply function - expected $expected params, got $got"
}

final case class UnknownConstructor(ctor: String, inductive: String, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Constructor $ctor does not belong to $inductive"
}

final case class DuplicateCase(ctor: String, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Duplicate case for constructor $ctor"
}

final case class UnreachableCase(ctor: String, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Unreachable case for constructor $ctor"
}

final case class MissingCase(ctor: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Missing case : $ctor"
}

final case class VarAlreadyLinked(id: Long, span: Option[Span] = None) extends TypeError {
  val msg: String = s"FreshVar $id already linked"
}

final case class CannotLinkToBottom(id: Long, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Cannot link to bottom of chain for var $id"
}

final case class NotAType(value: Interpreter.Value, span: Option[Span] = None) extends TypeError {
  val msg: String = s"$value is not a type"
}

final case class NonInductiveMatch(tpe: Interpreter.Value, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Cannot match on non-inductive type $tpe"
}

final case class NotFound(name: String, span: Option[Span] = None) extends TypeError {
  val msg: String = s"$name not found"
}

final case class AlreadyDefined(name: String, span: Option[Span] = None) extends TypeError {
  val msg: String = s"$name already defined"
}

final case class GenericTypeError(msg: String, span: Option[Span] = None) extends TypeError

final case class TypeMismatch(v1: Interpreter.Value, v2: Interpreter.Value, span: Option[Span] = None)
  extends TypeError {
  val msg: String = s"Type mismatch: $v1 expected type: $v2, actual: ${v1.tpe}"
}

final case class BindEval(name: String, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Tried to evaluate bind $$$name"
}
