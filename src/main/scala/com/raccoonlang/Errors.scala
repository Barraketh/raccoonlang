package com.raccoonlang

import com.raccoonlang.CoreAst.TypePattern

sealed trait TypeError extends RuntimeException {
  def msg: String
  def span: Option[Span]
  override def getMessage: String = msg
}

object TypeError {
  def withSpan(err: TypeError, sp: Span): TypeError = err match {
    case e: UnificationFailed               => e.copy(span = Some(sp))
    case e: OccursCheckFailed               => e.copy(span = Some(sp))
    case e: CannotApplyNonFunction          => e.copy(span = Some(sp))
    case e: ArityMismatch                   => e.copy(span = Some(sp))
    case e: UnknownConstructor              => e.copy(span = Some(sp))
    case e: DuplicateCase                   => e.copy(span = Some(sp))
    case e: UnreachableCase                 => e.copy(span = Some(sp))
    case e: MissingCase                     => e.copy(span = Some(sp))
    case e: NotAType                        => e.copy(span = Some(sp))
    case e: NonInductiveMatch               => e.copy(span = Some(sp))
    case e: MissingReturningClause          => e.copy(span = Some(sp))
    case e: NotFound                        => e.copy(span = Some(sp))
    case e: AlreadyDefined                  => e.copy(span = Some(sp))
    case e: CannotLinkToBottom              => e.copy(span = Some(sp))
    case e: VarAlreadyLinked                => e.copy(span = Some(sp))
    case e: TypeMismatch                    => e.copy(span = Some(sp))
    case e: DuplicateNormalizer             => e.copy(span = Some(sp))
    case e: InvalidConstructorResult        => e.copy(span = Some(sp))
    case e: NotALevel                       => e.copy(span = Some(sp))
    case e: InductiveUniverseTooSmall       => e.copy(span = Some(sp))
    case e: NonStrictlyPositive             => e.copy(span = Some(sp))
    case e: InductiveTypeNotASort           => e.copy(span = Some(sp))
    case e: PatternCaptureNeedsExpectedType => e.copy(span = Some(sp))
    case e: PatternHeadMismatch             => e.copy(span = Some(sp))
    case e: PatternArityMismatch            => e.copy(span = Some(sp))
    case e: PropEliminationRestricted       => e.copy(span = Some(sp))
    case e: LevelPatternMismatch            => e.copy(span = Some(sp))
    case e: WTF                             => e.copy(span = Some(sp))
    case e: InvalidStruct                   => e.copy(span = Some(sp))
    case e: NotAStruct                      => e.copy(span = Some(sp))
    case e: MultipleLevelCaptures           => e.copy(span = Some(sp))
    case e: UnknownNamedArgument            => e.copy(span = Some(sp))
    case e: DuplicateNamedArgument          => e.copy(span = Some(sp))
    case e: PositionalArgumentAfterNamed    => e.copy(span = Some(sp))
    case e: CannotCallAnonymousArgument     => e.copy(span = Some(sp))
    case e: NamedArgumentAlreadySupplied    => e.copy(span = Some(sp))
    case e: AmbiguousNamedArgument          => e.copy(span = Some(sp))

  }
}

final case class UnificationFailed(v1: Value, v2: Value, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Failed to unify $v1 and $v2"
}

final case class OccursCheckFailed(id: Long, inVal: Value, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Occurs check failed: $id in $inVal"
}

final case class CannotApplyNonFunction(got: Value, span: Option[Span] = None) extends TypeError {
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

final case class NotAType(value: Value, span: Option[Span] = None) extends TypeError {
  val msg: String = s"$value is not a type"
}

final case class NonInductiveMatch(tpe: Value, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Cannot match on non-inductive type $tpe"
}

final case class MissingReturningClause(reason: String, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Match requires a returning clause: $reason"
}

final case class NotFound(name: String, span: Option[Span] = None) extends TypeError {
  val msg: String = s"$name not found"
}

final case class AlreadyDefined(name: String, span: Option[Span] = None) extends TypeError {
  val msg: String = s"$name already defined"
}

final case class TypeMismatch(expected: Value, actual: Value, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Type mismatch: expected type: $expected, actual: $actual"
}

final case class DuplicateNormalizer(n: Normalizers.CarrierKey, span: Option[Span] = None) extends TypeError {
  override val msg: String = s"Normalizer for $n is already defined"
}

final case class NotALevel(v1: Value, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"$v1 is not a Level"
}

final case class PatternCaptureNeedsExpectedType(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Pattern capture $$$name needs an expected type"
}

final case class PatternHeadMismatch(expectedHead: Value, got: Value, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Pattern expected head $expectedHead, got $got"
}

final case class PatternArityMismatch(
    head: Value,
    expected: Int,
    got: Int,
    span: Option[Span] = None
) extends TypeError {
  override def msg: String = s"Pattern head $head expected $expected args, got $got"
}

final case class WTF(msg: String, span: Option[Span] = None) extends TypeError

final case class InvalidConstructorResult(
    ctor: String,
    inductive: String,
    got: Value,
    span: Option[Span] = None
) extends TypeError {
  override val msg: String =
    s"Constructor $ctor must return $inductive but got $got"
}

final case class InductiveUniverseTooSmall(
    inductive: String,
    where: String,
    fieldTy: Value,
    fieldUniverse: Value.Level,
    inductiveUniverse: Value.Level,
    span: Option[Span] = None
) extends TypeError {
  override val msg: String =
    s"Inductive $inductive lives in Sort $inductiveUniverse, but $where has type $fieldTy : Sort $fieldUniverse"
}

final case class InductiveTypeNotASort(tpe: Value, span: Option[Span]) extends TypeError {
  override def msg: String = s"Inductive type must be a Sort, got $tpe instead"
}

final case class NonStrictlyPositive(
    inductive: String,
    ctor: String,
    field: String,
    fieldTy: Value,
    span: Option[Span] = None
) extends TypeError {
  override val msg: String =
    s"Constructor $ctor of $inductive is not strictly positive in field $field : $fieldTy"
}

final case class PropEliminationRestricted(
    inductive: String,
    motive: Value,
    span: Option[Span] = None
) extends TypeError {
  override def msg: String =
    s"Cannot eliminate proposition $inductive into non-Prop motive $motive"
}

final case class MultipleLevelCaptures(p: TypePattern, span: Option[Span]) extends TypeError {
  override def msg: String = "Cannot pattern match multiple level captures "
}

final case class LevelPatternMismatch(p: TypePattern, v: Value, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Level pattern mismatch - expected $p, got $v"
}

final case class InvalidStruct(inductive: String, reason: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Invalid struct $inductive: $reason"
}

final case class NotAStruct(inductive: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Cannot select field from non-struct $inductive"
}

final case class UnknownNamedArgument(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Unknown named argument $name"
}

final case class DuplicateNamedArgument(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Duplicate named argument $name"
}

final case class PositionalArgumentAfterNamed(span: Option[Span] = None) extends TypeError {
  override def msg: String = "Positional arguments cannot follow named arguments"
}

final case class CannotCallAnonymousArgument(span: Option[Span] = None) extends TypeError {
  override def msg: String = "Anonymous parameter _ cannot be called by name"
}

final case class NamedArgumentAlreadySupplied(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Argument $name was already supplied by position"
}

final case class AmbiguousNamedArgument(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Named argument $name is ambiguous"
}
