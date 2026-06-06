package com.raccoonlang

import java.nio.file.Path

sealed trait TypeError extends RuntimeException {
  def msg: String
  def span: Option[Span]
  override def getMessage: String = msg
}

object TypeError {
  def withSpan(err: TypeError, sp: Span): TypeError = err match {
    case e: UnificationFailed               => e.copy(span = Some(sp))
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
    case e: InvalidErasedConstructorBinder  => e.copy(span = Some(sp))
    case e: NonUniformInductiveParam        => e.copy(span = Some(sp))
    case e: NotALevel                       => e.copy(span = Some(sp))
    case e: InductiveUniverseTooSmall       => e.copy(span = Some(sp))
    case e: NonStrictlyPositive             => e.copy(span = Some(sp))
    case e: InductiveTypeNotASort           => e.copy(span = Some(sp))
    case e: PatternCaptureNeedsExpectedType => e.copy(span = Some(sp))
    case e: PropEliminationRestricted       => e.copy(span = Some(sp))
    case e: WTF                             => e.copy(span = Some(sp))
    case e: InvalidStruct                   => e.copy(span = Some(sp))
    case e: NotAStruct                      => e.copy(span = Some(sp))
    case e: NoInstanceFound                 => e.copy(span = Some(sp))
    case e: CyclicInstanceSearch            => e.copy(span = Some(sp))
    case e: InvalidInstance                 => e.copy(span = Some(sp))
    case e: InstanceSearchBudgetExceeded    => e.copy(span = Some(sp))
    case e: AmbiguousName                   => e.copy(span = Some(sp))
    case e: UnsupportedImport               => e.copy(span = Some(sp))
    case e: ModuleNotFound                  => e.copy(span = Some(sp))
    case e: CyclicImport                    => e.copy(span = Some(sp))
    case e: ModuleParseError                => e.copy(span = Some(sp))
    case e: ImportedModuleHasBody           => e.copy(span = Some(sp))
    case e: ModuleReadFailed                => e.copy(span = Some(sp))
    case e: LocalCaseHead                   => e.copy(span = Some(sp))
    case e: CannotQuoteValue                => e.copy(span = Some(sp))
    case e: InvalidDecreaseSpec             => e.copy(span = Some(sp))
    case e: MissingDecreaseSpec             => e.copy(span = Some(sp))
    case e: NonDecreasingRecursiveCall      => e.copy(span = Some(sp))
    case e: InvalidRecursiveOccurrence      => e.copy(span = Some(sp))
  }
}

final case class UnificationFailed(v1: Value, v2: Value, span: Option[Span] = None) extends TypeError {
  val msg: String = s"Failed to unify $v1 and $v2"
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

final case class AmbiguousName(name: String, candidates: Vector[String], span: Option[Span] = None) extends TypeError {
  override val msg: String = s"$name is ambiguous: ${candidates.mkString(", ")}"
}

final case class UnsupportedImport(path: String, span: Option[Span] = None) extends TypeError {
  override val msg: String = s"Unresolved import $path; load files through ModuleLoader before elaboration"
}

final case class ModuleNotFound(importPath: String, searchedPaths: Vector[Path], span: Option[Span] = None)
  extends TypeError {
  override val msg: String = s"Module $importPath not found. Searched: ${searchedPaths.mkString(", ")}"
}

final case class CyclicImport(cycle: Vector[Path], span: Option[Span] = None) extends TypeError {
  override val msg: String = s"Cyclic import: ${cycle.map(_.toString).mkString(" -> ")}"
}

final case class ModuleParseError(path: Path, message: String, offset: Int, span: Option[Span] = None)
  extends TypeError {
  override val msg: String = s"Failed to parse module ${path.toString}: $message"
}

final case class ImportedModuleHasBody(path: Path, span: Option[Span] = None) extends TypeError {
  override val msg: String = s"Imported module ${path.toString} must not contain a program body"
}

final case class ModuleReadFailed(path: Path, reason: String, span: Option[Span] = None) extends TypeError {
  override val msg: String = s"Failed to read module ${path.toString}: $reason"
}

final case class LocalCaseHead(name: String, span: Option[Span] = None) extends TypeError {
  override val msg: String =
    s"Case head $name is local; unqualified case heads must resolve to globals. Use .$name for short-name matching."
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

final case class InvalidErasedConstructorBinder(
    ctor: String,
    binder: String,
    reason: String,
    span: Option[Span] = None
) extends TypeError {
  override val msg: String =
    s"Invalid erased constructor binder $binder in $ctor: $reason"
}

final case class NonUniformInductiveParam(
    inductive: String,
    ctor: String,
    param: String,
    got: Value,
    span: Option[Span] = None
) extends TypeError {
  override val msg: String =
    s"Constructor $ctor of $inductive returns non-uniform parameter $param as $got"
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

final case class InvalidStruct(inductive: String, reason: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Invalid struct $inductive: $reason"
}

final case class NotAStruct(inductive: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Cannot select field from non-struct $inductive"
}

final case class NoInstanceFound(goal: Value, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"No instance found for $goal"
}

final case class CyclicInstanceSearch(goal: Value, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Cyclic instance search for $goal"
}

final case class InvalidInstance(
    name: String,
    tpe: Value,
    reason: String = "non-searchable result type",
    span: Option[Span] = None
) extends TypeError {
  override def msg: String = s"Invalid instance $name: $reason in $tpe"
}

final case class InstanceSearchBudgetExceeded(
    goal: Value,
    maxDepth: Int,
    span: Option[Span] = None
) extends TypeError {
  override def msg: String = s"Instance search depth exceeded for $goal (max depth $maxDepth)"
}

final case class CannotQuoteValue(value: Value, reason: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Cannot quote $value as checked syntax: $reason"
}

final case class InvalidDecreaseSpec(reason: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Invalid decreases annotation: $reason"
}

final case class MissingDecreaseSpec(function: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Recursive call to $function requires a decreases annotation"
}

final case class NonDecreasingRecursiveCall(function: String, reason: String, span: Option[Span] = None)
  extends TypeError {
  override def msg: String = s"Recursive call to $function is not decreasing: $reason"
}

final case class InvalidRecursiveOccurrence(function: String, reason: String, span: Option[Span] = None)
  extends TypeError {
  override def msg: String = s"Invalid recursive occurrence of $function: $reason"
}
