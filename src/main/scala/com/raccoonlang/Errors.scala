package com.raccoonlang

import java.nio.file.Path

sealed trait TypeError extends RuntimeException {
  def msg: String
  def span: Option[Span]

  /** The same error, located. Abstract so that adding an error class without it is a compile error. */
  def withSpan(sp: Span): TypeError

  override def getMessage: String = msg
}

final case class CannotApplyNonFunction(got: Value, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"Cannot apply non-fn type ${got}"
}

final case class ArityMismatch(expected: Int, got: Int, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"Cannot apply function - expected $expected params, got $got"
}

final case class UnknownConstructor(ctor: String, inductive: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"Constructor $ctor does not belong to $inductive"
}

final case class DuplicateCase(ctor: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"Duplicate case for constructor $ctor"
}

final case class UnreachableCase(ctor: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"Unreachable case for constructor $ctor"
}

final case class MissingCase(ctor: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override def msg: String = s"Missing case : $ctor"
}

final case class VarAlreadyLinked(id: Long, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"FreshVar $id already linked"
}

final case class NotAType(value: Value, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"$value is not a type"
}

final case class NonInductiveMatch(tpe: Value, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"Cannot match on non-inductive type $tpe"
}

final case class MissingReturningClause(reason: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"Match requires a returning clause: $reason"
}

final case class NotFound(name: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"$name not found"
}

final case class AlreadyDefined(name: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"$name already defined"
}

final case class ReservedKernelName(name: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"$name has a builtin body, which only a prelude may declare"
}

final case class NatLiteralUnavailable(reason: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"Nat literal unavailable: $reason"
}

final case class StringLiteralUnavailable(reason: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"String literal unavailable: $reason"
}

final case class NativeOperationDeclarationMismatch(name: String, reason: String, span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"Native operation declaration mismatch for $name: $reason"
}

final case class NativeOperationLimitExceeded(
    operation: String,
    argument: BigInt,
    limit: BigInt,
    span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"$operation argument $argument exceeds native evaluation limit $limit"
}

final case class AmbiguousName(name: String, candidates: Vector[String], span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"$name is ambiguous: ${candidates.mkString(", ")}"
}

final case class UnsupportedImport(path: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"Unresolved import $path; load files through ModuleLoader before elaboration"
}

final case class ModuleNotFound(importPath: String, searchedPaths: Vector[Path], span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"Module $importPath not found. Searched: ${searchedPaths.mkString(", ")}"
}

final case class CyclicImport(cycle: Vector[Path], span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"Cyclic import: ${cycle.map(_.toString).mkString(" -> ")}"
}

final case class ModuleParseError(path: Path, message: String, offset: Int, span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"Failed to parse module ${path.toString}: $message"
}

final case class ImportedModuleHasBody(path: Path, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"Imported module ${path.toString} must not contain a program body"
}

final case class ModuleReadFailed(path: Path, reason: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"Failed to read module ${path.toString}: $reason"
}

final case class LocalCaseHead(name: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String =
    s"Case head $name is local; unqualified case heads must resolve to globals. Use .$name for short-name matching."
}

final case class TypeMismatch(expected: Value, actual: Value, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg: String = s"Type mismatch: expected type: $expected, actual: $actual"
}

final case class NotALevel(v1: Value, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override def msg: String = s"$v1 is not a Level"
}

final case class WTF(msg: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
}

final case class InvalidConstructorResult(
    ctor: String,
    inductive: String,
    got: Value,
    span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String =
    s"Constructor $ctor must return $inductive but got $got"
}

final case class NonForcedImplicitParam(param: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String =
    s"Parameter $param cannot be implicit: it is not forced by the type of any later non-implicit parameter"
}

final case class ImplicitReconstructionFailed(
    param: String,
    fn: String,
    reason: String,
    span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String =
    s"Cannot reconstruct implicit argument $param of $fn: $reason"
}

final case class NonUniformInductiveParam(
    inductive: String,
    ctor: String,
    param: String,
    got: Value,
    span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
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
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String =
    s"Inductive $inductive lives in Sort $inductiveUniverse, but $where has type $fieldTy : Sort $fieldUniverse"
}

final case class InductiveTypeNotASort(tpe: Value, span: Option[Span]) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override def msg: String = s"Inductive type must be a Sort, got $tpe instead"
}

final case class InvalidInductiveBlock(reason: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override def msg: String = s"Invalid inductive block: $reason"
}

final case class NonStrictlyPositive(
    inductive: String,
    ctor: String,
    field: String,
    fieldTy: Value,
    span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String =
    s"Constructor $ctor of $inductive is not strictly positive in field $field : $fieldTy"
}

final case class PropEliminationRestricted(
    inductive: String,
    motive: Value,
    span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override def msg: String =
    s"Cannot eliminate proposition $inductive into non-Prop motive $motive"
}

final case class InvalidProjection(
    inductive: String,
    fieldIndex: Int,
    reason: String,
    span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override def msg: String = s"Invalid projection $inductive.$fieldIndex: $reason"
}

final case class InvalidDecreaseSpec(reason: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override def msg: String = s"Invalid decreases annotation: $reason"
}

final case class NonDecreasingRecursiveCall(function: String, reason: String, span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override def msg: String = s"Recursive call to $function is not decreasing: $reason"
}

final case class InvalidRecursiveOccurrence(function: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override def msg: String = s"Invalid recursive occurrence of $function"
}

final case class InvalidRecursiveGroup(reason: String, span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override def msg: String = s"Invalid recursive definition group: $reason"
}
