package com.raccoonlang

import java.nio.file.Path

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
final case class ReservedKernelName(name: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"$name has a builtin body, which only a prelude may declare"
}
final case class NatLiteralUnavailable(reason: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"Native Nat literals unavailable: $reason"
}
final case class StringLiteralUnavailable(reason: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"Native String literals unavailable: $reason"
}
final case class NativeOperationDeclarationMismatch(
    operation: String,
    reason: String,
    override val span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"Native operation $operation has an invalid declaration: $reason"
}
final case class NativeOperationLimitExceeded(
    operation: String,
    argument: BigInt,
    limit: BigInt,
    override val span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  override val msg: String = s"$operation argument $argument exceeds native limit $limit"
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
final case class NotALevel(value: Value, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"$value is not a universe level"
}
final case class CannotApplyNonFunction(got: Value, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Cannot apply non-function type $got"
}
final case class ArityMismatch(expected: Int, got: Int, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Expected $expected arguments, got $got"
}
final case class NonForcedImplicitParam(param: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Parameter $param cannot be implicit: it is not forced by a later explicit parameter"
}
final case class ImplicitReconstructionFailed(
    param: String,
    fn: String,
    reason: String,
    override val span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Cannot reconstruct implicit argument $param of $fn: $reason"
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
final case class PropEliminationRestricted(inductive: String, motive: Value, override val span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Cannot eliminate proposition $inductive into data motive $motive without proof recovery"
}
final case class AmbiguousName(name: String, candidates: Vector[String], override val span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"$name is ambiguous: ${candidates.mkString(", ")}"
}

final case class LocalCaseHead(name: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Match case head $name cannot be a local"
}

final case class UnsupportedImport(name: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Unresolved import $name; load files through ModuleLoader before elaboration"
}

final case class ModuleNotFound(importPath: String, searchedPaths: Vector[Path], override val span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Module $importPath not found. Searched: ${searchedPaths.mkString(", ")}"
}

final case class CyclicImport(cycle: Vector[Path], override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Cyclic import: ${cycle.map(_.toString).mkString(" -> ")}"
}

final case class ModuleParseError(path: Path, message: String, offset: Int, override val span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Failed to parse module ${path.toString}: $message"
}

final case class ImportedModuleHasBody(path: Path, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Imported module ${path.toString} must not contain a program body"
}

final case class ModuleReadFailed(path: Path, reason: String, override val span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Failed to read module ${path.toString}: $reason"
}

final case class InvalidConstructorResult(
    ctor: String,
    inductive: String,
    got: Value,
    override val span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Constructor $ctor must return $inductive but got $got"
}
final case class NonUniformInductiveParam(
    inductive: String,
    ctor: String,
    param: String,
    got: Value,
    override val span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Constructor $ctor of $inductive returns non-uniform parameter $param as $got"
}
final case class InductiveUniverseTooSmall(
    inductive: String,
    where: String,
    fieldTy: Value,
    fieldUniverse: Value.Level,
    inductiveUniverse: Value.Level,
    override val span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Inductive $inductive lives in Sort $inductiveUniverse, but $where has type $fieldTy : Sort $fieldUniverse"
}
final case class InductiveTypeNotASort(tpe: Value, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Inductive type must be a Sort, got $tpe instead"
}
final case class InvalidInductiveBlock(reason: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Invalid inductive block: $reason"
}
final case class InvalidRecursiveGroup(reason: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Invalid recursive definition group: $reason"
}
final case class InvalidDecreaseSpec(reason: String, override val span: Option[Span] = None) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Invalid decreases annotation: $reason"
}
final case class NonDecreasingRecursiveCall(function: String, reason: String, override val span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Recursive call to $function is not decreasing: $reason"
}
final case class InvalidRecursiveOccurrence(function: String, override val span: Option[Span] = None)
  extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Invalid recursive occurrence of $function"
}
final case class NonStrictlyPositive(
    inductive: String,
    ctor: String,
    field: String,
    fieldTy: Value,
    override val span: Option[Span] = None
) extends TypeError {
  override def withSpan(sp: Span): TypeError = copy(span = Some(sp))
  val msg = s"Constructor $ctor of $inductive is not strictly positive in field $field : $fieldTy"
}
