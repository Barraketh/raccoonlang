package com.raccoonlang

import java.nio.file.Path
import scala.util.control.NoStackTrace

/** What went wrong, as plain data: no location, not throwable. `Diagnostic` carries it. */
sealed trait TypeError

/** How the checker reached a failure; appended by the boundary that knows it. */
sealed trait Frame

object Frame {

  /** The declaration whose checking was in progress. */
  final case class InDefinition(name: String) extends Frame

  /** An explicit argument of a call, numbered from 1 in source order. */
  final case class InArgument(index: Int, binder: String, callee: String) extends Frame

  /** One branch of a match, named by its constructor and the fields it binds. */
  final case class InBranch(ctor: String, args: Vector[String]) extends Frame
}

/**
 * The one thrown carrier. `span` and `frames` are filled in by boundaries while unwinding (`at`, `framed`), innermost
 * first; nothing is built on the success path.
 */
final case class Diagnostic(error: TypeError, span: Option[Span], frames: Vector[Frame])
  extends RuntimeException
  with NoStackTrace {

  override def getMessage: String = ErrorRendering.render(error)
}

final case class CannotApplyNonFunction(got: Value) extends TypeError

final case class ArityMismatch(expected: Int, got: Int) extends TypeError

final case class UnknownConstructor(ctor: String, inductive: String) extends TypeError

final case class DuplicateCase(ctor: String) extends TypeError

final case class UnreachableCase(ctor: String) extends TypeError

final case class MissingCase(ctor: String) extends TypeError

final case class VarAlreadyLinked(id: Long) extends TypeError

final case class NotAType(value: Value) extends TypeError

final case class NonInductiveMatch(tpe: Value) extends TypeError

final case class MissingReturningClause(reason: String) extends TypeError

final case class NotFound(name: String) extends TypeError

final case class AlreadyDefined(name: String) extends TypeError

final case class ReservedKernelName(name: String) extends TypeError

final case class NatLiteralUnavailable(reason: String) extends TypeError

final case class StringLiteralUnavailable(reason: String) extends TypeError

final case class NativeOperationDeclarationMismatch(name: String, reason: String) extends TypeError

final case class NativeOperationLimitExceeded(operation: String, argument: BigInt, limit: BigInt) extends TypeError

final case class AmbiguousName(name: String, candidates: Vector[String]) extends TypeError

final case class UnsupportedImport(path: String) extends TypeError

final case class ModuleNotFound(importPath: String, searchedPaths: Vector[Path]) extends TypeError

final case class CyclicImport(cycle: Vector[Path]) extends TypeError

final case class ModuleParseError(path: Path, message: String, offset: Int) extends TypeError

final case class ImportedModuleHasBody(path: Path) extends TypeError

final case class ModuleReadFailed(path: Path, reason: String) extends TypeError

final case class LocalCaseHead(name: String) extends TypeError

/** `detail` is the failure the conversion itself produced, never a second run that could disagree with it. */
final case class TypeMismatch(expected: Value, actual: Value, detail: Option[ValueEquivalence.UnifyFailure])
  extends TypeError

final case class NotALevel(v1: Value) extends TypeError

/** A broken kernel invariant, not a `TypeError`: keeps its stack trace and is reported as a kernel bug. */
final class InternalError(val reason: String) extends RuntimeException {
  private var located: Option[Span] = None

  /** Where the kernel was when the invariant broke, once a boundary has said so. */
  def span: Option[Span] = located

  /** Innermost span wins. Mutated rather than copied so the throw site's stack trace survives. */
  private[raccoonlang] def locate(span: Span): Unit = if (located.isEmpty) located = Some(span)

  override def getMessage: String = s"internal kernel error: $reason"
}

final case class InvalidConstructorResult(ctor: String, inductive: String, got: Value) extends TypeError

final case class NonForcedImplicitParam(param: String) extends TypeError

final case class ImplicitReconstructionFailed(param: String, fn: String, reason: String) extends TypeError

final case class NonUniformInductiveParam(inductive: String, ctor: String, param: String, got: Value) extends TypeError

final case class InductiveUniverseTooSmall(
    inductive: String,
    where: String,
    fieldTy: Value,
    fieldUniverse: Value.Level,
    inductiveUniverse: Value.Level
) extends TypeError

final case class InductiveTypeNotASort(tpe: Value) extends TypeError

final case class InvalidInductiveBlock(reason: String) extends TypeError

/** One family of a mutual block declared in a different universe from its siblings. */
final case class MutualBlockSortMismatch(family: String, declared: Value.VSort, expected: Value.VSort) extends TypeError

final case class NonStrictlyPositive(inductive: String, ctor: String, field: String, fieldTy: Value) extends TypeError

final case class PropEliminationRestricted(inductive: String, motive: Value) extends TypeError

final case class InvalidProjection(inductive: String, fieldIndex: Int, reason: String) extends TypeError

final case class InvalidDecreaseSpec(reason: String) extends TypeError

/** A decrease metric structural recursion cannot measure; `isProof` selects the reason. */
final case class NonInductiveDecreaseMetric(metric: Value, isProof: Boolean) extends TypeError

final case class NonDecreasingRecursiveCall(function: String, reason: String) extends TypeError

final case class InvalidRecursiveOccurrence(function: String) extends TypeError

final case class InvalidRecursiveGroup(reason: String) extends TypeError
