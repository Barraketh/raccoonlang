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

/** A sort of a kind other than `Kind.unr` at a level that may be zero (spec §2.3): proofs are unrestricted. */
final case class LinearProp(kind: Value.Kind, level: Value.Level) extends TypeError

/** A declared kind that does not contain the kind of `part` (spec §2.6), such as a family's constructor field. */
final case class KindExceeded(declaration: String, declared: Value.Kind, part: String, partKind: Value.Kind)
  extends TypeError

/**
 * A declared scope that does not contain the scope of `part` (spec §2.6), such as a family's constructor field,
 * parameter or index.
 */
final case class ScopeExceeded(declaration: String, declared: Value.Lifetime, part: String, partScope: Value.Lifetime)
  extends TypeError

/** A local of linear type that some path through its binder's extent does not use (spec §3.2). */
final case class LinearUnused(local: String) extends TypeError

/** A second use of a local of linear type on some path through its binder's extent (spec §3.2). */
final case class LinearReused(local: String) extends TypeError

/**
 * A subterm of linear type, `term`, inside a term whose type is a sort or a proposition: types and proofs hold no
 * tokens (spec §3.2).
 */
final case class LinearInType(term: CoreAst.Term, tpe: Value) extends TypeError

/**
 * A value outside every binder whose type is linear (spec §3.2): `definition` names a definition, which every reference
 * uses, and is absent for the program's result, which nothing uses. Only a local's uses are counted.
 */
final case class LinearGlobal(definition: Option[String], tpe: Value) extends TypeError

/** A type that names the atom of a `scope` whose binder `lifetime` does not enclose it (spec §4.2). */
final case class LifetimeEscapes(lifetime: String, tpe: Value) extends TypeError

/**
 * A use of a sealed family's constructors or selectors outside its module (spec §7.1): `member` names the constructor
 * or selector named, and is absent for a match on a value of the family.
 */
final case class SealedConstructor(family: String, member: Option[String]) extends TypeError

/**
 * An axiom outside the trusted prelude (spec §7.3). No rule on an axiom's type could keep it from breaking sealing,
 * linearity or confinement, since an axiom can state `False`; a program adds an assumption in a custom prelude.
 */
final case class UntrustedAxiom(axiom: String) extends TypeError

final case class InvalidInductiveBlock(reason: String) extends TypeError

final case class NonStrictlyPositive(inductive: String, ctor: String, field: String, fieldTy: Value) extends TypeError

final case class PropEliminationRestricted(inductive: String, motive: Value) extends TypeError

final case class InvalidProjection(inductive: String, fieldIndex: Int, reason: String) extends TypeError

final case class InvalidDecreaseSpec(reason: String) extends TypeError

/** A decrease metric structural recursion cannot measure; `isProof` selects the reason. */
final case class NonInductiveDecreaseMetric(metric: Value, isProof: Boolean) extends TypeError

final case class NonDecreasingRecursiveCall(function: String, reason: String) extends TypeError

final case class InvalidRecursiveOccurrence(function: String) extends TypeError

final case class InvalidRecursiveGroup(reason: String) extends TypeError
