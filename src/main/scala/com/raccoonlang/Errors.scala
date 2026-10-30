package com.raccoonlang

import com.raccoonlang.Value.Level

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
    case e: RedundantCase                   => e.copy(span = Some(sp))
    case e: InvalidMutualBlock              => e.copy(span = Some(sp))
    case e: MatchEquationUnavailable        => e.copy(span = Some(sp))
    case e: MatchEquationIndexed            => e.copy(span = Some(sp))
    case e: NotAType                        => e.copy(span = Some(sp))
    case e: NonInductiveMatch               => e.copy(span = Some(sp))
    case e: InvalidSingleConstructorMatch   => e.copy(span = Some(sp))
    case e: InvalidDestructuring            => e.copy(span = Some(sp))
    case e: MissingReturningClause          => e.copy(span = Some(sp))
    case e: NotFound                        => e.copy(span = Some(sp))
    case e: AlreadyDefined                  => e.copy(span = Some(sp))
    case e: CannotLinkToBottom              => e.copy(span = Some(sp))
    case e: VarAlreadyLinked                => e.copy(span = Some(sp))
    case e: TypeMismatch                    => e.copy(span = Some(sp))
    case e: PropositionAsTypeCarrier        => e.copy(span = Some(sp))
    case e: InvalidConstructorResult        => e.copy(span = Some(sp))
    case e: InvalidErasedConstructorBinder  => e.copy(span = Some(sp))
    case e: NonUniformInductiveParam        => e.copy(span = Some(sp))
    case e: NotALevel                       => e.copy(span = Some(sp))
    case e: NotAKind                        => e.copy(span = Some(sp))
    case e: InductiveUniverseTooSmall       => e.copy(span = Some(sp))
    case e: FamilyArgumentTooLarge          => e.copy(span = Some(sp))
    case e: NonStrictlyPositive             => e.copy(span = Some(sp))
    case e: FamilyInResultIndex             => e.copy(span = Some(sp))
    case e: InductiveTypeNotASort           => e.copy(span = Some(sp))
    case e: PatternCaptureNeedsExpectedType => e.copy(span = Some(sp))
    case e: CaptureWithoutOpening           => e.copy(span = Some(sp))
    case e: InvalidTypePattern              => e.copy(span = Some(sp))
    case e: FailedToOpenCapture             => e.copy(span = Some(sp))
    case e: PropEliminationRestricted       => e.copy(span = Some(sp))
    case e: InvalidLevelSubtraction         => e.copy(span = Some(sp))
    case e: WTF                             => e.copy(span = Some(sp))
    case e: InvalidStruct                   => e.copy(span = Some(sp))
    case e: UnappliedField                  => e.copy(span = Some(sp))
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
    case e: NatValueTooLarge                => e.copy(span = Some(sp))
    case e: EvaluationTooDeep               => e.copy(span = Some(sp))
    case e: UserAxiom                       => e.copy(span = Some(sp))
    case e: ProgramBuiltin                  => e.copy(span = Some(sp))
    case e: LinearReused                    => e.copy(span = Some(sp))
    case e: LinearCapture                   => e.copy(span = Some(sp))
    case e: LinearInType                    => e.copy(span = Some(sp))
    case e: LinearFieldInUnrestrictedFamily => e.copy(span = Some(sp))
    case e: LinearFamilyArgument            => e.copy(span = Some(sp))
    case e: LinearReusedInType              => e.copy(span = Some(sp))
    case e: LinearNotJointlyLive            => e.copy(span = Some(sp))
    case e: LinearInstance                  => e.copy(span = Some(sp))
    case e: LinearGlobal                    => e.copy(span = Some(sp))
    case e: LinearAxiom                     => e.copy(span = Some(sp))
  }
}

final case class UserAxiom(name: String, span: Option[Span] = None) extends TypeError {
  def msg: String = s"axiom $name is not allowed: user axioms are disabled by --no-user-axioms"
}

/**
 * A `:= builtin` in a program: only the kernel and the prelude declare builtins, whose types are trusted, not checked.
 */
final case class ProgramBuiltin(name: String, span: Option[Span] = None) extends TypeError {
  def msg: String = s"builtin $name is not allowed: only the kernel and the prelude declare builtins"
}

final case class UnificationFailed(v1: Value, v2: Value, span: Option[Span] = None) extends TypeError {
  def msg: String = s"Failed to unify $v1 and $v2"
}

final case class CannotApplyNonFunction(got: Value, span: Option[Span] = None) extends TypeError {
  def msg: String = s"Cannot apply non-fn type ${got}"
}

final case class ArityMismatch(expected: Int, got: Int, span: Option[Span] = None) extends TypeError {
  def msg: String = s"Cannot apply function - expected $expected params, got $got"
}

final case class UnknownConstructor(ctor: String, inductive: String, span: Option[Span] = None) extends TypeError {
  def msg: String = s"Constructor $ctor does not belong to $inductive"
}

final case class DuplicateCase(ctor: String, span: Option[Span] = None) extends TypeError {
  def msg: String = s"Duplicate case for constructor $ctor"
}

final case class UnreachableCase(ctor: String, span: Option[Span] = None) extends TypeError {
  def msg: String = s"Unreachable case for constructor $ctor"
}

final case class MissingCase(ctor: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Missing case : $ctor"
}

/** A match that names its equation, `match h : e`, where no equation can be stated: `reason` says why. */
final case class MatchEquationUnavailable(reason: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"This match cannot name its equation: $reason"
}

/**
 * A named equation in the case of `ctor` of an indexed family, whose refinement left the constructor's indices apart
 * from the scrutinee's, so the scrutinee and the constructor value have different types.
 */
final case class MatchEquationIndexed(ctor: String, span: Option[Span] = None) extends TypeError {
  override def msg: String =
    s"The equation of the case $ctor relates values of different types: its refinement does not equate the constructor's indices with the scrutinee's"
}

/** A `mutual` block that is empty, mixes families with definitions, or has a member it cannot hold. */
final case class InvalidMutualBlock(reason: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Invalid mutual block: $reason"
}

/** A wildcard case that stands for no constructor: the other cases name every reachable one. */
final case class RedundantCase(span: Option[Span] = None) extends TypeError {
  override def msg: String = "Redundant wildcard case: the other cases name every reachable constructor"
}

final case class VarAlreadyLinked(id: Long, span: Option[Span] = None) extends TypeError {
  def msg: String = s"FreshVar $id already linked"
}

final case class CannotLinkToBottom(id: Long, span: Option[Span] = None) extends TypeError {
  def msg: String = s"Cannot link to bottom of chain for var $id"
}

final case class NotAType(value: Value, span: Option[Span] = None) extends TypeError {
  def msg: String = s"$value is not a type"
}

final case class NonInductiveMatch(tpe: Value, span: Option[Span] = None) extends TypeError {
  def msg: String = s"Cannot match on non-inductive type $tpe"
}

final case class InvalidSingleConstructorMatch(
    tpe: Value,
    reason: String,
    span: Option[Span] = None
) extends TypeError {
  def msg: String = s"Cannot use a constructor-omitting match on $tpe: $reason"
}

final case class InvalidDestructuring(reason: String, span: Option[Span] = None) extends TypeError {
  def msg: String = s"Invalid destructuring let: $reason"
}

final case class MissingReturningClause(reason: String, span: Option[Span] = None) extends TypeError {
  def msg: String = s"Match requires a returning clause: $reason"
}

/**
 * A name that resolves to nothing; `reason`, when given, says why, such as a family with no constructor of that name.
 */
final case class NotFound(name: String, span: Option[Span] = None, reason: Option[String] = None) extends TypeError {
  def msg: String = s"$name not found" + reason.fold("")(r => s": $r")
}

final case class AlreadyDefined(name: String, span: Option[Span] = None) extends TypeError {
  def msg: String = s"$name already defined"
}

final case class AmbiguousName(name: String, candidates: Vector[String], span: Option[Span] = None) extends TypeError {
  override def msg: String = s"$name is ambiguous: ${candidates.mkString(", ")}"
}

final case class UnsupportedImport(path: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Unresolved import $path; load files through ModuleLoader before elaboration"
}

final case class ModuleNotFound(importPath: String, searchedPaths: Vector[Path], span: Option[Span] = None)
  extends TypeError {
  override def msg: String = s"Module $importPath not found. Searched: ${searchedPaths.mkString(", ")}"
}

final case class CyclicImport(cycle: Vector[Path], span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Cyclic import: ${cycle.map(_.toString).mkString(" -> ")}"
}

final case class ModuleParseError(path: Path, message: String, offset: Int, span: Option[Span] = None)
  extends TypeError {
  override def msg: String = s"Failed to parse module ${path.toString}: $message"
}

final case class ImportedModuleHasBody(path: Path, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Imported module ${path.toString} must not contain a program body"
}

final case class ModuleReadFailed(path: Path, reason: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Failed to read module ${path.toString}: $reason"
}

final case class LocalCaseHead(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String =
    s"Case head $name is local; unqualified case heads must resolve to globals. Use .$name for short-name matching."
}

final case class TypeMismatch(expected: Value, actual: Value, span: Option[Span] = None) extends TypeError {
  def msg: String = s"Type mismatch: expected type: $expected, actual: $actual"
}

final case class PropositionAsTypeCarrier(span: Option[Span] = None) extends TypeError {
  override def msg: String = "Expected a Type carrier, but got a proposition (of sort Prop)"
}

final case class NotALevel(v1: Value, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"$v1 is not a Level"
}

final case class NotAKind(v1: Value, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"$v1 is not a Kind"
}

final case class PatternCaptureNeedsExpectedType(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Pattern capture $$$name needs an expected type"
}

/**
 * A capture that no binding can read off the argument's type, such as `$u` in `Sort(Level.max($u, $v))`: in a universe,
 * a level capture must be the level or a `Level.succ` of it, and a kind capture the kind itself.
 */
final case class CaptureWithoutOpening(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String =
    s"Capture $$$name cannot be read off the argument's type: in a universe, a level capture must be the level or " +
      "a Level.succ of it, and a kind capture the kind itself"
}

/** A type pattern the checker cannot open, such as one with a capture under a projection. */
final case class InvalidTypePattern(reason: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Invalid type pattern: $reason"
}

/**
 * A type-pattern capture that cannot be read off an argument's type, which has no argument `idx` at the position the
 * capture reads: the type does not have the pattern's shape there, such as `Nat` for `Box($A)`, or `Lin(u)` for
 * `U($k, $u)` with an alias `U(k, u) := Univ(k, u)`, since a universe reads by position only as `Sort(l)` or `Lin(l)`,
 * with its level at position 0.
 */
final case class FailedToOpenCapture(capture: String, v: Value, idx: Int, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"The type-pattern capture $$$capture cannot be read off $v, which has no argument $idx"
}

final case class WTF(msg: String, span: Option[Span] = None) extends TypeError

final case class InvalidConstructorResult(
    ctor: String,
    inductive: String,
    got: Value,
    span: Option[Span] = None
) extends TypeError {
  override def msg: String =
    s"Constructor $ctor must return $inductive but got $got"
}

final case class InvalidErasedConstructorBinder(
    ctor: String,
    binder: String,
    reason: String,
    span: Option[Span] = None
) extends TypeError {
  override def msg: String =
    s"Invalid erased constructor binder $binder in $ctor: $reason"
}

final case class NonUniformInductiveParam(
    inductive: String,
    ctor: String,
    param: String,
    got: Value,
    span: Option[Span] = None
) extends TypeError {
  override def msg: String =
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
  override def msg: String =
    s"Inductive $inductive lives in Sort $inductiveUniverse, but $where has type $fieldTy : Sort $fieldUniverse"
}

final case class FamilyArgumentTooLarge(
    inductive: String,
    argument: String,
    level: Value.Level,
    span: Option[Span] = None
) extends TypeError {
  override def msg: String = s"Family $inductive argument $argument requires the family to live in Sort $level or above"
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
  override def msg: String =
    s"Constructor $ctor of $inductive is not strictly positive in field $field : $fieldTy"
}

final case class FamilyInResultIndex(
    inductive: String,
    ctor: String,
    index: String,
    indexValue: Value,
    span: Option[Span] = None
) extends TypeError {
  override def msg: String =
    s"Constructor $ctor of $inductive names a family of its block in result index $index := $indexValue"
}

final case class PropEliminationRestricted(
    inductive: String,
    motive: Value,
    span: Option[Span] = None
) extends TypeError {
  override def msg: String =
    s"Cannot eliminate proposition $inductive into non-Prop motive $motive"
}

final case class InvalidLevelSubtraction(l: Level, sub: Int, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Tried to subtract $sub from $l"
}

/**
 * A field of the record `inductive` that has no projection at the projected value's type, for `reason`: its type
 * depends on a capture that the type's arguments do not determine (docs/kernel.md, "Structure eta and projections").
 */
final case class InvalidStruct(inductive: String, reason: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Invalid struct $inductive: $reason"
}

/** `inductive.field`, a field of the record `inductive`, used as a value: a field is selected from a record. */
final case class UnappliedField(inductive: String, field: String, span: Option[Span] = None) extends TypeError {
  override def msg: String =
    s"$inductive.$field is a field of $inductive, not a function: apply it to a record, as $inductive.$field(r), or write r.$field"
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

/** A closed Nat power whose result a JVM integer cannot represent; a representation limit, not a budget. */
final case class NatValueTooLarge(exponent: BigInt, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Nat power with exponent $exponent is too large to represent"
}

/**
 * Checking a declaration, or checking, evaluating and showing the program's body, exhausted the host stack
 * (docs/kernel.md, "Evaluation depth"). It is located at the whole declaration or body: a stack overflow is caught only
 * there.
 */
final case class EvaluationTooDeep(span: Option[Span] = None) extends TypeError {
  override def msg: String =
    "Evaluation is too deep: it exhausted the stack, whose size the command line sets with --stack"
}

// Linear types (docs/kernel.md, "Linear types").

/** A second use of a linear local on some path through its binder's extent, located at that use. */
final case class LinearReused(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Linear local $name is used more than once on some path"
}

/** A lambda body that references a linear local bound outside the lambda. */
final case class LinearCapture(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"A lambda cannot capture the linear local $name; pass it as an argument"
}

/** A type-pattern capture of linear type, which would bind an untracked linear local (L7). */
final case class LinearInType(span: Option[Span] = None) extends TypeError {
  override def msg: String = "A type-pattern capture cannot bind a linear value"
}

/** One call inside a type or proof that receives the same tracked local in two of its linear inputs. */
final case class LinearReusedInType(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String =
    s"A call inside a type or proof receives linear local $name in two of its inputs, which must be separate"
}

/** One call inside a type or proof whose linear inputs were never live together. */
final case class LinearNotJointlyLive(consumed: String, later: String, span: Option[Span] = None) extends TypeError {
  override def msg: String =
    s"A call inside a type or proof combines $consumed with $later, which was bound after $consumed was consumed"
}

final case class LinearFieldInUnrestrictedFamily(inductive: String, field: String, span: Option[Span] = None)
  extends TypeError {
  override def msg: String = s"Field $field of $inductive is linear, but $inductive is not declared in Lin"
}

final case class LinearFamilyArgument(inductive: String, argument: String, span: Option[Span] = None)
  extends TypeError {
  override def msg: String = s"Family $inductive argument $argument has a linear type"
}

final case class LinearInstance(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Instance $name has a linear type"
}

/** A definition or the program result of linear type: every reference would copy it, and nothing consumes it. */
final case class LinearGlobal(subject: LinearGlobal.Subject, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"${subject.description} cannot have a linear type"
}

object LinearGlobal {

  /**
   * What has the linear type: a definition, or the program's result, that of its body or, for an entry, of the call.
   */
  sealed trait Subject {
    def description: String
  }

  final case class Definition(name: String) extends Subject {
    def description: String = s"Definition $name"
  }

  case object ProgramResult extends Subject {
    def description: String = "The program result"
  }

  case object EntryResult extends Subject {
    def description: String = "The entry's result"
  }
}

final case class LinearAxiom(name: String, span: Option[Span] = None) extends TypeError {
  override def msg: String = s"Axiom $name produces or consumes a linear value"
}
