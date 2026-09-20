package com.raccoonlang

/** Every message in the language is written here. Values print through `PrettyPrinter`, never as case-class dumps. */
object ErrorRendering {

  def render(error: TypeError): String =
    error match {
      case CannotApplyNonFunction(got) => s"Cannot apply non-fn type $got"
      case ArityMismatch(expected, got) =>
        s"Cannot apply function - expected $expected params, got $got"
      case UnknownConstructor(ctor, inductive) => s"Constructor $ctor does not belong to $inductive"
      case DuplicateCase(ctor)                 => s"Duplicate case for constructor $ctor"
      case UnreachableCase(ctor)               => s"Unreachable case for constructor $ctor"
      case MissingCase(ctor)                   => s"Missing case : $ctor"
      case VarAlreadyLinked(id)                => s"FreshVar $id already linked"
      case NotAType(value)                     => s"$value is not a type"
      case NonInductiveMatch(tpe)              => s"Cannot match on non-inductive type $tpe"
      case MissingReturningClause(reason)      => s"Match requires a returning clause: $reason"
      case NotFound(name)                      => s"$name not found"
      case AlreadyDefined(name)                => s"$name already defined"
      case ReservedKernelName(name)            => s"$name has a builtin body, which only a prelude may declare"
      case NatLiteralUnavailable(reason)       => s"Nat literal unavailable: $reason"
      case StringLiteralUnavailable(reason)    => s"String literal unavailable: $reason"
      case NativeOperationDeclarationMismatch(name, reason) =>
        s"Native operation declaration mismatch for $name: $reason"
      case NativeOperationLimitExceeded(operation, argument, limit) =>
        s"$operation argument $argument exceeds native evaluation limit $limit"
      case AmbiguousName(name, candidates) => s"$name is ambiguous: ${candidates.mkString(", ")}"
      case UnsupportedImport(path) =>
        s"Unresolved import $path; load files through ModuleLoader before elaboration"
      case ModuleNotFound(importPath, searchedPaths) =>
        s"Module $importPath not found. Searched: ${searchedPaths.mkString(", ")}"
      case CyclicImport(cycle)                => s"Cyclic import: ${cycle.map(_.toString).mkString(" -> ")}"
      case ModuleParseError(path, message, _) => s"Failed to parse module ${path.toString}: $message"
      case ImportedModuleHasBody(path)        => s"Imported module ${path.toString} must not contain a program body"
      case ModuleReadFailed(path, reason)     => s"Failed to read module ${path.toString}: $reason"
      case LocalCaseHead(name) =>
        s"Case head $name is local; unqualified case heads must resolve to globals. " +
          s"Use .$name for short-name matching."
      case mismatch: TypeMismatch => renderTypeMismatch(mismatch)
      case NotALevel(v1)          => s"$v1 is not a Level"
      case InvalidConstructorResult(ctor, inductive, got) =>
        s"Constructor $ctor must return $inductive but got $got"
      case NonForcedImplicitParam(param) =>
        s"Parameter $param cannot be implicit: it is not forced by the type of any later non-implicit parameter"
      case ImplicitReconstructionFailed(param, fn, reason) =>
        s"Cannot reconstruct implicit argument $param of $fn: $reason"
      case NonUniformInductiveParam(inductive, ctor, param, got) =>
        s"Constructor $ctor of $inductive returns non-uniform parameter $param as $got"
      case InductiveUniverseTooSmall(inductive, where, fieldTy, fieldUniverse, inductiveUniverse) =>
        s"Inductive $inductive lives in Sort ${PrettyPrinter.print(inductiveUniverse)}, " +
          s"but $where has type $fieldTy : Sort ${PrettyPrinter.print(fieldUniverse)}"
      case InductiveTypeNotASort(tpe)    => s"Inductive type must be a Sort, got $tpe instead"
      case InvalidInductiveBlock(reason) => s"Invalid inductive block: $reason"
      case MutualBlockSortMismatch(family, declared, expected) =>
        s"Invalid inductive block: family $family lives in $declared, expected $expected"
      case NonStrictlyPositive(inductive, ctor, field, fieldTy) =>
        s"Constructor $ctor of $inductive is not strictly positive in field $field : $fieldTy"
      case PropEliminationRestricted(inductive, motive) =>
        s"Cannot eliminate proposition $inductive into non-Prop motive $motive"
      case InvalidProjection(inductive, fieldIndex, reason) =>
        s"Invalid projection $inductive.$fieldIndex: $reason"
      case InvalidDecreaseSpec(reason) => s"Invalid decreases annotation: $reason"
      case NonInductiveDecreaseMetric(metric, isProof) =>
        if (isProof) s"decrease metric $metric is a proof; structural recursion on proofs is not supported"
        else s"decrease metric $metric must have an inductive type"
      case NonDecreasingRecursiveCall(function, reason) =>
        s"Recursive call to $function is not decreasing: $reason"
      case InvalidRecursiveOccurrence(function) => s"Invalid recursive occurrence of $function"
      case InvalidRecursiveGroup(reason)        => s"Invalid recursive definition group: $reason"
    }

  /**
   * The "differ at" line is omitted when the unifier failed at the root. `checkFits` asks `actual ~ expected`, so `v1`
   * belongs to `actual`; both are printed expected-first to match the lines above.
   */
  private def renderTypeMismatch(mismatch: TypeMismatch): String = {
    val expected = PrettyPrinter.print(mismatch.expected)
    val actual = PrettyPrinter.print(mismatch.actual)
    val differ =
      mismatch.detail.flatMap { failure =>
        val expectedPart = PrettyPrinter.print(failure.v2)
        val actualPart = PrettyPrinter.print(failure.v1)
        val reason = if (failure.apart) "provably different" else "not reducible: stuck"
        Option.when(!(expectedPart == expected && actualPart == actual))(
          s"\n  differ at: $expectedPart  vs  $actualPart   ($reason)"
        )
      }
    s"type mismatch\n  expected: $expected\n  actual:   $actual${differ.getOrElse("")}"
  }
}
