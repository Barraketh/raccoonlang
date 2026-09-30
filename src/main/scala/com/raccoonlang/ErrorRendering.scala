package com.raccoonlang

/** Every message in the language is written here. Values print through `PrettyPrinter`, never as case-class dumps. */
object ErrorRendering {

  def render(error: TypeError): String =
    error match {
      case CannotApplyNonFunction(got) => s"Cannot apply non-fn type $got"
      case ArityMismatch(expected, got, ArityMismatch.Arguments) =>
        s"Cannot apply function - expected $expected params, got $got"
      case ArityMismatch(expected, got, ArityMismatch.Fields) =>
        s"Cannot bind the constructor's fields - expected $expected fields, got $got"
      case UnknownConstructor(ctor, inductive) => s"Constructor $ctor does not belong to $inductive"
      case DuplicateCase(ctor)                 => s"Duplicate case for constructor $ctor"
      case UnreachableCase(ctor)               => s"Unreachable case for constructor $ctor"
      case MissingCase(ctor)                   => s"Missing case : $ctor"
      case VarAlreadyLinked(id)                => s"FreshVar $id already linked"
      case NotAType(value)                     => s"$value is not a type"
      case NonInductiveMatch(tpe)              => s"Cannot match on non-inductive type $tpe"
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
      case NotDestructurable(tpe) =>
        s"Cannot destructure a value of type $tpe: only a family with one constructor, no indices and no recursive " +
          "field, outside Prop, is taken apart by its fields"
      case mismatch: TypeMismatch => renderTypeMismatch(mismatch)
      case InvalidConstructorResult(ctor, inductive, got) =>
        s"Constructor $ctor must return $inductive but got $got"
      case NonForcedImplicitParam(param) =>
        s"Parameter $param cannot be implicit: it is not forced by the type of any later non-implicit parameter"
      case ImplicitReconstructionFailed(param, fn, reason) =>
        s"Cannot reconstruct implicit argument $param of $fn: $reason"
      case NonUniformInductiveParam(inductive, ctor, param, got) =>
        s"Constructor $ctor of $inductive returns non-uniform parameter $param as $got"
      case InductiveUniverseTooSmall(inductive, where, fieldTy, fieldUniverse, inductiveUniverse) =>
        s"Inductive $inductive lives in Sort { level = ${PrettyPrinter.print(inductiveUniverse)} }, " +
          s"but $where has type $fieldTy : Sort { level = ${PrettyPrinter.print(fieldUniverse)} }"
      case InductiveTypeNotASort(tpe) => s"Inductive type must be a Sort, got $tpe instead"
      case LinearProp(kind, level)    =>
        // The level is not never zero, so a constant one is zero.
        val levelIsZero = if (level.terms.isEmpty) "is zero" else s"$level may be zero"
        s"A sort of kind $kind needs a level that is never zero, but its level $levelIsZero; proofs are unrestricted"
      case KindExceeded(declaration, declared, part, partKind) =>
        s"$declaration is declared at kind $declared, which does not contain the kind $partKind of $part"
      case ScopeExceeded(declaration, declared, part, partScope) =>
        s"$declaration is declared at scope $declared, which does not contain the scope $partScope of $part"
      case LinearUnused(local) =>
        if (local == "_") "A wildcard binds a value of linear type, which must be used exactly once, and is never used"
        else s"$local has a linear type, so it must be used exactly once, but some path does not use it"
      case LinearReused(local) =>
        s"$local has a linear type, so it must be used exactly once, but this is a second use on some path"
      case LinearInType(term, tpe) =>
        s"${PrettyPrinter.printTerm(term)} has the linear type $tpe, so it cannot stand inside a type or a proof: " +
          "types and proofs hold no tokens"
      case LinearGlobal(definition, tpe) =>
        val value = definition.fold("The program's result")(name => s"Definition $name")
        s"$value has the linear type $tpe; a value outside every binder is never linear, since only a local's uses " +
          "are counted"
      case LifetimeEscapes(lifetime, tpe) =>
        s"Lifetime $lifetime escapes its scope: the type $tpe names it outside `scope $lifetime`"
      case SealedConstructor(family, member) =>
        val use = member.fold("matching on a value of it")(name => s"naming $name")
        s"The sealed family $family keeps its constructors and selectors to the module that declares it, so $use " +
          "is not allowed here"
      case UntrustedAxiom(axiom) =>
        s"Axiom $axiom is declared outside the trusted prelude; only the prelude declares axioms, so an assumption " +
          "goes in a custom prelude (--prelude)"
      case InvalidInductiveBlock(reason) => s"Invalid inductive block: $reason"
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
   * belongs to `actual`; both are printed expected-first to match the lines above. Function types that differ in their
   * closures fail at the two function types, and the report names the closure fields that differ.
   */
  private def renderTypeMismatch(mismatch: TypeMismatch): String = {
    val expected = PrettyPrinter.print(mismatch.expected)
    val actual = PrettyPrinter.print(mismatch.actual)
    val differ =
      mismatch.detail.map { failure =>
        val expectedPart = PrettyPrinter.print(failure.v2)
        val actualPart = PrettyPrinter.print(failure.v1)
        val closures = (failure.v2, failure.v1) match {
          case (expectedPi: Value.VPi, actualPi: Value.VPi) =>
            Vector(
              Option.when(expectedPi.closureKind != actualPi.closureKind)(
                s"kind ${PrettyPrinter.print(expectedPi.closureKind)}  vs  ${PrettyPrinter.print(actualPi.closureKind)}"
              ),
              Option.when(expectedPi.closureScope != actualPi.closureScope)(
                s"scope ${PrettyPrinter.print(expectedPi.closureScope)}  vs  ${PrettyPrinter.print(actualPi.closureScope)}"
              )
            ).flatten
          case _ => Vector.empty
        }
        val reason = if (failure.apart) "provably different" else "not reducible: stuck"
        val at =
          if (expectedPart == expected && actualPart == actual) ""
          else if (closures.nonEmpty) s"\n  differ at: $expectedPart  vs  $actualPart"
          else s"\n  differ at: $expectedPart  vs  $actualPart   ($reason)"
        at + closures.map(field => s"\n  closures differ in $field").mkString
      }
    s"type mismatch\n  expected: $expected\n  actual:   $actual${differ.getOrElse("")}"
  }
}
