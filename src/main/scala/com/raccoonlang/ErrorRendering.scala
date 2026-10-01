package com.raccoonlang

/**
 * Every message in the language is written here. Values print through `PrettyPrinter`, never as case-class dumps, and
 * never through `toString`: each is printed with `strings`, the `String` layout of the environment the program was
 * checked in, so a `String` whose characters are all known prints as a literal, whether it was written or computed.
 */
object ErrorRendering {

  def render(error: TypeError, strings: Option[Value.ValidatedStringLayout]): String = {
    def show(value: Value): String = PrettyPrinter.print(value, strings)
    error match {
      case CannotApplyNonFunction(got) => s"Cannot apply non-fn type ${show(got)}"
      case ArityMismatch(expected, got, ArityMismatch.Arguments) =>
        s"Cannot apply function - expected $expected params, got $got"
      case ArityMismatch(expected, got, ArityMismatch.Call(callee, explicit, implicitFamily)) =>
        val named = if (explicit.isEmpty) "" else explicit.mkString(" (", ", ", ")")
        val determined = "implicit, determined by the other arguments"
        val implicitNote =
          if (implicitFamily.isEmpty) ""
          else if (implicitFamily.length == 1) s"; family parameter ${implicitFamily.head} is $determined"
          else s"; family parameters ${implicitFamily.mkString(", ")} are $determined"
        s"Cannot apply $callee - expected $expected params$named, got $got$implicitNote"
      case ArityMismatch(expected, got, ArityMismatch.Evidence) =>
        s"Cannot supply evidence - expected $expected proofs, got $got"
      case ArityMismatch(expected, got, ArityMismatch.Fields) =>
        s"Cannot bind the constructor's fields - expected $expected fields, got $got"
      case UnknownConstructor(ctor, inductive) => s"Constructor $ctor does not belong to $inductive"
      case DuplicateCase(ctor)                 => s"Duplicate case for constructor $ctor"
      case UnreachableCase(ctor)               => s"Unreachable case for constructor $ctor"
      case MissingCase(ctor)                   => s"Missing case : $ctor"
      case RedundantCase =>
        "Redundant wildcard case: every constructor the scrutinee can be built by already has a case"
      case MatchEquationIndexed(family) =>
        s"A match names its equation only on a family without indices, but $family has indices"
      case MatchEquationUnavailable(reason) => s"Match equation unavailable: $reason"
      case VarAlreadyLinked(id)             => s"FreshVar $id already linked"
      case NotAType(value)                  => s"${show(value)} is not a type"
      case NonInductiveMatch(tpe)           => s"Cannot match on non-inductive type ${show(tpe)}"
      case NotFound(name)                   => s"$name not found"
      case AlreadyDefined(name)             => s"$name already defined"
      case ReservedKernelName(name)         => s"$name has a builtin body, which only a prelude may declare"
      case NatLiteralUnavailable(reason)    => s"Nat literal unavailable: $reason"
      case StringLiteralUnavailable(reason) => s"String literal unavailable: $reason"
      case NativeOperationDeclarationMismatch(name, reason) =>
        s"Native operation declaration mismatch for $name: $reason"
      case NativeOperationLimitExceeded(operation, argument, limit) =>
        s"$operation argument $argument exceeds native evaluation limit $limit"
      case EvaluationTooDeep =>
        "Evaluation is too deep: it exhausted the stack, whose size the command line sets with --stack"
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
        s"Cannot destructure a value of type ${show(tpe)}: only a family with one constructor, no indices and no " +
          "recursive field, outside Prop, is taken apart by its fields"
      case mismatch: TypeMismatch => renderTypeMismatch(mismatch, show)
      case InvalidConstructorResult(ctor, inductive, got) =>
        s"Constructor $ctor must return $inductive but got ${show(got)}"
      case NonForcedImplicitParam(param, isProposition) =>
        val evidence =
          if (isProposition) s"; a proposition each call discharges is an evidence parameter, written [$param: …]"
          else ""
        s"Parameter $param cannot be implicit: it is not forced by the type of any later explicit parameter$evidence"
      case NotAProposition(binder, tpe) =>
        s"Evidence parameter $binder has the type ${show(tpe)}, which is not a proposition: evidence is a proof, so " +
          "its type is in Prop"
      case EvidenceNotDischarged(binder, callee, path, proposition, reason) =>
        val failed =
          if (path.isEmpty) s"its proposition is ${show(proposition)}"
          else s"through its proposition's evidence fields, ${renderPath(path)}: ${show(proposition)}"
        val why = reason match {
          case EvidenceNotDischarged.NoConstructor =>
            "which no constructor proves with the fields its type determines"
          case EvidenceNotDischarged.Sealed     => "whose sealed family keeps its constructors to its module"
          case EvidenceNotDischarged.Undeclared => "whose family's constructors are not yet declared"
          case EvidenceNotDischarged.TooDeep =>
            s"which lies ${Discharge.DepthBound} evidence fields deep, the bound past which discharge does not descend"
        }
        s"Evidence $binder of $callee is not discharged: $failed, $why; supply a proof as $callee(…)[proof]"
      case BuiltinEvidence(name, binder) =>
        s"Builtin $name binds the evidence parameter $binder: a builtin reads its arguments as values, so its " +
          "binders are explicit or implicit"
      case ImplicitReconstructionFailed(param, fn, reason) =>
        s"Cannot reconstruct implicit argument $param of $fn: ${renderProjectionFailure(reason, show)}"
      case NonUniformInductiveParam(inductive, ctor, param, got) =>
        s"Constructor $ctor of $inductive returns non-uniform parameter $param as ${show(got)}"
      case InductiveUniverseTooSmall(inductive, where, fieldTy, fieldUniverse, inductiveUniverse) =>
        s"Inductive $inductive lives in Sort { level = ${show(inductiveUniverse)} }, " +
          s"but $where has type ${show(fieldTy)} : Sort { level = ${show(fieldUniverse)} }"
      case InductiveTypeNotASort(tpe) => s"Inductive type must be a Sort, got ${show(tpe)} instead"
      case LinearProp(kind, level)    =>
        // The level is not never zero, so a constant one is zero.
        val levelIsZero = if (level.terms.isEmpty) "is zero" else s"${show(level)} may be zero"
        s"A sort of kind ${show(kind)} needs a level that is never zero, but its level $levelIsZero; proofs are " +
          "unrestricted"
      case KindExceeded(declaration, declared, part, partKind) =>
        s"$declaration is declared at kind ${show(declared)}, which does not contain the kind ${show(partKind)} " +
          s"of ${renderPart(part, show)}"
      case ScopeExceeded(declaration, declared, part, partScope) =>
        s"$declaration is declared at scope ${show(declared)}, which does not contain the scope ${show(partScope)} " +
          s"of ${renderPart(part, show)}"
      case LinearUnused(local) =>
        if (local == "_") "A wildcard binds a value of linear type, which must be used exactly once, and is never used"
        else s"$local has a linear type, so it must be used exactly once, but some path does not use it"
      case LinearReused(local) =>
        s"$local has a linear type, so it must be used exactly once, but this is a second use on some path"
      case LinearInType(term, tpe) =>
        s"${PrettyPrinter.printTerm(term)} has the linear type ${show(tpe)}, so it cannot stand inside a type or a " +
          "proof: types and proofs hold no tokens"
      case LinearGlobal(definition, tpe) =>
        val value = definition.fold("The program's result")(name => s"Definition $name")
        s"$value has the linear type ${show(tpe)}; a value outside every binder is never linear, since only a " +
          "local's uses are counted"
      case LifetimeEscapes(lifetime, tpe) =>
        s"Lifetime $lifetime escapes its scope: the type ${show(tpe)} names it outside `scope $lifetime`"
      case SealedConstructor(family, member) =>
        val use = member.fold("matching on a value of it")(name => s"naming $name")
        s"The sealed family $family keeps its constructors and selectors to the module that declares it, so $use " +
          "is not allowed here"
      case UntrustedAxiom(axiom) =>
        s"Axiom $axiom is declared outside the trusted prelude; only the prelude declares axioms, so an assumption " +
          "goes in a custom prelude (--prelude)"
      case InvalidInductiveBlock(reason) => s"Invalid inductive block: $reason"
      case NonStrictlyPositive(inductive, ctor, field, fieldTy) =>
        s"Constructor $ctor of $inductive is not strictly positive in field $field : ${show(fieldTy)}"
      case PropEliminationRestricted(inductive, motive) =>
        s"Cannot eliminate proposition $inductive into non-Prop motive ${show(motive)}"
      case InvalidProjection(inductive, fieldIndex, reason) =>
        s"Invalid projection $inductive.$fieldIndex: $reason"
      case InvalidDecreaseSpec(reason) => s"Invalid decreases annotation: $reason"
      case NonInductiveDecreaseMetric(metric, isProof) =>
        if (isProof) s"decrease metric ${show(metric)} is a proof; structural recursion on proofs is not supported"
        else s"decrease metric ${show(metric)} must have an inductive type"
      case NonDecreasingRecursiveCall(function, reason) =>
        s"Recursive call to $function is not decreasing: $reason"
      case InvalidRecursiveOccurrence(function) => s"Invalid recursive occurrence of $function"
      case InvalidRecursiveGroup(reason)        => s"Invalid recursive definition group: $reason"
    }
  }

  /**
   * The "differ at" line is omitted when the unifier failed at the root. `checkFits` asks `actual ~ expected`, so `v1`
   * belongs to `actual`; both are printed expected-first to match the lines above. Function types that differ in their
   * closures, or in what their code captures, fail at the two function types, and the report names what differs.
   */
  private def renderTypeMismatch(mismatch: TypeMismatch, show: Value => String): String = {
    val expected = show(mismatch.expected)
    val actual = show(mismatch.actual)
    val differ =
      mismatch.detail.map { failure =>
        val expectedPart = show(failure.v2)
        val actualPart = show(failure.v1)
        val functionParts = (failure.v2, failure.v1) match {
          case (expectedPi: Value.VPi, actualPi: Value.VPi) =>
            Vector(
              Option.when(expectedPi.closureKind != actualPi.closureKind)(
                s"closures differ in kind ${show(expectedPi.closureKind)}  vs  ${show(actualPi.closureKind)}"
              ),
              Option.when(expectedPi.closureScope != actualPi.closureScope)(
                s"closures differ in scope ${show(expectedPi.closureScope)}  vs  ${show(actualPi.closureScope)}"
              ),
              Option.when(expectedPi.mentionedScope != actualPi.mentionedScope)(
                s"their code captures differ in scope ${show(expectedPi.mentionedScope)}  vs  " +
                  show(actualPi.mentionedScope)
              )
            ).flatten
          case _ => Vector.empty
        }
        val reason = if (failure.apart) "provably different" else "not reducible: stuck"
        val at =
          if (expectedPart == expected && actualPart == actual) ""
          else if (functionParts.nonEmpty) s"\n  differ at: $expectedPart  vs  $actualPart"
          else s"\n  differ at: $expectedPart  vs  $actualPart   ($reason)"
        at + functionParts.map(field => s"\n  $field").mkString
      }
    s"type mismatch\n  expected: $expected\n  actual:   $actual${differ.getOrElse("")}"
  }

  /**
   * A path of evidence fields, `Both.y > GemmShape.nOk`, with a run of one field repeated written once with its count,
   * `Wrap.h ×1024`, since a path may be as deep as discharge's bound.
   */
  private def renderPath(path: Vector[String]): String = {
    val runs = path.foldLeft(Vector.empty[(String, Int)]) {
      case (init :+ ((step, count)), next) if step == next => init :+ (step -> (count + 1))
      case (runs, next)                                    => runs :+ (next -> 1)
    }
    runs.map { case (step, count) => if (count == 1) step else s"$step ×$count" }.mkString(" > ")
  }

  /** A part whose kind or scope a declaration's must contain, as the phrase that follows "of". */
  private def renderPart(part: ContainedPart, show: Value => String): String =
    part match {
      case ContainedPart.Capture(name, tpe)      => s"capture $name : ${show(tpe)}"
      case ContainedPart.Field(name, tpe)        => s"field $name : ${show(tpe)}"
      case ContainedPart.LifetimeParameter(name) => s"lifetime parameter $name, which every type former must name"
    }

  /** Why an implicit argument's projection could not be followed (`Projection.project`). */
  private def renderProjectionFailure(failure: telescope.Projection.Failure, show: Value => String): String = {
    import telescope.Projection.Failure._
    failure match {
      case RootOutOfRange(root, provided) => s"projection root $root out of range ($provided args)"
      case NotALevel(got)                 => s"expected a level, got ${show(got)}"
      case NotAnApplication(head, got)    => s"expected an application of $head, got ${show(got)}"
      case NotAConstructor(ctor, got)     => s"expected a $ctor value, got ${show(got)}"
      case NotASort(got)                  => s"expected a sort, got ${show(got)}"
      case NotAFunctionType(got)          => s"expected a function type, got ${show(got)}"
      case LevelBelowOffset(level, k)     => s"level ${show(level)} does not cover offset $k"
      case DependentDomain(idx, pi)       => s"domain $idx of ${show(pi)} depends on earlier binders"
      case DependentCodomain(pi)          => s"codomain of ${show(pi)} depends on its binders"
      case DependentResult(pi)            => s"result of ${show(pi)} depends on its binders"
    }
  }
}
