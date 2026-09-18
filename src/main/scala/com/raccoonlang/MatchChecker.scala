package com.raccoonlang

import com.raccoonlang.CoreAst.{Case, Term}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/** Static checking and refinement of pattern matches over the available inductive values. */
object MatchChecker {
  private final case class ReachableCtor(
      name: String,
      head: ConstructorHead,
      fieldArgs: Vector[Value],
      resultTy: Value,
      branchEqStore: EqStore
  )

  private def computeReachable(
      scrut: Value,
      scrutTpe: Value,
      family: InductiveFamilyInstance,
      env: Env
  ): Vector[ReachableCtor] = {
    final case class Refinable(ids: DepSet, vars: Vector[Var]) {
      def ++(other: Refinable): Refinable = Refinable(ids ++ other.ids, vars ++ other.vars)
    }
    def refinableIn(value: Value, ids: DepSet): Refinable = Refinable(ids, Value.varsIn(value, ids))
    def rootRefinable(value: Value): Refinable = value match {
      case Blocker(blockedOn) => refinableIn(value, blockedOn)
      case _                  => Refinable(DepSet.empty, Vector.empty)
    }

    family.meta.constructors.flatMap { ctorMeta =>
      val head = env(ctorMeta.canonicalName) match {
        case value: ConstructorHead => value
        case _                      => throw UnknownConstructor(ctorMeta.canonicalName, family.head.name)
      }
      val (allArgs, resultTy) = BinderOps.freshCtorArgsAndResult(head)
      val fields = Value.constructorStoredArgs(head, allArgs)
      val ctorValue = Value.canonicalizeProof(VCtor(head, fields, resultTy))
      val ctorRefinable = refinableIn(ctorValue, ctorValue.synDeps)
      val valueRefinable = rootRefinable(scrut) ++ ctorRefinable
      val typeRefinable = refinableIn(scrutTpe, scrutTpe.synDeps) ++ ctorRefinable
      val branchStore = ValueEquivalence.tryUnify(
        scrut,
        ctorValue,
        EqStore.empty.allowEta(valueRefinable.ids, valueRefinable.vars)
      ) match {
        case Right(store)                   => Some(store)
        case Left(failure) if failure.apart => None
        case Left(_) =>
          ValueEquivalence.tryUnify(
            resultTy,
            scrutTpe,
            EqStore.empty.allowEta(typeRefinable.ids, typeRefinable.vars)
          ) match {
            case Right(store)                   => Some(store)
            case Left(failure) if failure.apart => None
            case Left(_)                        => Some(EqStore.empty)
          }
      }
      branchStore.map { store =>
        ReachableCtor(
          ctorMeta.canonicalName,
          head,
          fields.map(ValueOps.materialize(_, store)),
          ValueOps.materialize(scrutTpe, store),
          store
        )
      }
    }
  }

  /** Prop-to-data elimination is safe only for impossible families or certified field recovery. */
  private def allowLargeElimination(scrutTpe: Value, reachable: Vector[ReachableCtor]): Boolean =
    reachable.isEmpty || ProofReconstruction.canRecoverAll(scrutTpe)

  private def checkPropElimination(
      family: InductiveFamilyInstance,
      scrutTpe: Value,
      motive: Value,
      reachable: => Vector[ReachableCtor],
      span: Span
  ): Unit =
    if (
      TypeChecker.isPropValuedType(scrutTpe) && !TypeChecker.isPropValuedType(motive) &&
      !allowLargeElimination(scrutTpe, reachable)
    )
      throw PropEliminationRestricted(family.head.name, motive, Some(span))

  private def resolveCase(c: Case, family: InductiveFamilyInstance): Case = {
    val candidates =
      if (c.isFullyQualified)
        family.meta.constructors.collect { case ctor if ctor.canonicalName == c.ctorName => ctor.canonicalName }
      else family.meta.constructors.collect { case ctor if ctor.shortName == c.ctorName => ctor.canonicalName }
    candidates match {
      case Vector(name) => c.copy(ctorName = name)
      case Vector()     => throw UnknownConstructor(c.ctorName, family.head.name, Some(c.span))
      case many         => throw AmbiguousName(c.ctorName, many, Some(c.span))
    }
  }

  private def checkBranch(br: Case, args: Vector[Value], env: Env, expected: Value): Case = {
    if (args.length != br.argRefs.length) throw ArityMismatch(args.length, br.argRefs.length, Some(br.span))
    val branchEnv = br.argRefs.zip(args).foldLeft(env) {
      case (current, (Some(ref), value)) =>
        current.putLocal(ref, Value.canonicalizeProof(ValueOps.materialize(value, EqStore.empty)))
      case (current, (None, _)) => current
    }
    val checked = TypeChecker.check(br.body, Some(TypeChecker.Expected(expected, None)), branchEnv)
    br.copy(body = checked.residual)
  }

  def checkMatch(term: Term.Match, env: Env, expected: Option[TypeChecker.Expected]): TypeChecker.CheckedTerm = {
    val checkedScrut = TypeChecker.checkTerm(term.scrut, env)
    // Nullary constructors are values at runtime even though their global
    // binding is published as a constructor head.
    val scrut = checkedScrut.value match {
      case head: ConstructorHead if head.totalArity == 0 => Value.canonicalizeProof(VCtor(head, Vector.empty, head.tpe))
      case value                                         => value
    }
    val family = scrut.tpe match {
      case InductiveFamilyValue(instance) => instance
      case _                              => throw NonInductiveMatch(scrut.tpe, Some(term.span))
    }
    val cases = term.cases.map(resolveCase(_, family))
    cases.groupBy(_.ctorName).collectFirst {
      case (name, duplicate) if duplicate.length > 1 =>
        throw DuplicateCase(name, Some(duplicate(1).span))
    }
    lazy val reachable = computeReachable(scrut, scrut.tpe, family, env)

    val explicitMotive = term.motive.map(motive => {
      val checked = TypeChecker.checkTerm(motive, env)
      TypeChecker.assertType(checked.value)
      checked
    })
    lazy val inferred: Value = {
      val first = reachable.headOption.getOrElse(
        throw MissingReturningClause("no constructors are reachable", Some(term.span))
      )
      if (!reachable.tail.forall(info => ValueEquivalence.defEq(first.resultTy, info.resultTy)))
        throw MissingReturningClause("reachable constructors have different result types", Some(term.span))
      TypeChecker.assertType(first.resultTy)
      first.resultTy
    }
    lazy val inherited: Option[(Value, Term)] = expected.map { exp =>
      val syntax = exp.syntax.getOrElse(
        throw MissingReturningClause("the match result is not syntactically available; add returning", Some(term.span))
      )
      exp.value -> syntax
    }
    val motiveValue = explicitMotive.map(_.value).orElse(inherited.map(_._1)).getOrElse(inferred)
    expected.foreach(exp => TypeChecker.checkFits(motiveValue, exp.value))
    checkPropElimination(family, scrut.tpe, motiveValue, reachable, term.span)

    var checkedByCtor = Map.empty[String, Case]
    scrut match {
      case ConstructorForm(ctorName, fields) =>
        cases.filterNot(_.ctorName == ctorName).foreach(c => throw UnreachableCase(c.ctorName, Some(c.span)))
        val branch = cases.find(_.ctorName == ctorName).getOrElse(throw MissingCase(ctorName, Some(term.span)))
        checkedByCtor += ctorName -> checkBranch(branch, fields, env, motiveValue)
      case packed: VPacked =>
        val (ctorName, fields) = packed.codec.decodeHead(packed)
        cases.filterNot(_.ctorName == ctorName).foreach(c => throw UnreachableCase(c.ctorName, Some(c.span)))
        val branch = cases.find(_.ctorName == ctorName).getOrElse(throw MissingCase(ctorName, Some(term.span)))
        checkedByCtor += ctorName -> checkBranch(branch, fields, env, motiveValue)
      case _ =>
        val reachableByName = reachable.map(info => info.name -> info).toMap
        family.meta.constructors.foreach { ctor =>
          reachableByName.get(ctor.canonicalName) match {
            case None =>
              cases.find(_.ctorName == ctor.canonicalName).foreach(c => throw UnreachableCase(c.ctorName, Some(c.span)))
            case Some(info) =>
              val branch = cases
                .find(_.ctorName == ctor.canonicalName)
                .getOrElse(
                  throw MissingCase(ctor.canonicalName, Some(term.span))
                )
              val branchEnv = ValueOps.materializeEnv(env, info.branchEqStore)
              val branchMotive = ValueOps.materialize(motiveValue, info.branchEqStore)
              checkedByCtor += info.name -> checkBranch(branch, info.fieldArgs, branchEnv, branchMotive)
          }
        }
    }
    val checkedCases = cases.map(c => checkedByCtor.getOrElse(c.ctorName, throw WTF(s"Unchecked case ${c.ctorName}")))
    val residual = Term.Match(
      checkedScrut.residual,
      explicitMotive.map(_.residual).orElse(inherited.map(_._2)),
      checkedCases,
      term.span
    )
    TypeChecker.CheckedTerm(Interpreter.evalTerm(residual, env), residual)
  }
}
