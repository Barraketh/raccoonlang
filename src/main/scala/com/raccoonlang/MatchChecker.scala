package com.raccoonlang

import com.raccoonlang.TypeChecker._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}
import com.raccoonlang.ValueQuote.{quoteContext, quoteType}

object MatchChecker {

  private final case class ReachableCtor(
      name: String,
      head: ConstructorHead,
      fieldArgs: Vector[Value],
      resultTy: Value,
      branchEqStore: EqStore
  )

  private final case class FreshCtor(fieldArgs: Vector[Value], captures: Vector[Value], resultTy: Value)

  private def freshCtor(head: ConstructorHead): FreshCtor =
    head.tpe match {
      case pi: VPi =>
        val fresh = BinderOps.freshen(pi)
        val args = pi.binders.map(binder => fresh(binder.localRef))
        val captures = pi.binders.flatMap(_.captures).map(capture => fresh(capture.localRef))
        FreshCtor(args.drop(head.numErased), captures, pi.codomain(fresh))

      case _ => FreshCtor(Vector.empty, Vector.empty, head.tpe)
    }

  /**
   * A constructor branch must inhabit the scrutinee's declared fiber. Its result telescope therefore supplies equations
   * between the corresponding family arguments, including for Prop families. These are premises of indexed elimination,
   * not consequences of injectivity of the family as a type-valued expression.
   */
  private def refineConstructorResult(
      constructorResult: Value,
      scrutineeType: Value,
      store: EqStore
  ): Either[ValueEquivalence.UnificationFailure, EqStore] = {
    val result = ValueOps.materialize(constructorResult, store)
    val scrutinee = ValueOps.materialize(scrutineeType, store)
    (result, scrutinee) match {
      case (InductiveFamilyValue(ctorFamily), InductiveFamilyValue(scrutineeFamily))
          if ctorFamily.head.name == scrutineeFamily.head.name &&
            ctorFamily.args.length == scrutineeFamily.args.length =>
        val equations = ctorFamily.args.zip(scrutineeFamily.args) :+ (result.tpe -> scrutinee.tpe)
        equations.foldLeft[Either[ValueEquivalence.UnificationFailure, EqStore]](Right(store)) {
          case (current, (left, right)) => current.flatMap(ValueEquivalence.tryUnify(left, right, _))
        }
      case _ => throw WTF("Constructor result does not belong to the scrutinee's inductive family")
    }
  }

  private def computeReachableCtors(
      scrut: Value,
      scrutTpe: Value,
      inductiveName: String,
      ctorNames: Vector[String],
      env: Env
  ): Vector[ReachableCtor] = {
    import ValueEquivalence.UnificationFailure._

    def tryUnify(left: Value, right: Value, refinable: DepSet) =
      ValueEquivalence.tryUnify(left, right, EqStore.empty.allow(refinable))

    def rootRefinable(value: Value): DepSet =
      value match {
        case Blocker(blockerId) => DepSet(blockerId)
        case _                  => DepSet.empty
      }

    ctorNames.flatMap { ctorName =>
      env(ctorName) match {
        case h: ConstructorHead =>
          val FreshCtor(fieldArgs, _, resultTy) = freshCtor(h)
          val ctorValue = VCtor(h, fieldArgs, resultTy)
          val valueRefinable = rootRefinable(scrut) ++ ctorValue.synDeps
          val typeRefinable = scrutTpe.synDeps ++ ctorValue.synDeps

          val valueRefinement = tryUnify(scrut, ctorValue, valueRefinable)
          val refinement = valueRefinement match {
            case Left(_: Stuck) =>
              refineConstructorResult(resultTy, scrutTpe, EqStore.empty.allow(typeRefinable))
            case other => other
          }
          val branchStore = refinement match {
            case Right(store)           => Some(store)
            case Left(_: Contradiction) => None
            case Left(_: Stuck)         => Some(EqStore.empty)
          }

          branchStore.map { store =>
            val refinedResultTy = ValueOps.materialize(scrutTpe, store)
            ReachableCtor(ctorName, h, fieldArgs, refinedResultTy, store)
          }

        case _ => throw UnknownConstructor(ctorName, inductiveName)
      }
    }
  }

  private def allowLargeElimination(
      scrutTpe: Value,
      reachable: Vector[ReachableCtor]
  ): Boolean = {
    if (reachable.isEmpty) return true
    if (reachable.length > 1) return false

    val only = reachable.head
    val FreshCtor(fields1, captures1, res1) = freshCtor(only.head)
    val FreshCtor(fields2, captures2, res2) = freshCtor(only.head)

    val refinable0 = DepSet.unionAll(scrutTpe.synDeps, res1.synDeps, res2.synDeps)

    val startEq = {
      val start = EqStore.empty.allow(refinable0)
      refineConstructorResult(res1, scrutTpe, start)
        .flatMap(eq1 => refineConstructorResult(res2, scrutTpe, eq1)) match {
        case Right(eqStore) => eqStore
        case Left(_)        => return false
      }
    }

    // Type-pattern captures are implicit constructor arguments, including when
    // hidden in a proof field's type. They must already agree after result
    // refinement; no extra equations may equate otherwise independent choices.
    (fields1 ++ captures1).zip(fields2 ++ captures2).forall { case (f1, f2) =>
      val mf1 = ValueOps.materialize(f1, startEq)
      val mf2 = ValueOps.materialize(f2, startEq)
      // Proof irrelevance applies only at the same proposition. defEq erases
      // proof values after comparing their types, while data must agree too.
      ValueEquivalence.defEq(mf1.tpe, mf2.tpe) && ValueEquivalence.defEq(mf1, mf2)
    }
  }

  private def checkPropElimination(
      inductiveName: String,
      scrutTpe: Value,
      motiveTy: Value,
      reachable: => Vector[ReachableCtor],
      span: Span
  ): Unit =
    if (getUniverse(scrutTpe) == PropTpe && getUniverse(motiveTy) != PropTpe) {
      if (!allowLargeElimination(scrutTpe, reachable))
        throw PropEliminationRestricted(inductiveName, motiveTy, Some(span))
    }

  private final case class PlannedBranch(
      br: CA.Case,
      args: Vector[Value],
      branchEnv: Env,
      store: EqStore
  )

  private final case class CheckedBranch(
      residual: EA.Case,
      checkedBody: CheckedTerm,
      store: EqStore
  )

  private def checkBranch(
      planned: PlannedBranch,
      expected: Option[CheckedTypeTerm]
  ): CheckedBranch = {
    val br = planned.br
    val args = planned.args
    if (args.length != br.argRefs.length)
      throw ArityMismatch(args.length, br.argRefs.length, Some(br.span))
    val branchEnv = br.argRefs.zip(args).foldLeft(planned.branchEnv) { case (curEnv, (argRef, argVal)) =>
      argRef match {
        case Some(ref) => curEnv.putLocal(ref, argVal)
        case None      => curEnv
      }
    }
    val branchRes = expected match {
      case Some(motive) =>
        val branchMotive = motive.copy(value = ValueOps.materialize(motive.value, planned.store))
        checkTermAgainst(br.body, branchEnv, branchMotive)
      case None => checkTerm(br.body, branchEnv)
    }
    CheckedBranch(
      EA.Case(br.ctorName, br.argRefs, branchRes.residual, br.span),
      branchRes,
      planned.store
    )
  }

  def checkMatch(t: CA.Term.MatchTerm, env: Env, contextualExpected: Option[CheckedTypeTerm] = None): CheckedTerm = {
    val span = t.span
    val scrutChecked = checkTerm(t.scrut, env)
    val scrut = scrutChecked.value
    val scrutTpe = scrut.tpe

    val inductiveFamily = inductiveFamilyOf(scrutTpe).getOrElse(throw NonInductiveMatch(scrut.tpe))
    val inductiveName = inductiveFamily.head.name
    val inductiveMeta = inductiveFamily.meta
    val inductiveCtorNames = inductiveMeta.constructorNames
    val cases = t match {
      case single: CA.Term.MatchOne =>
        if (inductiveCtorNames.length != 1)
          throw InvalidSingleConstructorMatch(
            scrutTpe,
            s"the family declares ${inductiveCtorNames.length} constructors",
            Some(span)
          )
        val ctorName = inductiveCtorNames.head
        val head = env(ctorName) match {
          case constructor: ConstructorHead => constructor
          case _ => throw WTF(s"Inductive metadata points to non-constructor $ctorName", Some(span))
        }
        val storedArity = head.totalArity - head.numErased
        if (single.fieldRefs.length != storedArity)
          throw InvalidDestructuring(
            s"expected $storedArity stored fields, got ${single.fieldRefs.length}",
            Some(span)
          )
        Vector(CA.Case(ctorName, true, single.fieldRefs.map(Some(_)), single.body, span))
      case named: CA.Term.Match =>
        named.cases.map { c =>
          val candidates =
            if (c.isFullyQualified) inductiveMeta.constructors.collect {
              case ctor if ctor.canonicalName == c.ctorName => ctor.canonicalName
            }
            else
              inductiveMeta.constructors.collect {
                case ctor if ctor.shortName == c.ctorName => ctor.canonicalName
              }
          candidates match {
            case Vector(name) => c.copy(ctorName = name)
            case Vector()     => throw UnknownConstructor(c.ctorName, inductiveName, Some(c.span))
            case many         => throw AmbiguousName(c.ctorName, many, Some(c.span))
          }
        }
    }

    val resolvedCases = cases

    resolvedCases.groupBy(_.ctorName).find(_._2.length > 1).foreach { case (ctor, duplicateCases) =>
      throw DuplicateCase(ctor, Some(duplicateCases(1).span))
    }

    lazy val reachableByType: Vector[ReachableCtor] =
      computeReachableCtors(scrut, scrutTpe, inductiveName, inductiveCtorNames, env)

    val checkedSourceMotive = t.motive.map(syntax => checkTypeTerm(syntax, env))
    val expectedMotive = checkedSourceMotive.orElse(contextualExpected)
    expectedMotive.foreach(motive => assertType(motive.value))
    expectedMotive.foreach(motive => checkPropElimination(inductiveName, scrutTpe, motive.value, reachableByType, span))

    val plannedBranches: Vector[PlannedBranch] = scrut match {
      case VCtor(head, fields, _) =>
        resolvedCases.find(_.ctorName != head.name).foreach { c =>
          throw UnreachableCase(c.ctorName, Some(c.span))
        }
        val br = resolvedCases.find(_.ctorName == head.name).getOrElse(throw MissingCase(head.name))
        Vector(PlannedBranch(br, fields, env, EqStore.empty))

      case _ =>
        val reachableMap = reachableByType.map(info => info.name -> info).toMap
        inductiveCtorNames.flatMap { ctorName =>
          reachableMap.get(ctorName) match {
            case None =>
              resolvedCases.find(_.ctorName == ctorName).foreach { c =>
                throw UnreachableCase(ctorName, Some(c.span))
              }
              None
            case Some(info) =>
              val br = resolvedCases.find(_.ctorName == ctorName).getOrElse(throw MissingCase(ctorName))
              Some(
                PlannedBranch(
                  br,
                  info.fieldArgs.map(arg => ValueOps.materialize(arg, info.branchEqStore)),
                  ValueOps.materializeEnv(env, info.branchEqStore),
                  info.branchEqStore
                )
              )
          }
        }
    }

    val checkedBranches = plannedBranches.map(branch => checkBranch(branch, expectedMotive))
    val chosenMotive = expectedMotive.getOrElse {
      val first = checkedBranches.headOption.getOrElse {
        throw MissingReturningClause("no reachable branches have a result type to infer", Some(span))
      }
      val candidate = ValueOps.materialize(first.checkedBody.value.tpe, first.store)
      val changedLocalIds = env.locals.zipWithIndex.collect {
        case (binding, index) if binding.valueOption.exists { original =>
              !ValueEquivalence.defEq(original.tpe, ValueOps.materialize(original, first.store).tpe)
            } =>
          index
      }.toSet
      val context = quoteContext(env)
      val safeContext = context.copy(
        quote = context.quote.filterNot { case (_, entry) =>
          entry.term match {
            case EA.Term.LocalRef(ref, _) => changedLocalIds.contains(ref.id)
            case _                        => false
          }
        }
      )
      val residual =
        try quoteType(candidate, safeContext, span)
        catch {
          case _: CannotQuoteValue =>
            throw MissingReturningClause(
              "the common branch result type cannot be expressed outside the match",
              Some(span)
            )
        }
      val value = Interpreter.evalTypeTerm(residual, env)
      assertType(value)
      checkPropElimination(inductiveName, scrutTpe, value, reachableByType, span)
      checkedBranches.foreach { branch =>
        val branchValue = ValueOps.materialize(branch.checkedBody.value, branch.store)
        val branchExpected = ValueOps.materialize(value, branch.store)
        checkType(branchValue, branchExpected)
      }
      CheckedTypeTerm(value, residual)
    }
    val checkedMatch = EA.Term.Match(
      scrutChecked.residual,
      Some(chosenMotive.residual),
      checkedBranches.map(_.residual),
      span,
      t.nodeId
    )
    val value = scrut match {
      case VCtor(_, _, _) =>
        checkedBranches.headOption.map(_.checkedBody.value).getOrElse {
          throw WTF("Known constructor match had no checked branch", Some(span))
        }
      case _ => Interpreter.stuckMatch(checkedMatch, scrut, env, chosenMotive.value)
    }
    CheckedTerm(value, checkedMatch)
  }

}
