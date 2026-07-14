package com.raccoonlang

import com.raccoonlang.TypeChecker._
import com.raccoonlang.Value._
import com.raccoonlang.ValueQuote.{quoteContext, quoteTerm}
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

object MatchChecker {

  private final case class ReachableCtor(
      name: String,
      head: ConstructorHead,
      fieldArgs: Vector[Value],
      resultTy: Value,
      branchEqStore: EqStore
  )

  private def computeReachableCtors(
      scrut: Value,
      scrutTpe: Value,
      inductiveName: String,
      ctorNames: Vector[String],
      env: Env
  ): Vector[ReachableCtor] = {
    def unify(left: Value, right: Value, refinable: DepSet): Either[ValueEquivalence.UnifyFailure, EqStore] =
      ValueEquivalence.tryUnify(left, right, EqStore.empty.allow(refinable))

    def rootRefinable(value: Value): DepSet =
      value match {
        case Blocker(blockerId) => DepSet(blockerId)
        case _                  => DepSet.empty
      }

    ctorNames.flatMap { ctorName =>
      env(ctorName) match {
        case h: ConstructorHead =>
          val (freshArgs, resultTy) = BinderOps.freshCtorArgsAndResult(h)
          val storedArgs = Value.constructorStoredArgs(h, freshArgs)
          // For a Prop scrutinee the ctor value collapses, so the value probe below degenerates
          // to the type probe (proof-collapse.md §5).
          val ctorValue = Value.collapseIfProof(VCtor(h, storedArgs, resultTy))
          val valueRefinable = rootRefinable(scrut) ++ ctorValue.synDeps
          val typeRefinable = scrutTpe.synDeps ++ ctorValue.synDeps

          // A constructor may only be pruned on a provably-apart unification failure. A merely stuck
          // failure keeps the branch required but yields no refinement: checking it with fewer
          // equations is conservative, whereas pruning on it would refute equations that may hold
          // propositionally (e.g. via Quot.sound).
          val branchEqStore =
            unify(scrut, ctorValue, valueRefinable) match {
              case Right(store)       => Some(store)
              case Left(f) if f.apart => None
              case Left(_) =>
                unify(resultTy, scrutTpe, typeRefinable) match {
                  case Right(store)       => Some(store)
                  case Left(f) if f.apart => None
                  case Left(_)            => Some(EqStore.empty)
                }
            }

          branchEqStore.map { branchStore =>
            val refinedResultTy = ValueOps.materialize(scrutTpe, branchStore)
            ReachableCtor(ctorName, h, storedArgs, refinedResultTy, branchStore)
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
    val (args1, res1) = BinderOps.freshCtorArgsAndResult(only.head)
    val (args2, res2) = BinderOps.freshCtorArgsAndResult(only.head)
    val fields1 = Value.constructorStoredArgs(only.head, args1)
    val fields2 = Value.constructorStoredArgs(only.head, args2)

    val refinable0 = DepSet.unionAll(scrutTpe.synDeps, res1.synDeps, res2.synDeps)

    val startEq = {
      val start = EqStore.empty.allow(refinable0)
      ValueEquivalence
        .tryUnify(res1, scrutTpe, start)
        .flatMap(eq1 => ValueEquivalence.tryUnify(res2, scrutTpe, eq1)) match {
        case Right(eqStore) => eqStore
        case Left(_)        => return false
      }
    }

    fields1.zip(fields2).forall { case (f1, f2) =>
      val mf1 = ValueOps.materialize(f1, startEq)
      val mf2 = ValueOps.materialize(f2, startEq)
      isPropValuedType(mf1.tpe) || ValueEquivalence.defEq(mf1, mf2)
    }
  }

  private def checkPropElimination(
      inductiveName: String,
      scrutTpe: Value,
      motiveTy: Value,
      reachable: => Vector[ReachableCtor],
      span: Span
  ): Unit =
    if (isPropValuedType(scrutTpe) && !isPropValuedType(motiveTy)) {
      if (!allowLargeElimination(scrutTpe, reachable))
        throw PropEliminationRestricted(inductiveName, motiveTy, Some(span))
    }

  private def checkBranch(
      br: CA.Case,
      args: Seq[Value],
      envWithScrut: Env,
      expectedTy: Value
  ): EA.Case = {
    if (args.length != br.argRefs.length)
      throw ArityMismatch(args.length, br.argRefs.length, Some(br.span))
    val branchEnv = br.argRefs.zip(args).foldLeft(envWithScrut) { case (curEnv, (argRef, argVal)) =>
      argRef match {
        case Some(ref) => curEnv.putLocal(ref, argVal)
        case None      => curEnv
      }
    }
    val branchRes = checkTerm(br.body, expectedTy, branchEnv)
    EA.Case(
      br.ctorName,
      br.argRefs,
      branchRes.residual,
      br.span
    )
  }

  def checkMatch(t: CA.Term.Match, env: Env, expectedTy: Option[Value] = None): CheckedTerm = {
    val scrutChecked = checkTerm(t.scrut, env)
    val scrut = scrutChecked.value
    val scrutTpe = scrut.tpe

    val inductiveFamily = inductiveFamilyOf(scrutTpe).getOrElse(throw NonInductiveMatch(scrut.tpe))
    val inductiveName = inductiveFamily.head.name
    val inductiveMeta = inductiveFamily.meta
    val inductiveCtorNames = inductiveMeta.constructorNames
    val cases = t.cases.map { c =>
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

    cases.groupBy(_.ctorName).find(_._2.length > 1).foreach { case (ctor, duplicateCases) =>
      throw DuplicateCase(ctor, Some(duplicateCases(1).span))
    }

    lazy val reachableByType: Vector[ReachableCtor] =
      computeReachableCtors(scrut, scrutTpe, inductiveName, inductiveCtorNames, env)

    def inferMotiveFromReachable(reachable: Vector[ReachableCtor]): Value = {
      val first = reachable.headOption.getOrElse {
        throw MissingReturningClause("no constructors are reachable", Some(t.span))
      }
      val inferred = first.resultTy
      val allEqual = reachable.tail.forall { info =>
        ValueEquivalence.defEq(inferred, info.resultTy)
      }
      if (!allEqual)
        throw MissingReturningClause("reachable constructors have different result types", Some(t.span))
      assertType(inferred)
      inferred
    }

    val checkedMotive = t.motive.map(motiveSyntax => checkTerm(motiveSyntax, env))
    val motiveTy = checkedMotive match {
      case Some(motive) => motive.value
      case None if expectedTy.nonEmpty =>
        expectedTy.get
      case None => inferMotiveFromReachable(reachableByType)
    }
    expectedTy.foreach(expected => checkFits(motiveTy, expected))

    checkPropElimination(inductiveName, scrutTpe, motiveTy, reachableByType, t.span)

    var checkedByCtor = Map.empty[String, EA.Case]

    scrut match {
      case VCtor(h, storedArgs, _) =>
        cases.find(_.ctorName != h.name).foreach { c =>
          throw UnreachableCase(c.ctorName, Some(c.span))
        }

        val br = cases.find(_.ctorName == h.name).getOrElse(throw MissingCase(h.name))
        checkedByCtor += h.name -> checkBranch(br, storedArgs, env, motiveTy)

      case _ =>
        val reachableMap = reachableByType.map(info => info.name -> info).toMap

        inductiveCtorNames.foreach { ctorName =>
          reachableMap.get(ctorName) match {
            case None =>
              cases.find(_.ctorName == ctorName).foreach { c =>
                throw UnreachableCase(ctorName, Some(c.span))
              }

            case Some(info) =>
              val br = cases.find(_.ctorName == ctorName).getOrElse(throw MissingCase(ctorName))
              val branchStore = info.branchEqStore
              val branchEnv = ValueOps.materializeEnv(env, branchStore)
              val branchArgs = info.fieldArgs.map(arg => ValueOps.materialize(arg, branchStore))
              val branchMotiveTy = ValueOps.materialize(motiveTy, branchStore)
              checkedByCtor += ctorName -> checkBranch(br, branchArgs, branchEnv, branchMotiveTy)
          }
        }
    }

    val checkedCases = cases.map { c =>
      checkedByCtor.getOrElse(c.ctorName, throw WTF(s"Unchecked reachable case ${c.ctorName}"))
    }
    val checkedMatch = EA.Term.Match(
      scrutChecked.residual,
      // orElse is by-name: the expected type is only quoted when there is no user motive.
      checkedMotive
        .map(_.residual)
        .orElse(expectedTy.map(expected => quoteTerm(expected, quoteContext(env), t.span))),
      checkedCases,
      t.span,
      t.span.nodeId
    )
    val value = expectedTy match {
      case Some(expected) => Value.ascribe(Interpreter.evalTerm(checkedMatch, env), expected)
      case None           => Interpreter.evalTerm(checkedMatch, env)
    }
    CheckedTerm(value, checkedMatch)
  }

}
