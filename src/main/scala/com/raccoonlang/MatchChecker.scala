package com.raccoonlang

import com.raccoonlang.TypeChecker._
import com.raccoonlang.Value._
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

  private def freshCtorArgsAndResult(head: ConstructorHead): (Vector[Value], Value) =
    head.tpe match {
      case pi: VPi =>
        val fresh = BinderOps.freshen(pi)
        val args = pi.binders.map(binder => fresh(binder.localRef))
        (args, pi.codomain(fresh))

      case _ => (Vector.empty, head.tpe)
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
          val (freshArgs, resultTy) = freshCtorArgsAndResult(h)
          val fieldArgs = freshArgs.drop(h.numErased)
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
    val (args1, res1) = freshCtorArgsAndResult(only.head)
    val (args2, res2) = freshCtorArgsAndResult(only.head)
    val fields1 = args1.drop(only.head.numErased)
    val fields2 = args2.drop(only.head.numErased)

    val refinable0 = DepSet.unionAll(scrutTpe.synDeps, res1.synDeps, res2.synDeps)

    val startEq = {
      val start = EqStore.empty.allow(refinable0)
      refineConstructorResult(res1, scrutTpe, start)
        .flatMap(eq1 => refineConstructorResult(res2, scrutTpe, eq1)) match {
        case Right(eqStore) => eqStore
        case Left(_)        => return false
      }
    }

    fields1.zip(fields2).forall { case (f1, f2) =>
      val mf1 = ValueOps.materialize(f1, startEq)
      val mf2 = ValueOps.materialize(f2, startEq)
      TypeChecker.getUniverse(mf1.tpe) match {
        case PropTpe => true
        case _       => ValueEquivalence.defEq(mf1, mf2)
      }
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

  private def checkBranch(br: CA.Case, args: Seq[Value], envWithScrut: Env, expectedTy: Value): EA.Case = {
    if (args.length != br.argRefs.length)
      throw ArityMismatch(args.length, br.argRefs.length, Some(br.span))
    val branchEnv = br.argRefs.zip(args).foldLeft(envWithScrut) { case (curEnv, (argRef, argVal)) =>
      argRef match {
        case Some(ref) => curEnv.putLocal(ref, argVal)
        case None      => curEnv
      }
    }
    val branchRes = checkTerm(br.body, branchEnv)
    checkType(branchRes.value, expectedTy)
    EA.Case(
      br.ctorName,
      br.argRefs,
      branchRes.residual,
      br.span
    )
  }

  def checkMatch(t: CA.Term.Match, env: Env): CheckedTerm = {
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

    val checkedMotive = t.motive.map(motiveSyntax => checkTypeTerm(motiveSyntax, env))
    val motiveTy = checkedMotive match {
      case Some(motive) => motive.value
      case None         => inferMotiveFromReachable(reachableByType)
    }

    checkPropElimination(inductiveName, scrutTpe, motiveTy, reachableByType, t.span)

    var checkedByCtor = Map.empty[String, EA.Case]

    scrut match {
      case VCtor(h, fields, _) =>
        cases.find(_.ctorName != h.name).foreach { c =>
          throw UnreachableCase(c.ctorName, Some(c.span))
        }

        val br = cases.find(_.ctorName == h.name).getOrElse(throw MissingCase(h.name))
        checkedByCtor += h.name -> checkBranch(br, fields, env, motiveTy)

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
      checkedMotive.map(_.residual),
      checkedCases,
      t.span,
      t.nodeId
    )
    CheckedTerm(Interpreter.evalTerm(checkedMatch, env), checkedMatch)
  }

}
