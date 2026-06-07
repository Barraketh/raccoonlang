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

  private def computeReachableCtors(
      scrut: Value,
      scrutTpe: Value,
      inductiveName: String,
      ctorNames: Vector[String],
      env: Env
  ): Vector[ReachableCtor] = {
    def tryUnify(left: Value, right: Value, refinable: DepSet): Option[EqStore] =
      ValueEquivalence.tryUnify(left, right, EqStore.empty.allow(refinable), env.normalizers).toOption

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

          val branchEqStore =
            tryUnify(scrut, ctorValue, valueRefinable)
              .orElse(tryUnify(resultTy, scrutTpe, typeRefinable))

          branchEqStore.map { branchStore =>
            val refinedResultTy = ValueOps.materialize(scrutTpe, branchStore)
            ReachableCtor(ctorName, h, fieldArgs, refinedResultTy, branchStore)
          }

        case _ => throw UnknownConstructor(ctorName, inductiveName)
      }
    }
  }

  private def allowLargeElimination(
      scrutTpe: Value,
      reachable: Vector[ReachableCtor],
      normalizerMap: Normalizers.NormalizerMap
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
      ValueEquivalence
        .tryUnify(res1, scrutTpe, start, normalizerMap)
        .flatMap(eq1 => ValueEquivalence.tryUnify(res2, scrutTpe, eq1, normalizerMap)) match {
        case Right(eqStore) => eqStore
        case Left(_)        => return false
      }
    }

    fields1.zip(fields2).forall { case (f1, f2) =>
      val mf1 = ValueOps.materialize(f1, startEq)
      val mf2 = ValueOps.materialize(f2, startEq)
      TypeChecker.getUniverse(mf1.tpe) match {
        case PropTpe => true
        case _       => ValueEquivalence.defEq(mf1, mf2, normalizerMap, propIrrelevant = true)
      }
    }
  }

  private def checkPropElimination(
      inductiveName: String,
      scrutTpe: Value,
      motiveTy: Value,
      reachable: => Vector[ReachableCtor],
      normalizerMap: Normalizers.NormalizerMap,
      span: Span
  ): Unit =
    if (getUniverse(scrutTpe) == PropTpe && !isPropValuedType(motiveTy)) {
      if (!allowLargeElimination(scrutTpe, reachable, normalizerMap))
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
    checkType(branchRes.value, expectedTy, branchEnv.normalizers)
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
        ValueEquivalence.defEq(inferred, info.resultTy, env.normalizers, propIrrelevant = true)
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

    checkPropElimination(inductiveName, scrutTpe, motiveTy, reachableByType, env.normalizers, t.span)

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
      t.span
    )
    CheckedTerm(Interpreter.evalTerm(checkedMatch, env), checkedMatch)
  }

}
