package com.raccoonlang

import com.raccoonlang.TypeChecker._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA}

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
      cases: Vector[CA.Case],
      env: Env
  ): Vector[ReachableCtor] = {
    def unify(left: Value, right: Value, refinable: Refinable): Either[ValueEquivalence.UnifyFailure, EqStore] =
      ValueEquivalence.tryUnify(left, right, EqStore.empty.allowEta(refinable.ids, refinable.vars))

    // What a unification may refine: the ids, which are the authority, together with the `Var`
    // objects behind them. `EqStore.allowEta` needs the variables themselves because admitting one
    // at an eta-eligible struct type also expands it, which takes its type. Ids without a variable
    // (level parameters) stay refinable exactly as before.
    final case class Refinable(ids: DepSet, vars: Vector[Var]) {
      def ++(other: Refinable): Refinable = Refinable(ids ++ other.ids, vars ++ other.vars)
    }

    def refinableIn(value: Value, ids: DepSet): Refinable = Refinable(ids, Value.varsIn(value, ids))

    // The variables the scrutinee is blocked on, and the ids that blocking reported.
    def rootRefinable(value: Value): Refinable =
      value match {
        case Blocker(blockedOn) => refinableIn(value, blockedOn)
        case _                  => Refinable(DepSet.empty, Vector.empty)
      }

    ctorNames.flatMap { ctorName =>
      env(ctorName) match {
        case h: ConstructorHead =>
          val fieldNames =
            cases.find(_.ctorName == ctorName).fold(Vector.empty[Option[String]])(_.argRefs.map(_.map(_.name)))
          val (freshArgs, resultTy) = BinderOps.freshCtorArgsAndResult(h, fieldNames)
          val storedArgs = Value.constructorStoredArgs(h, freshArgs)
          val ctorValue = Value.canonicalizeProof(
            Packed.foldCtor(h, storedArgs, resultTy).getOrElse(VCtor(h, storedArgs, resultTy))
          )
          val ctorRefinable = refinableIn(ctorValue, ctorValue.synDeps)
          val valueRefinable = rootRefinable(scrut) ++ ctorRefinable
          val typeRefinable = refinableIn(scrutTpe, scrutTpe.synDeps) ++ ctorRefinable

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

        case _ => fail(UnknownConstructor(ctorName, inductiveName))
      }
    }
  }

  private def allowLargeElimination(scrutTpe: Value, reachable: Vector[ReachableCtor]): Boolean =
    reachable.isEmpty || ProofReconstruction.canRecoverAll(scrutTpe)

  private def checkPropElimination(
      inductiveName: String,
      scrutTpe: Value,
      motiveTy: Value,
      reachable: => Vector[ReachableCtor]
  ): Unit =
    if (isPropValuedType(scrutTpe) && !isPropValuedType(motiveTy) && !allowLargeElimination(scrutTpe, reachable))
      fail(PropEliminationRestricted(inductiveName, motiveTy))

  /** The branch boundary: locates and frames failures in the pattern and the refined environment around the body. */
  private def checkBranch(
      br: CA.Case,
      args: Seq[Value],
      envWithScrut: Env,
      expectedTy: Value
  ): CA.Case =
    framed(Frame.InBranch(br.ctorName, br.argRefs.map(_.fold("_")(_.name)))) {
      at(br.span) {
        if (args.length != br.argRefs.length) fail(ArityMismatch(args.length, br.argRefs.length))
        val branchEnv = br.argRefs.zip(args).foldLeft(envWithScrut) { case (curEnv, (argRef, argVal)) =>
          argRef match {
            // Proof recovery stores recursive proof fields shallowly. Crossing the pattern
            // boundary exposes one such field, so put it into the canonical form for its exact type.
            case Some(ref) => curEnv.putLocal(ref, Value.canonicalizeProof(argVal))
            case None      => curEnv
          }
        }
        val branchRes = checkTerm(br.body, expectedTy, branchEnv)
        br.copy(body = branchRes.residual)
      }
    }

  def checkMatch(t: CA.Term.Match, env: Env, expected: Option[Expected] = None): CheckedTerm = {
    val scrutChecked = checkTerm(t.scrut, env)
    val scrut = scrutChecked.value
    val scrutTpe = scrut.tpe

    val inductiveFamily = scrutTpe match {
      case InductiveFamilyValue(instance) => instance
      case _                              => fail(NonInductiveMatch(scrut.tpe))
    }
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
        case Vector(name) => c.copy(ctorName = name, isFullyQualified = true)
        case Vector()     => at(c.span) { fail(UnknownConstructor(c.ctorName, inductiveName)) }
        case many         => at(c.span) { fail(AmbiguousName(c.ctorName, many)) }
      }
    }

    cases.groupBy(_.ctorName).find(_._2.length > 1).foreach { case (ctor, duplicateCases) =>
      at(duplicateCases(1).span) { fail(DuplicateCase(ctor)) }
    }

    lazy val reachableByType: Vector[ReachableCtor] =
      computeReachableCtors(scrut, scrutTpe, inductiveName, inductiveCtorNames, cases, env)

    def inferMotiveFromReachable(reachable: Vector[ReachableCtor]): Value = {
      val first = reachable.headOption.getOrElse(fail(MissingReturningClause("no constructors are reachable")))
      val inferred = first.resultTy
      val allEqual = reachable.tail.forall { info =>
        ValueEquivalence.defEq(inferred, info.resultTy)
      }
      if (!allEqual) fail(MissingReturningClause("reachable constructors have different result types"))
      assertType(inferred)
      inferred
    }

    val checkedMotive = t.motive.map(motiveSyntax => checkTerm(motiveSyntax, env))

    // The motive inherited from the expectation, for a match with no `returning` clause.
    //
    // A residual is re-evaluated later, so the motive must be *syntax* valid in this env. Under an
    // expectation, the only such syntax is the one the expectation carries — a declared return type
    // the program wrote down. When the expectation is a bare value (an application argument's binder
    // type, a branch's own motive), there is nothing to write into the residual, so the program must
    // supply a `returning` clause itself. Lazy, because a user-written clause supersedes the
    // expectation entirely: a syntax-less expectation is only an error when no clause was given.
    lazy val inheritedMotive: Option[(Value, CA.Term)] =
      expected.map { exp =>
        val syntax = exp.syntax.getOrElse(
          fail(MissingReturningClause("the match's result type is not syntactically in scope; add a returning clause"))
        )
        (exp.value, syntax)
      }

    val motiveTy = checkedMotive match {
      case Some(motive) => motive.value
      case None =>
        inheritedMotive match {
          case Some((value, _)) => value
          // No expectation at all: the branches must all agree on the scrutinee's own type, and the
          // residual motive stays `None`, which means exactly that (Interpreter.matchOutType).
          case None => inferMotiveFromReachable(reachableByType)
        }
    }
    expected.foreach(exp => checkFits(motiveTy, exp.value))

    checkPropElimination(inductiveName, scrutTpe, motiveTy, reachableByType)

    var checkedByCtor = Map.empty[String, CA.Case]

    scrut match {
      case ConstructorForm(ctorName, storedArgs) =>
        cases.find(_.ctorName != ctorName).foreach { c =>
          at(c.span) { fail(UnreachableCase(c.ctorName)) }
        }

        val br = cases.find(_.ctorName == ctorName).getOrElse(fail(MissingCase(ctorName)))
        checkedByCtor += ctorName -> checkBranch(br, storedArgs, env, motiveTy)

      case _ =>
        val reachableMap = reachableByType.map(info => info.name -> info).toMap

        inductiveCtorNames.foreach { ctorName =>
          reachableMap.get(ctorName) match {
            case None =>
              cases.find(_.ctorName == ctorName).foreach { c =>
                at(c.span) { fail(UnreachableCase(ctorName)) }
              }

            case Some(info) =>
              val br = cases.find(_.ctorName == ctorName).getOrElse(fail(MissingCase(ctorName)))
              val branchStore = info.branchEqStore
              val branchEnv = ValueOps.materializeEnv(env, branchStore)
              val branchArgs = info.fieldArgs.map(arg => ValueOps.materialize(arg, branchStore))
              val branchMotiveTy = ValueOps.materialize(motiveTy, branchStore)
              checkedByCtor += ctorName -> checkBranch(br, branchArgs, branchEnv, branchMotiveTy)
          }
        }
    }

    val checkedCases = cases.map { c =>
      checkedByCtor.getOrElse(c.ctorName, wtf(s"Unchecked reachable case ${c.ctorName}"))
    }
    val checkedMatch = CA.Term.Match(
      scrutChecked.residual,
      // orElse is by-name: `inheritedMotive` is only forced when there is no user clause.
      checkedMotive.map(_.residual).orElse(inheritedMotive.map(_._2)),
      checkedCases,
      t.span
    )
    val value = expected match {
      case Some(_) => Interpreter.evalTerm(checkedMatch, env)
      case None    => Interpreter.evalTerm(checkedMatch, env)
    }
    CheckedTerm(value, checkedMatch)
  }

}
