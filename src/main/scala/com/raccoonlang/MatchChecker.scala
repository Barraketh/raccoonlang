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
      family: InductiveFamilyInstance,
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

    family.meta.constructorNames.flatMap { ctorName =>
      env(ctorName) match {
        case h: ConstructorHead =>
          val fieldRefs = cases.find(_.ctorName == ctorName).fold(Vector.empty[CA.LocalRef])(_.argRefs)
          // The constructor's parameters are the scrutinee type's own, so they need no equation, and a stuck index
          // equation cannot leave a field's type over parameters nothing binds. Only the fresh fields are unknowns:
          // they are exactly what the constructor value mentions beyond the scrutinee type.
          val (fields, resultTy) = BinderOps.freshCtorFields(h, family.args, fieldRefs)
          val ctorValue = Value.canonicalizeProof(
            Packed.foldCtor(h, fields, resultTy).getOrElse(VCtor(h, fields, resultTy))
          )
          val ctorRefinable = refinableIn(ctorValue, ctorValue.synDeps -- scrutTpe.synDeps)
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
            ReachableCtor(ctorName, h, fields, refinedResultTy, branchStore)
          }

        case _ => fail(UnknownConstructor(ctorName, family.head.name))
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
    if (Sorts.isProposition(scrutTpe) && !Sorts.isProposition(motiveTy) && !allowLargeElimination(scrutTpe, reachable))
      fail(PropEliminationRestricted(inductiveName, motiveTy))

  /** The branch boundary: locates and frames failures in the pattern and the refined environment around the body. */
  private def checkBranch(
      br: CA.Case,
      args: Seq[Value],
      envWithScrut: Env,
      expectedTy: Value
  ): CA.Case =
    framed(Frame.InBranch(br.ctorName, br.argRefs.map(_.name))) {
      at(br.span) {
        if (args.length != br.argRefs.length) fail(ArityMismatch(args.length, br.argRefs.length))
        // Proof recovery stores recursive proof fields shallowly. Crossing the pattern boundary exposes one such
        // field, so put it into the canonical form for its exact type. A field's type is its local's type at its
        // binder, so it is confined there (spec §4.2).
        val branchEnv = br.argRefs.zip(args).foldLeft(envWithScrut) { case (curEnv, (ref, argVal)) =>
          requireInScope(argVal.tpe, curEnv)
          curEnv.putLocal(ref, Value.canonicalizeProof(argVal))
        }
        val branchRes = checkTerm(br.body, expectedTy, branchEnv)
        // Each field is released to the ledger at the branch's extent (spec §6.1), a wildcard's included.
        br.argRefs.zip(args).foreach { case (ref, argVal) =>
          Ledger.requireUsedOnce(ref, argVal.tpe, br.span, Vector(branchRes.residual))
        }
        br.copy(body = branchRes.residual)
      }
    }

  /** A match's type is its written motive, whatever the match is checked against; `TypeChecker.check` compares. */
  def checkMatch(t: CA.Term.Match, env: Env): CheckedTerm = {
    val scrutChecked = checkTerm(t.scrut, env)
    val scrut = scrutChecked.value
    val scrutTpe = scrut.tpe

    val inductiveFamily = scrutTpe match {
      case InductiveFamilyValue(instance) => instance
      case _                              => fail(NonInductiveMatch(scrut.tpe))
    }
    val inductiveName = inductiveFamily.head.name
    val inductiveMeta = inductiveFamily.meta
    // Outside a sealed family's module no match opens its values, so no case, `.short` form included, names its
    // constructors (spec §7.1).
    Sealing.requireAccessible(inductiveMeta.seal, None, t.span)
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
      computeReachableCtors(scrut, scrutTpe, inductiveFamily, cases, env)

    val checkedMotive = checkTypeTerm(t.motive, env)
    val motiveTy = checkedMotive.value

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
    val checkedMatch = CA.Term.Match(scrutChecked.residual, checkedMotive.residual, checkedCases, t.span)
    CheckedTerm(Interpreter.evalTerm(checkedMatch, env), checkedMatch)
  }

}
