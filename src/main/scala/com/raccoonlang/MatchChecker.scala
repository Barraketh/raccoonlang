package com.raccoonlang

import com.raccoonlang.TypeChecker._
import com.raccoonlang.Value._
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}
import com.raccoonlang.ValueQuote.{quoteContext, quoteType}
import com.raccoonlang.Ledger.LinearInfo

object MatchChecker {

  /** A reachable constructor: its fields and result type at the scrutinee's parameters, and its branch's refinement. */
  private final case class ReachableCtor(
      head: ConstructorHead,
      fieldArgs: Vector[Value],
      resultTy: Value,
      branchEqStore: EqStore
  )

  private[raccoonlang] final case class FreshCtor(fieldArgs: Vector[Value], captures: Vector[Value], resultTy: Value)

  /**
   * A constructor's telescope at `family`, the scrutinee's type: a fresh value for each stored field and type-pattern
   * capture, and the constructor's result type over them. The constructor's witnesses of the family's parameters, its
   * erased binders and the captures named like parameters, are linked to the instance's own parameter arguments, so the
   * fields' types are at the scrutinee's parameters, as are the result's parameter arguments. Parameters are uniform,
   * so this needs no equation of the scrutinee's: it unifies each witness, a fresh variable, with its argument,
   * refining only the telescope's fresh variables, which solves the levels and kinds the witness's type captures. A
   * witness whose type is narrower than its parameter's, such as `$A in Sort($u)` for a parameter `A: Univ($k, $u)`,
   * may not unify with an argument that has the parameter's type; it stays fresh, and the branch's refinement relates
   * it as an index. So a stuck index equation leaves every other field at the scrutinee's parameters, where before it
   * left them over fresh parameters that nothing bound.
   */
  private[raccoonlang] def freshCtor(head: ConstructorHead, family: InductiveFamilyInstance): FreshCtor = {
    val opened = StructEta.template(head)
    val params = opened.solve(family.args.take(family.meta.paramCount))
    def atParams(value: Value): Value = ValueOps.materialize(value, params)
    FreshCtor(opened.fieldVars.map(atParams), opened.captures.map(atParams), atParams(opened.result))
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

  /**
   * The caller has identified the scrutinee's saturated inductive family. A scrutinee that is a variable, the root, is
   * unified with the constructor value, which links it once their types unify: that type unification refines the
   * variables of the scrutinee's type, its indices included, exactly as the result refinement does, so a variable index
   * is solved and the root linked in one step. Termination checking reads the link: a field of the constructor value is
   * then a structural subterm of the root, at a variable index as at a known one. Any other scrutinee is related by the
   * result refinement alone, of the constructor's result indices with the scrutinee type's. Stuck equations retain a
   * reachable branch.
   *
   * A proof variable converts with every constructor value of its proposition, so unification succeeds without linking
   * it. A branch whose refinement succeeds links it explicitly to the constructor value it matched, whose type that
   * refinement has unified with the scrutinee's. A stuck branch links nothing: its constructor's type was never unified
   * with the scrutinee's, so the link would change the proof's type. Termination checking of recursion on proofs reads
   * the link. Elsewhere the two convert, as proofs of one proposition, but the link is the proof's value in the branch,
   * as a refined data variable's is: a nested match on the same proof sees a known constructor.
   */
  private def computeReachableCtors(scrut: Value, family: InductiveFamilyInstance, env: Env): Vector[ReachableCtor] = {
    import ValueEquivalence.UnificationFailure._

    val scrutTpe = scrut.tpe
    def tryUnify(left: Value, right: Value, refinable: DepSet) =
      ValueEquivalence.tryUnify(left, right, EqStore.empty.allow(refinable))

    val rootRefinable = scrut match {
      case Var(_, id, _) => DepSet.single(id)
      case _             => DepSet.empty
    }
    val proofRoot = scrut match {
      case Var(_, id, _) if getUniverse(scrutTpe) == PropTpe => Some(id)
      case _                                                 => None
    }
    // Unification never links a proof root: it compares proofs by their propositions, and neither the scrutinee type
    // nor a fresh constructor value mentions the root. The result-only path does not make it refinable.
    def linkProofRoot(store: EqStore, ctorValue: Value): EqStore =
      proofRoot match {
        case Some(id) => store.allow(DepSet.single(id)).addLink(id, ValueOps.materialize(ctorValue, store))
        case None     => store
      }
    family.meta.constructorNames.flatMap { ctorName =>
      env(ctorName) match {
        case h: ConstructorHead =>
          val FreshCtor(fieldArgs, _, resultTy) = freshCtor(h, family)
          val ctorValue = ConstructorValue(h, fieldArgs, resultTy)
          // Both refinements may refine the scrutinee type's variables and the constructor value's own unknowns, its
          // fields and the captures its parameters do not determine; it shares only the scrutinee's parameters with the
          // scrutinee type.
          val refinable = scrutTpe.synDeps ++ ctorValue.synDeps

          val valueRefinement = tryUnify(scrut, ctorValue, rootRefinable ++ refinable)
          val refinement = valueRefinement match {
            case Left(_: Stuck) =>
              refineConstructorResult(resultTy, scrutTpe, EqStore.empty.allow(refinable))
            case other => other
          }
          val branchStore = refinement match {
            case Right(store)           => Some(linkProofRoot(store, ctorValue))
            case Left(_: Contradiction) => None
            case Left(_: Stuck)         => Some(EqStore.empty)
          }

          branchStore.map(store => ReachableCtor(h, fieldArgs, resultTy, store))

        case _ => throw UnknownConstructor(ctorName, family.head.name)
      }
    }
  }

  private def allowLargeElimination(
      family: InductiveFamilyInstance,
      scrutTpe: Value,
      reachable: Vector[ReachableCtor]
  ): Boolean = {
    if (reachable.isEmpty) return true
    if (reachable.length > 1) return false

    val only = reachable.head
    val FreshCtor(fields1, captures1, res1) = freshCtor(only.head, family)
    val FreshCtor(fields2, captures2, res2) = freshCtor(only.head, family)

    val refinable0 = DepSet.unionAll(Vector(scrutTpe.synDeps, res1.synDeps, res2.synDeps))

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
      family: InductiveFamilyInstance,
      scrutTpe: Value,
      motiveTy: Value,
      reachable: => Vector[ReachableCtor],
      span: Span
  ): Unit =
    if (getUniverse(scrutTpe) == PropTpe && getUniverse(motiveTy) != PropTpe) {
      if (!allowLargeElimination(family, scrutTpe, reachable))
        throw PropEliminationRestricted(family.head.name, motiveTy, Some(span))
    }

  /**
   * The Prop elimination check of a projection of field `index` of `scrut`, a value of the record `info` of `family`:
   * the check of the one-branch match on `scrut` that returns the field, whose motive is the field's type, and so of
   * the projections of the earlier fields that type holds, each checked as it would be written out
   * (`StructEta.readFields`). So projecting a data field out of a proof is refused unless the family allows its large
   * elimination, and so is projecting a proof field whose type depends on such a data field, such as `h` of
   * `Exists.intro (w: A)(h: P(w))`, which would hold `w` 's projection in a type, where an elimination into data could
   * read it back. Whether the family allows it does not depend on the motive, so the first data field's type decides.
   */
  private[raccoonlang] def checkProjectionElimination(
      scrut: Value,
      family: InductiveFamilyInstance,
      info: RecordInfo,
      index: Int,
      env: Env,
      span: Span
  ): Unit =
    if (getUniverse(scrut.tpe) == PropTpe)
      StructEta.readFields(info, family, index).find(getUniverse(_) != PropTpe).foreach { dataType =>
        checkPropElimination(family, scrut.tpe, dataType, computeReachableCtors(scrut, family, env), span)
      }

  private final case class PlannedBranch(
      br: CA.Case,
      args: Vector[Value],
      branchEnv: Env,
      store: EqStore,
      equation: Option[Value]
  )

  private final case class CheckedBranch(
      residual: EA.Case,
      checkedBody: CheckedTerm,
      store: EqStore
  ) {

    /**
     * The branch's uses without its fields: a field of linear type, read after the branch's refinement, is tracked
     * (L4), so its extent, the branch body, uses it at most once, or only reads it when the match is a read extent.
     * Only tracked locals have uses, so the other fields are no-ops here.
     */
    def usesWithoutFields(read: Boolean): Ledger.Summary =
      residual.argRefs.flatten.foldLeft(checkedBody.lin.uses)((uses, ref) => Ledger.bind(ref, uses, read))
  }

  /**
   * A linear field is a region of the scrutinee, of provenance `scrutinee`: stored field `i` is `scrutinee.field(i)`.
   */
  private def checkBranch(
      planned: PlannedBranch,
      expected: Option[CheckedTypeTerm],
      scrutinee: Ledger.Provenance
  ): CheckedBranch = {
    val br = planned.br
    val args = planned.args
    if (args.length != br.argRefs.length)
      throw ArityMismatch(args.length, br.argRefs.length, Some(br.span))
    val linearFields = args.map(arg => Linearity.isLinear(arg.tpe))
    val fieldsEnv = br.argRefs.zip(args).zip(linearFields).zipWithIndex.foldLeft(planned.branchEnv) {
      case (curEnv, (((argRef, argVal), linear), index)) =>
        argRef match {
          case Some(ref) => curEnv.putLocal(ref, argVal, linear = linear, alias = Some(scrutinee.field(index)))
          case None      => curEnv
        }
    }
    // The equation, a proof, after the fields; its match's checker made one exactly for the cases that bind it.
    val branchEnv = br.equation.zip(planned.equation).fold(fieldsEnv) { case (ref, value) =>
      fieldsEnv.putLocal(ref, value)
    }
    val branchRes = expected match {
      case Some(motive) =>
        val branchMotive = motive.copy(value = ValueOps.materialize(motive.value, planned.store))
        checkTermAgainst(br.body, branchEnv, branchMotive)
      case None => checkTerm(br.body, branchEnv)
    }
    CheckedBranch(
      EA.Case(br.ctorName, br.argRefs, branchRes.residual, br.span, br.equation),
      branchRes,
      planned.store
    )
  }

  /** Check branches against one constructor observation; dependency blockers schedule reduction, not refinement. */
  def checkMatch(t: CA.Term.MatchTerm, env: Env, contextualExpected: Option[CheckedTypeTerm] = None): CheckedTerm = {
    val span = t.span
    val scrutChecked = checkTerm(t.scrut, env)
    // The known-constructor view, refinement and the match's own value read the scrutinee's form, so a proof call is
    // forced, and the match sees its forced value and that value's type, as before suspension (docs/kernel.md, "Proof
    // calls").
    val scrut = Interpreter.force(scrutChecked.value)
    val scrutTpe = scrut.tpe

    val inductiveFamily = inductiveFamilyOf(scrutTpe).getOrElse(throw NonInductiveMatch(scrut.tpe))
    val inductiveName = inductiveFamily.head.name
    val inductiveMeta = inductiveFamily.meta
    val inductiveCtorNames = inductiveMeta.constructorNames
    def storedArity(ctorName: String): Int =
      env(ctorName) match {
        case head: ConstructorHead => head.totalArity - head.numErased
        case _                     => throw WTF(s"Inductive metadata points to non-constructor $ctorName", Some(span))
      }
    val (written, wildcard, equationSpan) = t match {
      case single: CA.Term.MatchOne =>
        if (inductiveCtorNames.length != 1)
          throw InvalidSingleConstructorMatch(
            scrutTpe,
            s"the family declares ${inductiveCtorNames.length} constructors",
            Some(span)
          )
        val ctorName = inductiveCtorNames.head
        val arity = storedArity(ctorName)
        if (single.fieldRefs.length != arity)
          throw InvalidDestructuring(
            s"expected $arity stored fields, got ${single.fieldRefs.length}",
            Some(span)
          )
        (Vector(CA.Case(ctorName, true, single.fieldRefs.map(Some(_)), single.body, span)), None, None)
      case named: CA.Term.Match =>
        val resolved = named.cases.map { c =>
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
        (resolved, named.wildcard, named.equation)
    }

    // A named equation is `Eq(T, e, C(fields))`, so `T` must be copyable data: `Eq` ranges over no proofs and has no
    // linear carrier (L8). Checked once, at the match, with the `Eq` it uses.
    val equality = equationSpan.map { at =>
      getUniverse(scrutTpe) match {
        case VUniv(kind, _) if kind.isCopy =>
        case PropTpe =>
          throw MatchEquationUnavailable("its scrutinee is a proof, and `Eq` does not range over proofs", Some(at))
        case _ =>
          throw MatchEquationUnavailable("its scrutinee is linear, and `Eq` has no linear carrier (L8)", Some(at))
      }
      MatchEquation.validate(env).fold(reason => throw MatchEquationUnavailable(reason, Some(at)), identity)
    }

    /**
     * What the case `br` binds its equation to, when the match names one: a hypothesis of `Eq(T, e, C(fields))`, at the
     * scrutinee's value `branchScrut` and its type in the case, and `constructed`, the constructor applied to the
     * case's fields at its own result type. In an indexed family the two need the case's refinement to share a type;
     * when it left them apart the equation is `MatchEquationIndexed`.
     */
    def hypothesis(br: CA.Case, branchScrut: Value, constructed: Value): Option[Value] =
      br.equation.zip(equality).map { case (ref, eq) =>
        val proposition = MatchEquation.proposition(eq, branchScrut, constructed).getOrElse {
          throw MatchEquationIndexed(br.ctorName, equationSpan)
        }
        FreshVar.freshVar(ref.name, proposition)
      }

    written.groupBy(_.ctorName).find(_._2.length > 1).foreach { case (ctor, duplicateCases) =>
      throw DuplicateCase(ctor, Some(duplicateCases(1).span))
    }

    /**
     * The match's cases: the written ones and, for a wildcard, a case for each constructor no written case names that
     * `standsFor` holds of, which are exactly those a missing case would be reported for. Each is the case written out
     * at the wildcard, with `_` for every field and a fresh copy of its body, so its refinement, ledger, termination
     * check and value identities are its own. A wildcard stands for at least one constructor.
     */
    def withWildcard(standsFor: String => Boolean): Vector[CA.Case] =
      wildcard.fold(written) { w =>
        val expanded =
          inductiveCtorNames.filter(name => standsFor(name) && !written.exists(_.ctorName == name)).map { ctorName =>
            val fields = Vector.fill(storedArity(ctorName))(None)
            CA.Case(ctorName, true, fields, CA.freshCopy(w.body), w.span, w.equation)
          }
        if (expanded.isEmpty) throw RedundantCase(Some(w.span))
        written ++ expanded
      }

    lazy val reachableByType: Vector[ReachableCtor] =
      computeReachableCtors(scrut, inductiveFamily, env)

    val checkedSourceMotive = t.motive.map(syntax => checkTypeTerm(syntax, env))
    val expectedMotive = checkedSourceMotive.orElse(contextualExpected)
    expectedMotive.foreach(motive => assertType(motive.value))
    expectedMotive.foreach(motive =>
      checkPropElimination(inductiveFamily, scrutTpe, motive.value, reachableByType, span)
    )

    // The branches follow the scrutinee on every path, so their bindings see what it consumed.
    val branchBaseEnv = after(env, scrutChecked.lin)
    val constructor = ConstructorValue.unapply(scrut)
    val plannedBranches: Vector[PlannedBranch] = constructor match {
      case Some((head, fields)) =>
        val cases = withWildcard(_ == head.name)
        cases.find(_.ctorName != head.name).foreach { c =>
          throw UnreachableCase(c.ctorName, Some(c.span))
        }
        val br = cases.find(_.ctorName == head.name).getOrElse(throw MissingCase(head.name))
        // The match's value is then its case's, so the case binds its equation to the proof evaluation gives it.
        val proof = br.equation.zip(equality).map(_ => MatchEquation.proof(env, scrut))
        Vector(PlannedBranch(br, fields, branchBaseEnv, EqStore.empty, proof))

      case None =>
        val reachableMap = reachableByType.map(info => info.head.name -> info).toMap
        val cases = withWildcard(reachableMap.contains)
        inductiveCtorNames.flatMap { ctorName =>
          reachableMap.get(ctorName) match {
            case None =>
              cases.find(_.ctorName == ctorName).foreach { c =>
                throw UnreachableCase(ctorName, Some(c.span))
              }
              None
            case Some(info) =>
              val br = cases.find(_.ctorName == ctorName).getOrElse(throw MissingCase(ctorName))
              val store = info.branchEqStore
              val fields = info.fieldArgs.map(arg => ValueOps.materialize(arg, store))
              def constructed = ConstructorValue(info.head, fields, ValueOps.materialize(info.resultTy, store))
              Some(
                PlannedBranch(
                  br,
                  fields,
                  ValueOps.materializeEnv(branchBaseEnv, store),
                  store,
                  hypothesis(br, ValueOps.materialize(scrut, store), constructed)
                )
              )
          }
        }
    }

    val checkedBranches =
      plannedBranches.map(branch => checkBranch(branch, expectedMotive, scrutChecked.lin.provenance))
    val chosenMotive = expectedMotive.getOrElse {
      val first = checkedBranches.headOption.getOrElse {
        throw MissingReturningClause("no reachable branches have a result type to infer", Some(span))
      }
      // Quotation reads the type's form, so a branch value that is a proof call gives its forced value's type.
      val candidate = ValueOps.materialize(Interpreter.force(first.checkedBody.value).tpe, first.store)
      val changedLocalIds = env.locals.zipWithIndex.collect {
        case (binding, index) if binding.valueOption.exists { original =>
              !ValueEquivalence.defEq(original.tpe, ValueOps.materialize(original, first.store).tpe)
            } =>
          index
      }.toSet
      val context = quoteContext(env)
      val safeContext = context.copy(quote = context.quote.filter { case (_, entry) =>
        entry.term match {
          case EA.Term.LocalRef(ref, _) => !changedLocalIds.contains(ref.id)
          case _                        => true
        }
      })
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
      checkPropElimination(inductiveFamily, scrutTpe, value, reachableByType, span)
      checkedBranches.foreach { branch =>
        val branchValue = ValueOps.materialize(branch.checkedBody.value, branch.store)
        val branchExpected = ValueOps.materialize(value, branch.store)
        checkType(branchValue, branchExpected)
      }
      CheckedTypeTerm(value, residual, LinearInfo.empty)
    }
    val checkedMatch = EA.Term.Match(
      scrutChecked.residual,
      Some(chosenMotive.residual),
      checkedBranches.map(_.residual),
      span,
      t.nodeId
    )
    val value = constructor match {
      case Some(_) =>
        checkedBranches.headOption.map(_.checkedBody.value).getOrElse {
          throw WTF("Known constructor match had no checked branch", Some(span))
        }
      // Structure eta: a value at an eligible type takes the one branch with its field projections. Any other is stuck.
      case None => Interpreter.evalMatchOn(checkedMatch, scrut, env, chosenMotive.value)
    }
    CheckedTerm(value, checkedMatch, linearInfo(value, scrutChecked.lin, checkedBranches))
  }

  /**
   * A match's uses are its scrutinee's, then one branch's on each path. The motive is a read extent, which may read the
   * scrutinee (L4), and a match that is itself a read extent only reads its fields. Inside a read extent a match only
   * inspects its scrutinee, as in the model, so it is no call of the read rules: its fields are regions of the
   * scrutinee, and a call that combines one with an overlapping region is refused there. A linear result is one of its
   * branches' results.
   */
  private def linearInfo(
      value: Value,
      scrut: LinearInfo,
      branches: Vector[CheckedBranch]
  ): LinearInfo = {
    val plain = (scrut eq LinearInfo.empty) && branches.forall(_.checkedBody.lin eq LinearInfo.empty)
    if (plain) LinearInfo.empty.at(value)
    else {
      val read = Linearity.role(value) == Linearity.Role.TypeOrProof
      val branchUses = branches.map(_.usesWithoutFields(read)).foldLeft(Ledger.Summary.empty)(_ or _)
      val pending = (scrut +: branches.map(_.checkedBody.lin)).iterator.flatMap(_.pending).nextOption()
      val provenance = branches match {
        case Vector(only) => only.checkedBody.lin.provenance
        case _            => Ledger.Provenance.union(branches.iterator.map(_.checkedBody.lin.provenance))
      }
      LinearInfo(scrut.uses.andThen(branchUses), provenance, pending).at(value)
    }
  }
}
