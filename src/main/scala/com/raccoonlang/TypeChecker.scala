package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.{BinderOps, Projection}
import com.raccoonlang.{CoreAst => CA}

object TypeChecker {
  private final case class CheckedPi(
      vpi: VPi,
      bodyEnv: Env,
      outTy: Value,
      residual: CA.Term.Pi
  )

  /** A checker-produced term; callers cannot construct or copy one themselves. */
  final class CheckedTerm private (val value: Value, val residual: CA.Term)

  private[raccoonlang] object CheckedTerm {
    def apply(value: Value, residual: CA.Term): CheckedTerm = new CheckedTerm(value, residual)
  }

  /** Check an elaborated program, retaining the value computed by the checking pass for the public runner. */
  def check(program: Execution.ElaboratedProgram): Execution.CheckedProgram =
    Execution.check(program)

  private[raccoonlang] def checkRaw(program: CA.Program, prelude: Prelude.Config): Option[Value] = {
    val env =
      program.decls.foldLeft(prelude.checkedEnv) { case (curEnv, decl) => Interpreter.evalDecl(decl, curEnv) }
    program.body.map(body => checkTerm(body, env).value)
  }

  /**
   * An expected type, optionally paired with the *syntax* that denotes it.
   *
   * `syntax`, when present, is a term valid in the env the expectation is pushed into — the same local references — so
   * it can be placed verbatim into a residual. That is what a `match` without a `returning` clause needs: its residual
   * motive has to be syntax, and the only syntax available is whatever the enclosing declaration wrote down. A declared
   * return type qualifies (a lambda's `pi.out`, an annotated let's type, a bare-body def's declared type); a type that
   * only exists as a checked value does not, and a match under such an expectation is rejected with
   * `MissingReturningClause`.
   */
  private[raccoonlang] final case class Expected(value: Value, syntax: Option[CA.Term])

  private[raccoonlang] object Expected {
    def valueOnly(value: Value): Expected = Expected(value, None)
  }
  private final case class CheckedApply(value: Value, residual: CA.Term.App)
  private[raccoonlang] final case class CheckedRecursiveDef(name: String, vpi: VPi, residual: CA.Term.Lam)

  /**
   * An argument whose elaboration is deferred until its binder's expected type is known.
   *
   * An argument is never a place where expected-type *syntax* is available: the binder type it would come from is
   * syntax in the callee's telescope env, not in the caller's. So the expectation pushed here could only ever be a bare
   * value, and a value-only expectation changes nothing that the final verification pass does not already do — the
   * check performed by `checkTermFits` happens there too (the telescope walk checks each arg against its binder type),
   * and both remaining consumers of a pushed expectation need syntax: subsumption's eta-adaptation needs a Pi *term*
   * for the synthetic lambda's type, and a motive-less `match` needs a motive term. Arguments are therefore always
   * synthesized, and `PendingArg` is either the argument's own syntax or an already-checked value (the eta-adaptation
   * path builds those).
   */
  private sealed trait PendingArg {
    def synth(env: Env): CheckedTerm
  }

  private object PendingArg {
    final case class Term(term: CA.Term) extends PendingArg {
      def synth(env: Env): CheckedTerm = checkTerm(term, env)
    }

    final case class Checked(checked: CheckedTerm) extends PendingArg {
      def synth(env: Env): CheckedTerm = checked
    }

    def term(t: CA.Term): PendingArg = Term(t)

    def checked(c: CheckedTerm): PendingArg = Checked(c)
  }

  // Universes are NOT cumulative (Lean-style): a type fits exactly the sorts defEq to its own.
  // Non-cumulativity is what makes `.tpe` canonical enough for implicit projection — the level a
  // spec reads is the only level the argument can carry.
  def checkFits(actual: Value, expected: Value): Unit =
    if (!ValueEquivalence.defEq(actual, expected))
      throw TypeMismatch(expected, actual)

  def checkType(value: Value, tyVal: Value): Unit =
    checkFits(value.tpe, tyVal)

  def getUniverse(value: Value): VSort = {
    value.tpe match {
      case u: VSort => u
      case _        => throw NotAType(value.tpe)
    }
  }

  /**
   * `Value.isPropositionType` plus the validation that `value` is a type at all.
   *
   * The classification itself is deliberately not duplicated — it is the one shared predicate, so the checker can never
   * disagree with proof collapse. What this adds is the `NotAType` check in `getUniverse`, and the one caller,
   * `MatchChecker.checkPropElimination`, needs it: its `motiveTy` can be a user-written motive or an inherited
   * expectation, neither of which has been asserted to be a type by the time elimination is classified. (A type is
   * Prop-valued when it is itself a proposition. The sort `Prop` is not: `Prop : Sort 1`, so `Nat -> Prop` lives in
   * Type, and predicates are data, not proofs — conflating the two made predicates proof-irrelevant and derived False.)
   */
  def isPropValuedType(value: Value): Boolean = {
    getUniverse(value)
    Value.isPropositionType(value)
  }

  private def assertNonRawRecursive(v: Value): Unit = {
    v match {
      case VLam(_, id, LamBody.Native(_, _, true)) => throw InvalidRecursiveOccurrence(s"$id")
      case _                                       =>
    }
  }

  private def checkTermFits(checked: CheckedTerm, expectedTy: Value): CheckedTerm = {
    checkType(checked.value, expectedTy)
    checked
  }

  /**
   * A synthesized term under an optional expectation: unconstrained it is returned as synthesized, and under an
   * expectation it must fit. This is plain subsumption — the syntax-directed forms that can also eta-adapt (refs,
   * lambdas) go through `subsume` instead.
   */
  private def fitsExpected(synthed: CheckedTerm, expected: Option[Expected]): CheckedTerm =
    expected.fold(synthed)(exp => checkTermFits(synthed, exp.value))

  private def applyHeadName(fnResidual: CA.Term): String =
    fnResidual match {
      case CA.Term.GlobalRef(name, _) => name
      case CA.Term.LocalRef(ref, _)   => ref.name
      case _                          => "function"
    }

  /**
   * Application checking without unification: callers supply exactly the explicit args; every implicit binder carries a
   * projection spec (compiled at Pi formation) that re-derives its value from those args. Elaboration order and
   * verification are separate phases because implicits lead their forcing args in the telescope: an arg is checked
   * against its binder type only once every binder that type mentions is known, and all fits are (re)verified in
   * telescope order at the end.
   */
  private def checkApplyChecked(
      fnValue: Value,
      fnResidual: CA.Term,
      providedArgs: Vector[PendingArg],
      env: Env,
      span: Span,
      expectedResult: Option[Value]
  ): CheckedApply =
    fnValue.tpe match {
      case pi: VPi =>
        val binders = pi.binders
        // Grouping is part of a function type's identity: a call supplies exactly this Pi's own
        // explicit binders. `(a:A) -> (b:B) -> C` takes one argument and returns a function;
        // `(a:A)(b:B) -> C` takes two. Supplying the wrong number is an arity error here, not a
        // descent into the codomain — `f(x)(y)` is how a nested group is reached.
        if (providedArgs.length != pi.numExplicit)
          throw ArityMismatch(pi.numExplicit, providedArgs.length, Some(span))

        val known = new Array[Value](binders.length)
        val checkedResiduals = Vector.newBuilder[CA.Term]
        var providedValues = Vector.empty[Value]

        var explicitIdx = 0
        binders.zipWithIndex.foreach { case (binder, idx) =>
          if (!binder.isImplicit) {
            // Arguments are synthesized and verified in the final pass; see PendingArg.
            val checked = providedArgs(explicitIdx).synth(env)
            assertNonRawRecursive(checked.value)
            known(idx) = checked.value
            checkedResiduals += checked.residual
            providedValues :+= checked.value
            // Specs always root at a non-implicit binder, so every implicit lands during this walk.
            pi.implicitRoots.getOrElse(explicitIdx, Vector.empty).foreach { implicitIdx =>
              Projection.project(binders(implicitIdx).projection.get, providedValues) match {
                case Right(value) => known(implicitIdx) = value
                case Left(reason) =>
                  throw ImplicitReconstructionFailed(
                    binders(implicitIdx).name,
                    applyHeadName(fnResidual),
                    reason,
                    Some(span)
                  )
              }
            }
            explicitIdx += 1
          }
        }

        // Verification pass: with the full group known, every binder type is evaluable in order
        // and each arg (provided or projected) must fit it. Projection was only a choice — this
        // pass is what makes the application well-typed. Arguments are bound as supplied.
        val calleeEnv = BinderOps.checkAndInstantiate(binders, pi.env, binders.indices.map(known).toVector)
        expectedResult.foreach(expected => checkFits(pi.codomain(calleeEnv), expected))

        val finalArgs = binders.map(binder => calleeEnv(binder.localRef))
        val residual = CA.Term.App(fnResidual, checkedResiduals.result(), span)
        CheckedApply(Interpreter.evalApply(fnValue, finalArgs), residual)

      case _ => throw CannotApplyNonFunction(fnValue)
    }

  private def checkPi(pi: CA.Term.Pi, env: Env, familyParams: Int = 0): CheckedPi = {
    // Implicit legality (forced-by-later-binders) and projection specs come from BinderOps.checkBinders.
    val checkedBinders = BinderOps.checkBinders(pi.binders, env, familyParams)
    val binderEnv = checkedBinders.env
    val checkedOut = checkTerm(pi.out, binderEnv)
    val outV = checkedOut.value
    val classifier = Interpreter.piClassifierFromChecked(checkedBinders.binders, binderEnv, outV)
    val checkedPi =
      CA.Term.Pi(
        checkedBinders.binders,
        checkedOut.residual,
        pi.span,
        knownPropValued = Interpreter.stablePiPropClassification(outV)
      )
    val vpi = evalPi(checkedPi, env).copy(classifier0 = () => classifier)
    // Force the classifier at declaration. Reuse the already checked fresh telescope instead of eta-expanding every
    // binder a second time; this is the universe validation (NotAType on a bad domain or codomain).
    vpi.tpe
    CheckedPi(vpi, binderEnv, outV, checkedPi)
  }

  /**
   * Constructor telescopes route through here so unforced family params (the leading `familyParams` binders) get
   * demoted instead of rejected; see Projection.compile.
   */
  private[raccoonlang] def getConstructorType(term: CA.Term, env: Env, familyParams: Int): Value =
    term match {
      case pi: CA.Term.Pi =>
        val checked = checkPi(pi, env, familyParams)
        assertType(checked.vpi)
        checked.vpi
      case other => getType(other, env)
    }

  // Returning the residual term lets callers preserve checked let/lambda structure instead of re-checking.
  private def checkBody(body: CA.Term.Body, env: Env, expected: Option[Expected]): CheckedTerm = {
    val checkedLets = Vector.newBuilder[CA.Let]
    var curEnv = env

    body.lets.foreach { l =>
      val checkedTy = l.ty.map(tyTerm => checkTerm(tyTerm, curEnv))
      val checkedValue = checkedTy match {
        // An annotated let carries its own syntax: `l.ty` is a term in `curEnv`, so it can serve as
        // the residual motive of a `match` in the let's value.
        case Some(ty) => check(l.value, Some(Expected(ty.value, l.ty)), curEnv)
        case None     => checkTerm(l.value, curEnv)
      }
      checkedLets += CA.Let(l.localRef, checkedTy.map(_.residual), checkedValue.residual, l.span)
      curEnv = curEnv.putLocal(l.localRef, checkedValue.value)
    }

    // The lets only add locals, so both the enclosing expectation's value and its syntax stay valid.
    val checkedRes = check(body.res, expected, curEnv)
    CheckedTerm(checkedRes.value, CA.Term.Body(checkedLets.result(), checkedRes.residual, body.span))
  }

  /**
   * Named field access is an ordinary call of the family's selector global: `base.f` is `Family.f(base)`, with the
   * selector's implicit family parameters forced by `self`. There is no projection node and no selector metadata — the
   * residual is a plain application, and the selector's own body is the match that does the work.
   */
  private def checkSelect(
      base: CheckedTerm,
      field: String,
      span: Span,
      env: Env,
      expected: Option[Expected]
  ): CheckedTerm = {
    val vType = base.value.tpe
    val family = vType match {
      case InductiveFamilyValue(instance) => instance
      case _                              => throw NotAType(vType)
    }
    val selectorName = s"${family.head.name}.$field"
    if (!env.globals.contains(selectorName)) throw NotFound(selectorName)
    val selector = env(selectorName)
    val applied =
      checkApplyChecked(
        selector,
        CA.Term.GlobalRef(selectorName, span),
        Vector(PendingArg.checked(base)),
        env,
        span,
        expected.map(_.value)
      )
    CheckedTerm(applied.value, applied.residual)
  }

  private def checkLam(l: CA.Term.Lam, env: Env): CheckedTerm = {
    val checkedVpi = checkPi(l.ty, env)
    val vpi = checkedVpi.vpi
    val bodyEnv = checkedVpi.bodyEnv

    // Recursive self references stay local for the whole pipeline, even if the source used a qualified name.
    // While checking, the local contains a raw recursive value that enforces the decrease and can only appear as an
    // application head, so the body cannot store it as an ordinary value. The checked lambda keeps the same self ref;
    // when the lambda runs, Interpreter.runLam binds that ref to the final VLam. The declaration is published to
    // globals separately after the body has checked.
    val recurEnv =
      l.recursion match {
        case Some(CA.Recursion(ref, decreaseSpec)) =>
          val name = l.name.getOrElse(throw WTF("Recursive lambda must have a name", Some(l.span)))
          val recursiveSelf = TerminationChecker.rawRecursiveSelf(name, vpi, decreaseSpec, bodyEnv)
          bodyEnv.putLocal(ref, recursiveSelf)
        case None => bodyEnv
      }

    // The Pi's `out` is syntax in the body's own scope — `checkPi` binds exactly the binder refs
    // `out` mentions, and the residual Pi reuses them — so the declared return type can be the
    // residual motive of a `match` body with no `returning` clause.
    val checkedBody =
      check(l.body, Some(Expected(checkedVpi.outTy, Some(checkedVpi.residual.out))), recurEnv)
    assertNonRawRecursive(checkedBody.value)

    val checkedLam =
      CA.Term.Lam(
        checkedVpi.residual,
        checkedBody.residual,
        l.span,
        l.name,
        l.recursion,
        recursivePeers = l.recursion.map(recursion => recursion.selfRef -> l.name.get).toVector
      )
    CheckedTerm(Interpreter.evalLam(checkedLam, vpi, env), checkedLam)
  }

  private[raccoonlang] def checkRecursiveDefBlock(
      block: CA.Decl.RecursiveDefBlock,
      env: Env
  ): Vector[CheckedRecursiveDef] = {
    val definitions = block.definitions
    if (definitions.isEmpty)
      throw InvalidRecursiveGroup("the group must not be empty", Some(block.span))
    if (definitions.map(_.name).distinct.length != definitions.length)
      throw InvalidRecursiveGroup("global names must be distinct", Some(block.span))
    if (definitions.map(_.peerRef).distinct.length != definitions.length)
      throw InvalidRecursiveGroup("peer refs must be distinct", Some(block.span))

    val peers = definitions.map(definition => definition.peerRef -> definition.name)
    val peerRefs = definitions.iterator.map(_.peerRef).toSet
    val ambientPeerRefs = peerRefs.intersect(env.locals.keySet)
    if (ambientPeerRefs.nonEmpty)
      throw InvalidRecursiveGroup(
        s"peer refs collide with the incoming environment: ${ambientPeerRefs.mkString(", ")}",
        Some(block.span)
      )
    val headers = definitions.map { definition =>
      val checkedPi = checkPi(definition.ty, env)
      val metric = TerminationChecker.checkLexicographic(checkedPi.vpi, definition.decreases, checkedPi.bodyEnv)
      (definition, checkedPi, metric)
    }
    val referenceMetric = headers.head._3
    headers.tail.foreach { case (_, _, metric) =>
      TerminationChecker.requireCompatible(referenceMetric, metric)
    }

    headers.map { case (definition, checkedPi, callerMetric) =>
      val bodyEnv = headers.foldLeft(checkedPi.bodyEnv) { case (current, (callee, calleePi, calleeMetric)) =>
        current.putLocal(
          callee.peerRef,
          TerminationChecker.rawRecursivePeer(
            callee.name,
            calleePi.vpi,
            calleeMetric,
            callerMetric,
            checkedPi.bodyEnv
          )
        )
      }
      val checkedBody =
        check(definition.body, Some(Expected(checkedPi.outTy, Some(checkedPi.residual.out))), bodyEnv)
      assertNonRawRecursive(checkedBody.value)
      val residual = CA.Term.Lam(
        checkedPi.residual,
        checkedBody.residual,
        definition.span,
        Some(definition.name),
        // A group member has no source `recursion` of its own: the whole group's peer table is
        // what its body's recursive calls resolve through.
        recursion = None,
        recursivePeers = peers
      )
      CheckedRecursiveDef(definition.name, checkedPi.vpi, residual)
    }
  }

  def getType(term: CA.Term, env: Env): Value = {
    val res = checkTerm(term, env).value
    assertType(res)
    res
  }

  def assertType(value: Value): Unit =
    value.tpe match {
      case _: VSort =>
      case _        => throw NotAType(value)
    }

  /**
   * Eta-adaptation of a bare polymorphic function against an expected Pi with fewer binders: `let f : Nat -> Nat := id`
   * becomes `fun (x: Nat): Nat => id(x)`, and the inner application reconstructs the implicits from `x` by projection.
   * Expected Pis may themselves have (forced) implicit binders — those become implicit binders of the synthetic lambda,
   * reconstructed at its call sites; only the explicit ones are applied.
   *
   * The synthetic lambda needs a *type* in residual syntax, and the only such syntax is the expectation's own: the
   * expected type must have been written down as a literal `Pi` term valid in the caller's env. That is exactly the
   * declared-type positions (`let f : Nat -> Nat := id`, a def's declared type). When the expectation carries no
   * syntax, or its syntax is not literally a Pi node (a reference to a let-bound type alias, say), the adaptation is
   * declined and plain subsumption applies.
   */
  private def tryInstantiateImplicits(
      checked: CheckedTerm,
      expected: Expected,
      env: Env,
      span: Span
  ): Option[CheckedTerm] =
    (checked.value.tpe, expected.value) match {
      case (actualPi: VPi, expectedPi: VPi)
          if actualPi.binders.exists(_.isImplicit) &&
            actualPi.binders.length > expectedPi.binders.length &&
            actualPi.numExplicit == expectedPi.numExplicit =>
        // Freshen through the expected Pi's own closure — its binder types are syntax valid in
        // expectedPi.env, not in the caller's env — then expose the fresh binders to the body.
        val piFreshEnv = BinderOps.freshen(expectedPi)
        val bodyEnv = expectedPi.binders.foldLeft(env) { (curEnv, binder) =>
          curEnv.putLocal(binder.localRef, piFreshEnv(binder.localRef))
        }
        expectedPiSyntax(expected, expectedPi).flatMap { residualPi =>
          try {
            val bodyArgs =
              expectedPi.binders.collect {
                case binder if !binder.isImplicit =>
                  val value = piFreshEnv(binder.localRef)
                  PendingArg.checked(CheckedTerm(value, CA.Term.LocalRef(binder.localRef, binder.ty.span)))
              }
            val app =
              checkApplyChecked(
                checked.value,
                checked.residual,
                bodyArgs,
                bodyEnv,
                span,
                Some(expectedPi.codomain(piFreshEnv))
              )
            val lam =
              CA.Term.Lam(
                residualPi,
                app.residual,
                // A fabricated lambda needs a node identity of its own (docs/kernel.md#value-identity);
                // its span carries one.
                Span.synthetic(),
                name = None,
                recursion = None
              )
            Some(CheckedTerm(Interpreter.evalLam(lam, expectedPi, env), lam))
          } catch {
            case _: TypeMismatch | _: ArityMismatch | _: ImplicitReconstructionFailed => None
          }
        }

      case _ => None
    }

  /**
   * The expectation's syntax as a Pi term for the synthetic eta-adaptation lambda's type.
   *
   * The binders are the *expected Pi value's* own, so local refs, implicit flags, and compiled projection specs are
   * preserved exactly; only the surrounding node identity is fresh. A fabricated Pi needs an identity of its own, or
   * two sibling adaptations checked at one caller span would mint values sharing a trusted ValueKey
   * (docs/kernel.md#value-identity).
   */
  private def expectedPiSyntax(expected: Expected, expectedPi: VPi): Option[CA.Term.Pi] =
    expected.syntax.collect { case pi: CA.Term.Pi =>
      CA.Term.Pi(pi.binders, pi.out, Span.synthetic(), knownPropValued = expectedPi.knownPropValued)
    }

  // Adapt a synthesized value to the expected type: eta-expand a polymorphic function against a
  // monomorphic expected Pi if that helps, otherwise plain subsumption.
  private def subsume(checked: CheckedTerm, expected: Expected, env: Env, span: Span): CheckedTerm =
    tryInstantiateImplicits(checked, expected, env, span)
      .getOrElse(checkTermFits(checked, expected.value))

  def checkTerm(term: CA.Term, env: Env): CheckedTerm =
    check(term, None, env)

  /** Check against an expected type with no syntax for it; a motive-less `match` under it is rejected. */
  def checkTerm(term: CA.Term, expectedTy: Value, env: Env): CheckedTerm =
    check(term, Some(Expected.valueOnly(expectedTy)), env)

  private[raccoonlang] def checkTerm(term: CA.Term, expected: Expected, env: Env): CheckedTerm =
    check(term, Some(expected), env)

  private def check(term: CA.Term, expected: Option[Expected], env: Env): CheckedTerm =
    try {
      term match {
        case CA.Term.NatLit(value, span) =>
          val layout = env.nativeLiterals.natLayout.getOrElse(
            throw NatLiteralUnavailable("no validated Nat layout", Some(span))
          )
          val synthed = CheckedTerm(VPacked.nat(value, layout.natTpe), CA.Term.NatLit(value, span))
          fitsExpected(synthed, expected)
        case CA.Term.StrLit(scalars, span) =>
          val layout = env.nativeLiterals.stringLayout.getOrElse(
            throw StringLiteralUnavailable("no validated String layout", Some(span))
          )
          val synthed = CheckedTerm(Packed.evalStrLit(scalars, env), CA.Term.StrLit(scalars, span))
          if (!ValueEquivalence.defEq(synthed.value.tpe, layout.stringTpe))
            throw WTF("String literal evaluator returned the wrong type", Some(span))
          fitsExpected(synthed, expected)
        case CA.Term.Select(base, field, span) =>
          val checkedBase = checkTerm(base, env)
          checkSelect(checkedBase, field, span, env, expected)
        case app: CA.Term.App =>
          val checkedFn = checkTerm(app.fn, env)
          val checkedArgs = app.args.map(PendingArg.term)
          val checkedApp =
            checkApplyChecked(checkedFn.value, checkedFn.residual, checkedArgs, env, app.span, expected.map(_.value))
          CheckedTerm(checkedApp.value, checkedApp.residual)
        case m: CA.Term.Match => MatchChecker.checkMatch(m, env, expected)
        case b: CA.Term.Body  => checkBody(b, env, expected)
        case pi: CA.Term.Pi =>
          val checked = checkPi(pi, env)
          val checkedTerm = CheckedTerm(checked.vpi, checked.residual)
          fitsExpected(checkedTerm, expected)
        // Refs evaluate directly; against an expected type they get subsumption
        // (eta-adaptation of polymorphic functions).
        case ref: CA.Term.Ref =>
          val synthed = CheckedTerm(Interpreter.evalTerm(ref, env), ref)
          expected.fold(synthed)(exp => subsume(synthed, exp, env, ref.span))
        case l: CA.Term.Lam =>
          val synthed = checkLam(l, env)
          expected.fold(synthed)(exp => subsume(synthed, exp, env, l.span))
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw e.withSpan(term.span)
    }

}
