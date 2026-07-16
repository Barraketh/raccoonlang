package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang.ValueQuote.{quoteContext, quotePi}
import com.raccoonlang.telescope.{BinderOps, Projection}
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

object TypeChecker {
  private final case class CheckedPi(
      vpi: VPi,
      bodyEnv: Env,
      outTy: Value,
      residual: EA.Term.Pi
  )
  final case class CheckedTerm(value: Value, residual: EA.Term)
  private final case class CheckedApply(value: Value, residual: EA.Term.App)

  // An argument whose elaboration is deferred until its binder's expected type is known.
  private final case class PendingArg(
      synthArg: Env => CheckedTerm,
      checkArg: (Value, Env) => CheckedTerm
  ) {
    // Push the expected type into checking only when it is closed over the caller's env;
    // open expected types cannot be quoted into residual motives (MatchChecker's inferred motive
    // is the one remaining quoting client fed from this path).
    def check(expectedTy: Value, env: Env): CheckedTerm =
      if (canQuoteFromEnv(expectedTy, env)) checkArg(expectedTy, env)
      else synthArg(env)
  }

  private object PendingArg {
    def term(t: CA.Term): PendingArg =
      PendingArg(checkTerm(t, _), (expected, env) => checkTerm(t, expected, env))

    def checked(c: CheckedTerm): PendingArg = PendingArg(_ => c, (_, _) => c)
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

  // A type is Prop-valued when it is itself a proposition (lives in Prop). The sort Prop is NOT
  // Prop-valued: `Prop : Sort 1`, so e.g. `Nat -> Prop` lives in Type, and predicates are data,
  // not proofs. Conflating the two made predicates proof-irrelevant (derived False).
  // getUniverse validates that `value` is a type (throws NotAType); classification itself is the
  // shared predicate, so the checker can never disagree with collapse (Value.isPropositionType).
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
    CheckedTerm(Value.ascribe(checked.value, expectedTy), checked.residual)
  }

  private def canQuoteFromEnv(value: Value, env: Env): Boolean =
    (value.synDeps -- Value.envDeps(env)).isEmpty

  private def expectedPiResidual(expectedTy: Value, env: Env, span: Span): Option[EA.Term.Pi] =
    try
      expectedTy match {
        case pi: VPi => Some(quotePi(pi, quoteContext(env), span))
        case _       => None
      }
    catch {
      case _: CannotQuoteValue => None
    }

  private def applyHeadName(fnResidual: EA.Term): String =
    fnResidual match {
      case EA.Term.GlobalRef(name, _)                 => name
      case EA.Term.LocalRef(ref, _)                   => ref.name
      case EA.Term.Proj(familyName, fieldIndex, _, _) => s"$familyName.$fieldIndex"
      case _                                          => "function"
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
      fnResidual: EA.Term,
      providedArgs: Vector[PendingArg],
      env: Env,
      span: Span,
      expectedResult: Option[Value] = None
  ): CheckedApply =
    fnValue.tpe match {
      case pi: VPi =>
        val binders = pi.binders
        val numExplicit = binders.count(!_.isImplicit)
        if (providedArgs.length != numExplicit)
          throw ArityMismatch(numExplicit, providedArgs.length, Some(span))

        // Implicit telescope indices grouped by the provided arg their spec projects from. Specs
        // always root at a non-implicit binder, so every implicit lands during the arg walk below.
        val specRoots: Map[Int, Vector[Int]] =
          binders.zipWithIndex
            .collect {
              case (binder, idx) if binder.isImplicit =>
                val spec = binder.projection.getOrElse(
                  throw WTF(s"Implicit binder ${binder.name} has no projection spec", Some(span))
                )
                spec.rootArgIdx -> idx
            }
            .groupMap(_._1)(_._2)

        val known = new Array[Value](binders.length)
        val checkedResiduals = Vector.newBuilder[EA.Term]
        var providedValues = Vector.empty[Value]
        var knownEnv = pi.env
        var unknownRefs = binders.map(_.localRef).toSet

        def land(idx: Int, value: Value): Unit = {
          known(idx) = value
          knownEnv = BinderOps.bindValue(knownEnv, binders(idx), value)
          unknownRefs -= binders(idx).localRef
        }

        var explicitIdx = 0
        binders.zipWithIndex.foreach { case (binder, idx) =>
          if (!binder.isImplicit) {
            // The binder type is evaluable only when every telescope ref it mentions is already
            // known; otherwise the arg is synthesized and verified in the final pass.
            val checked =
              if (CapturedRefs.mentions(binder.ty, unknownRefs))
                providedArgs(explicitIdx).synthArg(env)
              else
                providedArgs(explicitIdx).check(Interpreter.evalTerm(binder.ty, knownEnv), env)
            assertNonRawRecursive(checked.value)
            land(idx, checked.value)
            checkedResiduals += checked.residual
            providedValues :+= checked.value
            specRoots.getOrElse(explicitIdx, Vector.empty).foreach { implicitIdx =>
              Projection.project(binders(implicitIdx).projection.get, providedValues) match {
                case Right(value) => land(implicitIdx, value)
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

        // Verification pass: with the full telescope known, every binder type is evaluable in
        // order; each arg (provided or projected) must fit it and is bound ascribed. Projection
        // was only a choice — this pass is what makes the application well-typed.
        val calleeEnv = BinderOps.checkAndInstantiate(binders, pi.env, binders.indices.map(known).toVector)
        expectedResult.foreach(expected => checkFits(pi.codomain(calleeEnv), expected))

        val finalArgs = binders.map(binder => calleeEnv(binder.localRef))
        val residual = EA.Term.App(fnResidual, checkedResiduals.result(), span)
        val rawValue = Interpreter.evalApply(fnValue, finalArgs)
        val value = expectedResult match {
          case Some(expected) => Value.ascribe(rawValue, expected)
          case None           => rawValue
        }
        CheckedApply(value, residual)

      case _ => throw CannotApplyNonFunction(fnValue)
    }

  private def elabRef(ref: CA.Term.Ref): EA.Term.Ref =
    ref match {
      case CA.Term.GlobalRef(name, span) => EA.Term.GlobalRef(name, span)
      case CA.Term.LocalRef(ref, span)   => EA.Term.LocalRef(ref, span)
    }

  private def checkPi(pi: CA.Term.Pi, env: Env, familyParams: Int = 0): CheckedPi = {
    // Implicit legality (forced-by-later-binders) and projection specs come from BinderOps.checkBinders.
    val checkedBinders = BinderOps.checkBinders(pi.binders, env, familyParams)
    val binderEnv = checkedBinders.env
    val checkedOut = checkTerm(pi.out, binderEnv)
    val outV = checkedOut.value
    val checkedPi =
      EA.Term.Pi(
        checkedBinders.binders,
        checkedOut.residual,
        pi.span,
        pi.span.nodeId
      )
    val vpi = evalPi(checkedPi, env)
    // Force the classifier at declaration: Interpreter.piClassifier IS the universe validation
    // (NotAType on a bad domain or codomain), memoized by the lazy val — one home for the rule.
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
  private def checkBody(body: CA.Term.Body, env: Env, expectedTy: Option[Value]): CheckedTerm = {
    val checkedLets = Vector.newBuilder[EA.Let]
    var curEnv = env

    body.lets.foreach { l =>
      val checkedTy = l.ty.map(tyTerm => checkTerm(tyTerm, curEnv))
      val checkedValue = checkedTy match {
        case Some(ty) => checkTerm(l.value, ty.value, curEnv)
        case None     => checkTerm(l.value, curEnv)
      }
      val bound = checkedTy.fold(checkedValue.value)(ty => Value.ascribe(checkedValue.value, ty.value))

      checkedLets += EA.Let(l.localRef, checkedTy.map(_.residual), checkedValue.residual, l.span)
      curEnv = curEnv.putLocal(l.localRef, bound)
    }

    val checkedRes = check(body.res, expectedTy, curEnv)
    CheckedTerm(checkedRes.value, EA.Term.Body(checkedLets.result(), checkedRes.residual, body.span))
  }

  def inductiveFamilyOf(value: Value): Option[InductiveFamilyInstance] =
    value match {
      case InductiveFamilyValue(instance) => Some(instance)
      case _                              => None
    }

  private def checkSelect(
      base: CheckedTerm,
      field: String,
      span: Span,
      env: Env,
      expectedTy: Option[Value]
  ): CheckedTerm = {
    val vType = base.value.tpe
    val family = inductiveFamilyOf(vType).getOrElse(throw NotAType(vType))
    val indName = family.head.name
    val selectorName = s"$indName.$field"
    val alias = env.projectionAlias(selectorName).getOrElse(throw NotFound(selectorName))
    if (alias.familyName != indName)
      throw WTF(s"Selector $selectorName aliases a projection from ${alias.familyName}", Some(span))
    checkProj(indName, alias.fieldIndex, base, span, expectedTy)
  }

  private def checkProj(
      familyName: String,
      fieldIndex: Int,
      base: CheckedTerm,
      span: Span,
      expectedTy: Option[Value]
  ): CheckedTerm = {
    val family = inductiveFamilyOf(base.value.tpe).getOrElse {
      throw InvalidProjection(familyName, fieldIndex, s"major premise has type ${base.value.tpe}", Some(span))
    }
    if (family.head.name != familyName)
      throw InvalidProjection(
        familyName,
        fieldIndex,
        s"major premise belongs to ${family.head.name}",
        Some(span)
      )
    val info = family.meta.projectionInfo.getOrElse {
      throw InvalidProjection(
        familyName,
        fieldIndex,
        s"family has ${family.meta.constructors.length} constructors instead of one",
        Some(span)
      )
    }
    val projected = InductiveProjection.check(base.value, family, info, fieldIndex, span)
    val synthed = CheckedTerm(projected, EA.Term.Proj(familyName, fieldIndex, base.residual, span))
    expectedTy.fold(synthed)(expected => checkTermFits(synthed, expected))
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

    val checkedBody = checkTerm(l.body, checkedVpi.outTy, recurEnv)
    assertNonRawRecursive(checkedBody.value)

    val checkedLam =
      EA.Term.Lam(
        checkedVpi.residual,
        checkedBody.residual,
        l.span,
        l.name,
        l.recursion.map(_.selfRef),
        l.span.nodeId
      )
    CheckedTerm(Interpreter.evalLam(checkedLam, vpi, env), checkedLam)
  }

  def getType(term: CA.Term, env: Env): Value = {
    val res = checkTerm(term, env).value
    assertType(res)
    res
  }

  def assertType(value: Value): Unit = {
    value match {
      case PropTpe =>
      case _ =>
        value.tpe match {
          case _: VSort | PropTpe =>
          case _                  => throw NotAType(value)
        }
    }
  }

  /**
   * Eta-adaptation of a bare polymorphic function against an expected Pi with fewer binders: `let f : Nat -> Nat := id`
   * becomes `fun (x: Nat): Nat => id(x)`, and the inner application reconstructs the implicits from `x` by projection.
   * Expected Pis may themselves have (forced) implicit binders — those become implicit binders of the synthetic lambda,
   * reconstructed at its call sites; only the explicit ones are applied. The synthetic lambda's residual type is the
   * quoted expected Pi — the one remaining quoting client on the application path.
   */
  private def tryInstantiateImplicits(
      checked: CheckedTerm,
      expectedTy: Value,
      env: Env,
      span: Span
  ): Option[CheckedTerm] =
    (checked.value.tpe, expectedTy) match {
      case (actualPi: VPi, expectedPi: VPi)
          if actualPi.binders.exists(_.isImplicit) &&
            actualPi.binders.length > expectedPi.binders.length &&
            actualPi.binders.count(!_.isImplicit) == expectedPi.binders.count(!_.isImplicit) =>
        expectedPiResidual(expectedTy, env, span).flatMap { residualPi =>
          try {
            // Freshen through the expected Pi's own closure — its binder types are syntax valid in
            // expectedPi.env, not in the caller's env — then expose the fresh binders to the body.
            val piFreshEnv = BinderOps.freshen(expectedPi)
            val bodyEnv = expectedPi.binders.foldLeft(env) { (curEnv, binder) =>
              curEnv.putLocal(binder.localRef, piFreshEnv(binder.localRef))
            }
            val bodyArgs =
              expectedPi.binders.collect {
                case binder if !binder.isImplicit =>
                  val value = piFreshEnv(binder.localRef)
                  PendingArg.checked(CheckedTerm(value, EA.Term.LocalRef(binder.localRef, binder.ty.span)))
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
              EA.Term.Lam(residualPi, app.residual, span, name = None, recursiveSelf = None, AstNodeId.synthetic())
            Some(CheckedTerm(Interpreter.evalLam(lam, expectedPi, env), lam))
          } catch {
            case _: TypeMismatch | _: ImplicitReconstructionFailed => None
          }
        }

      case _ => None
    }

  // Adapt a synthesized value to the expected type: eta-expand a polymorphic function against a
  // monomorphic expected Pi if that helps, otherwise plain subsumption.
  private def subsume(checked: CheckedTerm, expectedTy: Value, env: Env, span: Span): CheckedTerm =
    tryInstantiateImplicits(checked, expectedTy, env, span)
      .getOrElse(checkTermFits(checked, expectedTy))

  def checkTerm(term: CA.Term, env: Env): CheckedTerm =
    check(term, None, env)

  def checkTerm(term: CA.Term, expectedTy: Value, env: Env): CheckedTerm =
    check(term, Some(expectedTy), env)

  private def check(term: CA.Term, expectedTy: Option[Value], env: Env): CheckedTerm =
    try {
      term match {
        case CA.Term.NatLit(value, span) =>
          val family = Packed.natFamily(env, span)
          val synthed = CheckedTerm(VPacked(NatCodec, value, family), EA.Term.NatLit(value, span))
          expectedTy.fold(synthed)(expected => checkTermFits(synthed, expected))
        case CA.Term.Select(base, field, span) =>
          val checkedBase = checkTerm(base, env)
          checkSelect(checkedBase, field, span, env, expectedTy)
        case CA.Term.Proj(familyName, fieldIndex, base, span) =>
          checkProj(familyName, fieldIndex, checkTerm(base, env), span, expectedTy)
        case app: CA.Term.App =>
          val checkedFn = checkTerm(app.fn, env)
          val checkedArgs = app.args.map(PendingArg.term)
          val checkedApp =
            checkApplyChecked(checkedFn.value, checkedFn.residual, checkedArgs, env, app.span, expectedTy)
          CheckedTerm(checkedApp.value, checkedApp.residual)
        case m: CA.Term.Match => MatchChecker.checkMatch(m, env, expectedTy)
        case b: CA.Term.Body  => checkBody(b, env, expectedTy)
        case pi: CA.Term.Pi =>
          val checked = checkPi(pi, env)
          val checkedTerm = CheckedTerm(checked.vpi, checked.residual)
          expectedTy.fold(checkedTerm)(expected => checkTermFits(checkedTerm, expected))
        // Refs evaluate directly; against an expected type they get subsumption
        // (eta-adaptation of polymorphic functions).
        case ref: CA.Term.Ref =>
          val residual = elabRef(ref)
          val synthed = CheckedTerm(Interpreter.evalTerm(residual, env), residual)
          expectedTy.fold(synthed)(expected => subsume(synthed, expected, env, ref.span))
        case l: CA.Term.Lam =>
          val synthed = checkLam(l, env)
          expectedTy.fold(synthed)(expected => subsume(synthed, expected, env, l.span))
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw e.withSpan(term.span)
    }

}
