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

  /** A Pi's checked binders and result, before its closure: the caller decides what the closure is. */
  private final case class CheckedTelescope(binders: Vector[CA.Binder], bodyEnv: Env, outTy: Value, out: CA.Term)

  /** A checker-produced term; callers cannot construct or copy one themselves. */
  final class CheckedTerm private (val value: Value, val residual: CA.Term)

  private[raccoonlang] object CheckedTerm {
    def apply(value: Value, residual: CA.Term): CheckedTerm = new CheckedTerm(value, residual)
  }

  /** Check an elaborated program, retaining the value computed by the checking pass for the public runner. */
  def check(program: Execution.ElaboratedProgram): Execution.CheckedProgram =
    Execution.check(program)

  /**
   * Check every declaration, collecting one diagnostic per independent failure. A declaration that names a failed (or
   * skipped) one is skipped silently; the body is checked only when nothing failed. Every rejection leaves as one
   * `CheckFailure`. An `InternalError` is never collected: it aborts.
   */
  private[raccoonlang] def checkRaw(program: CA.Program, prelude: Prelude.Config): Option[Value] = {
    var env = prelude.checkedEnv
    var unavailable = Set.empty[String]
    val diagnostics = Vector.newBuilder[Diagnostic]

    program.decls.foreach { decl =>
      // The scan is a full traversal; skip it while nothing has failed.
      if (unavailable.nonEmpty && decl.references(unavailable)) unavailable ++= decl.definedNames
      else
        try env = Interpreter.evalDecl(decl, env)
        catch {
          case diagnostic: Diagnostic =>
            diagnostics += diagnostic
            unavailable ++= decl.definedNames
        }
    }

    val collected = diagnostics.result()
    if (collected.nonEmpty) throw Execution.CheckFailure(collected)
    try program.body.map(body => checkTerm(body, env).value)
    catch { case diagnostic: Diagnostic => throw Execution.CheckFailure(Vector(diagnostic)) }
  }

  private final case class CheckedApply(value: Value, residual: CA.Term.App)
  private[raccoonlang] final case class CheckedRecursiveDef(name: String, vpi: VPi, residual: CA.Term.Lam)

  /**
   * An argument of a checked application: its own syntax, checked inside the application's argument frame, or a value
   * the caller has already checked (a selected field's base). An argument is synthesized, except that at a binder of a
   * sort parameter it is checked against that parameter, the one place an expression of one may stand as an argument
   * (spec §2.2). The verification pass then checks each one against its binder type, as any check is synthesis followed
   * by equality.
   */
  private sealed trait PendingArg {
    def check(env: Env, parameter: Option[ParameterTpe]): CheckedTerm
  }

  private object PendingArg {
    final case class Term(term: CA.Term) extends PendingArg {
      def check(env: Env, parameter: Option[ParameterTpe]): CheckedTerm =
        parameter match {
          case Some(parameterTpe) => checkTerm(term, parameterTpe, env)
          case None               => checkTerm(term, env)
        }
    }

    // A selected field's base was checked where it stands, and the verification pass fits it to its binder.
    final case class Checked(checked: CheckedTerm) extends PendingArg {
      def check(env: Env, parameter: Option[ParameterTpe]): CheckedTerm = checked
    }

    def term(t: CA.Term): PendingArg = Term(t)

    def checked(c: CheckedTerm): PendingArg = Checked(c)
  }

  // Universes are NOT cumulative (Lean-style): a type fits exactly the sorts defEq to its own.
  // Non-cumulativity is what makes `.tpe` canonical enough for implicit projection — the level a
  // spec reads is the only level the argument can carry.
  // This is `defEq`, keeping the unifier's failure for the report instead of re-deriving it.
  def checkFits(actual: Value, expected: Value): Unit =
    ValueEquivalence.tryUnify(actual, expected, EqStore.empty) match {
      case Right(_)     =>
      case Left(failed) => fail(TypeMismatch(expected, actual, Some(failed)))
    }

  def checkType(value: Value, tyVal: Value): Unit =
    checkFits(value.tpe, tyVal)

  def getUniverse(value: Value): VSort = {
    value.tpe match {
      case u: VSort => u
      case _        => fail(NotAType(value.tpe))
    }
  }

  private def assertNonRawRecursive(v: Value): Unit = {
    v match {
      // TerminationChecker.rawRecursiveStub always names its stubs `ValueId.Const(name)`.
      case VLam(_, ValueId.Const(name), LamBody.Native(_, _, true)) => fail(InvalidRecursiveOccurrence(name))
      case VLam(_, _, LamBody.Native(_, _, true))                   => wtf("raw-recursive stub without a constant name")
      case _                                                        =>
    }
  }

  /**
   * The sort parameter a binder binds a variable of. Its type is the closed name of the parameter, so it is recognized
   * before any argument is known; no other term evaluates to a sort parameter, since nothing of another type can have
   * one as a value.
   */
  private def binderParameter(binder: CA.Binder, env: Env): Option[ParameterTpe] =
    binder.ty match {
      case ref: CA.Term.GlobalRef =>
        Interpreter.evalTerm(ref, env) match {
          case parameterTpe: ParameterTpe => Some(parameterTpe)
          case _                          => None
        }
      case _ => None
    }

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
   *
   * `span` only goes onto the residual; failures are located by the enclosing `check`.
   */
  private def checkApplyChecked(
      fnValue: Value,
      fnResidual: CA.Term,
      providedArgs: Vector[PendingArg],
      env: Env,
      span: Span
  ): CheckedApply =
    fnValue.tpe match {
      case pi: VPi =>
        val binders = pi.binders
        // Grouping is part of a function type's identity: a call supplies exactly this Pi's own
        // explicit binders. `(a:A) -> (b:B) -> C` takes one argument and returns a function;
        // `(a:A)(b:B) -> C` takes two. Supplying the wrong number is an arity error here, not a
        // descent into the codomain — `f(x)(y)` is how a nested group is reached.
        if (providedArgs.length != pi.numExplicit)
          fail(ArityMismatch(pi.numExplicit, providedArgs.length))

        val known = new Array[Value](binders.length)
        val checkedResiduals = Vector.newBuilder[CA.Term]
        var providedValues = Vector.empty[Value]
        // Each binder's written-argument position from 1, or 0 for a projected implicit. Kept as ints
        // so that frames are only built on failure.
        val argumentPositions = new Array[Int](binders.length)

        var explicitIdx = 0
        binders.zipWithIndex.foreach { case (binder, idx) =>
          if (!binder.isImplicit) {
            argumentPositions(idx) = explicitIdx + 1
            // Arguments are checked where they stand and verified in the final pass; see PendingArg.
            val checked =
              framed(Frame.InArgument(argumentPositions(idx), binder.name, applyHeadName(fnResidual)))(
                providedArgs(explicitIdx).check(env, binderParameter(binder, pi.env))
              )
            assertNonRawRecursive(checked.value)
            known(idx) = checked.value
            checkedResiduals += checked.residual
            providedValues :+= checked.value
            // Specs always root at a non-implicit binder, so every implicit lands during this walk.
            pi.implicitRoots.getOrElse(explicitIdx, Vector.empty).foreach { implicitIdx =>
              Projection.project(binders(implicitIdx).projection.get, providedValues) match {
                case Right(value) => known(implicitIdx) = value
                case Left(reason) =>
                  fail(ImplicitReconstructionFailed(binders(implicitIdx).name, applyHeadName(fnResidual), reason))
              }
            }
            explicitIdx += 1
          }
        }

        // Verification pass: with the full group known, every binder type is evaluable in order
        // and each arg (provided or projected) must fit it. Projection was only a choice — this
        // pass is what makes the application well-typed. Arguments are bound as supplied.
        val calleeEnv =
          binders.indices.foldLeft(pi.env) { case (curEnv, idx) =>
            def bind: Env = BinderOps.bindValueAndCheck(curEnv, binders(idx), known(idx))
            val position = argumentPositions(idx)
            if (position == 0) bind
            else framed(Frame.InArgument(position, binders(idx).name, applyHeadName(fnResidual)))(bind)
          }
        val finalArgs = binders.map(binder => calleeEnv(binder.localRef))
        val residual = CA.Term.App(fnResidual, checkedResiduals.result(), span)
        CheckedApply(Interpreter.evalApply(fnValue, finalArgs), residual)

      case _ => fail(CannotApplyNonFunction(fnValue))
    }

  private def checkTelescope(pi: CA.Term.Pi, env: Env, familyParams: Int): CheckedTelescope = {
    // Implicit legality (forced-by-later-binders) and projection specs come from BinderOps.checkBinders.
    val checkedBinders = BinderOps.checkBinders(pi.binders, env, familyParams)
    val checkedOut = checkTypeTerm(pi.out, checkedBinders.env)
    CheckedTelescope(checkedBinders.binders, checkedBinders.env, checkedOut.value, checkedOut.residual)
  }

  /** The residual Pi of a checked telescope and closure, and its value with its classifier forced. */
  private def finishPi(telescope: CheckedTelescope, closure: CA.Closure, span: Span, env: Env): CheckedPi = {
    val residual =
      CA.Term.Pi(
        telescope.binders,
        telescope.out,
        closure,
        span,
        knownPropValued = Interpreter.stablePiPropClassification(telescope.outTy)
      )
    val evaluated = evalPi(residual, env)
    // Force the classifier at declaration. Reuse the already checked fresh telescope instead of eta-expanding every
    // binder a second time.
    val classifier = Interpreter.piClassifierFromChecked(
      telescope.binders,
      telescope.bodyEnv,
      telescope.outTy,
      evaluated.closureKind,
      evaluated.closureScope
    )
    CheckedPi(evaluated.copy(classifier0 = () => classifier), telescope.bodyEnv, telescope.outTy, residual)
  }

  /** A function type captures nothing, so its closure is always written (spec §1): the elaborator writes it so. */
  private def checkPi(pi: CA.Term.Pi, env: Env, familyParams: Int = 0): CheckedPi = {
    val telescope = checkTelescope(pi, env, familyParams)
    def written(field: CA.ClosureField, parameter: ParameterTpe): CA.ClosureField =
      field match {
        case CA.ClosureField.Written(term) => CA.ClosureField.Written(checkTerm(term, parameter, env).residual)
        case _: CA.ClosureField.Derived    => wtf(s"The function type $pi has a derived closure field")
      }
    finishPi(
      telescope,
      CA.Closure(written(pi.closure.kind, KindTpe), written(pi.closure.scope, LifetimeTpe)),
      pi.span,
      env
    )
  }

  /**
   * Constructor telescopes route through here so unforced family params (the leading `familyParams` binders) get
   * demoted instead of rejected; see Projection.compile. A constructor's type is a declaration's type, so it may be
   * large.
   */
  private[raccoonlang] def getConstructorType(term: CA.Term, env: Env, familyParams: Int): Value =
    term match {
      case pi: CA.Term.Pi => checkPi(pi, env, familyParams).vpi
      case other          => checkDeclType(other, env).value
    }

  // Returning the residual term lets callers preserve checked let/lambda structure instead of re-checking.
  private def checkBody(body: CA.Term.Body, env: Env): CheckedTerm = {
    val checkedLets = Vector.newBuilder[CA.Let]
    var curEnv = env

    body.lets.foreach { l =>
      val checkedTy = l.ty.map(tyTerm => checkTypeTerm(tyTerm, curEnv))
      val checkedValue = checkedTy match {
        case Some(ty) => checkTerm(l.value, ty.value, curEnv)
        case None     => checkTerm(l.value, curEnv)
      }
      checkedLets += CA.Let(l.localRef, checkedTy.map(_.residual), checkedValue.residual, l.span)
      curEnv = curEnv.putLocal(l.localRef, checkedValue.value)
    }

    val checkedRes = checkTerm(body.res, curEnv)
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
      env: Env
  ): CheckedTerm = {
    val vType = base.value.tpe
    val family = vType match {
      case InductiveFamilyValue(instance) => instance
      case _                              => fail(NotAType(vType))
    }
    val selectorName = s"${family.head.name}.$field"
    if (!env.globals.contains(selectorName)) fail(NotFound(selectorName))
    val selector = env(selectorName)
    val applied =
      checkApplyChecked(
        selector,
        CA.Term.GlobalRef(selectorName, span),
        Vector(PendingArg.checked(base)),
        env,
        span
      )
    CheckedTerm(applied.value, applied.residual)
  }

  /**
   * A derived closure field as an expression (spec §8, G9): each variable of the normal form is written as a local of
   * `env` bound to exactly that variable. Only a header's, lambda's or function type's binder binds a kind or lifetime,
   * and it binds a local, so every variable a capture's type mentions has one; in a refined branch two locals may
   * denote one variable, and either is correct.
   */
  private def quoteParameter(vars: DepSet, form: CA.Form, env: Env, span: Span): CA.Term = {
    val locals = env.locals.iterator.flatMap { case (ref, value) =>
      val variable = value match {
        case kind: Kind         => Kind.singleVariable(kind)
        case lifetime: Lifetime => Lifetime.singleVariable(lifetime)
        case _                  => None
      }
      variable.filter(vars.contains).map(_ -> ref)
    }.toMap
    val refs = Vector.newBuilder[CA.Term]
    vars.foreach { id =>
      refs += CA.Term.LocalRef(locals.getOrElse(id, wtf(s"No local binds the variable $id of a derived closure")), span)
    }
    refs.result().reduceLeft((acc, ref) => CA.Term.FormOp(form, Vector(acc, ref), span))
  }

  private def quoteKind(kind: Kind, env: Env, span: Span): CA.Term =
    if (kind.isLin) CA.Term.FormOp(CA.Form.KindLin, Vector.empty, span)
    else if (kind.isUnr) CA.Term.FormOp(CA.Form.KindUnr, Vector.empty, span)
    else quoteParameter(kind.vars, CA.Form.KindJoin, env, span)

  private def quoteLifetime(lifetime: Lifetime, env: Env, span: Span): CA.Term =
    if (lifetime.isEmpty) CA.Term.FormOp(CA.Form.LifetimeEmpty, Vector.empty, span)
    else quoteParameter(lifetime.vars, CA.Form.LifetimeUnion, env, span)

  /**
   * A lambda's closure is what it captures (spec §4.3): an omitted field is derived as the join of its captures' kinds
   * or scopes, and a written one must contain that join, else `KindExceeded` or `ScopeExceeded` naming a capture it
   * does not contain. Only the lambda and its captures' types decide it, never where the lambda stands.
   */
  private def checkLamClosure(l: CA.Term.Lam, env: Env): CA.Closure = {
    val captures = Interpreter.lambdaCaptures(l, env)
    val (derivedKind, derivedScope) = Interpreter.derivedClosure(captures)
    def part(capture: Interpreter.Capture): String = s"capture ${capture.ref.name} : ${capture.value.tpe}"
    val kind = l.ty.closure.kind match {
      case CA.ClosureField.Written(term) =>
        val checked = checkTerm(term, KindTpe, env)
        val written = Interpreter.getKind(checked.value)
        captures.find(capture => !Kind.contains(written, capture.sort.kind)).foreach { capture =>
          at(term.span) { fail(KindExceeded("Lambda", written, part(capture), capture.sort.kind)) }
        }
        CA.ClosureField.Written(checked.residual)
      case _: CA.ClosureField.Derived => CA.ClosureField.Derived(Some(quoteKind(derivedKind, env, l.span)))
    }
    val scope = l.ty.closure.scope match {
      case CA.ClosureField.Written(term) =>
        val checked = checkTerm(term, LifetimeTpe, env)
        val written = Interpreter.getLifetime(checked.value)
        captures.find(capture => !Lifetime.contains(written, capture.sort.scope)).foreach { capture =>
          at(term.span) { fail(ScopeExceeded("Lambda", written, part(capture), capture.sort.scope)) }
        }
        CA.ClosureField.Written(checked.residual)
      case _: CA.ClosureField.Derived => CA.ClosureField.Derived(Some(quoteLifetime(derivedScope, env, l.span)))
    }
    CA.Closure(kind, scope)
  }

  private def checkLam(l: CA.Term.Lam, env: Env): CheckedTerm = {
    val telescope = checkTelescope(l.ty, env, familyParams = 0)
    val checkedVpi = finishPi(telescope, checkLamClosure(l, env), l.ty.span, env)
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
          val name = l.name.getOrElse(wtf("Recursive lambda must have a name"))
          val recursiveSelf = TerminationChecker.rawRecursiveSelf(name, vpi, decreaseSpec, bodyEnv)
          bodyEnv.putLocal(ref, recursiveSelf)
        case None => bodyEnv
      }

    val checkedBody = checkTerm(l.body, checkedVpi.outTy, recurEnv)
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
    if (definitions.isEmpty) fail(InvalidRecursiveGroup("the group must not be empty"))
    if (definitions.map(_.name).distinct.length != definitions.length)
      fail(InvalidRecursiveGroup("global names must be distinct"))
    if (definitions.map(_.peerRef).distinct.length != definitions.length)
      fail(InvalidRecursiveGroup("peer refs must be distinct"))

    val peers = definitions.map(definition => definition.peerRef -> definition.name)
    val peerRefs = definitions.iterator.map(_.peerRef).toSet
    val ambientPeerRefs = peerRefs.intersect(env.locals.keySet)
    if (ambientPeerRefs.nonEmpty)
      fail(InvalidRecursiveGroup(s"peer refs collide with the incoming environment: ${ambientPeerRefs.mkString(", ")}"))
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
      val checkedBody = checkTerm(definition.body, checkedPi.outTy, bodyEnv)
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

  /** A term at a type position: it must be a type. */
  def checkTypeTerm(term: CA.Term, env: Env): CheckedTerm =
    at(term.span) {
      val checked = synthesize(term, env)
      assertType(checked.value)
      checked
    }

  /**
   * A binder's type: a type, or a sort parameter where the binder's site admits it (spec §2.2). A parameter site admits
   * every sort parameter, a function type's or lambda's binder only `Lifetime`, and a field site none.
   */
  def checkBinderType(binder: CA.Binder, env: Env): CheckedTerm =
    at(binder.ty.span) {
      val checked = synthesize(binder.ty, env)
      (binder.site, checked.value) match {
        case (CA.BinderSite.Parameter, _: ParameterTpe) =>
        case (CA.BinderSite.Function, LifetimeTpe)      =>
        case _                                          => assertType(checked.value)
      }
      checked
    }

  /**
   * A declaration's type: a type, or a large function type, since only a declaration's own type may bind a level (spec
   * §2.2). A definition, opaque definition, axiom, family or constructor may therefore be level-polymorphic.
   */
  def checkDeclType(term: CA.Term, env: Env): CheckedTerm =
    at(term.span) {
      val checked = synthesize(term, env)
      checked.value.tpe match {
        case _: VSort | Large =>
        case _                => fail(NotAType(checked.value))
      }
      checked
    }

  def assertType(value: Value): Unit =
    value.tpe match {
      case _: VSort =>
      case _        => fail(NotAType(value))
    }

  /**
   * A term must have a type wherever it stands (spec §2.2), except where `admitsNonType` allows otherwise. So a sort
   * parameter itself, an expression of one, and a reference whose type is large are `NotAType` there; a large reference
   * may still head an application (`checkHead`).
   */
  private def requireTyped(value: Value): Unit =
    value.tpe match {
      case _: VSort      =>
      case SortParameter => fail(NotAType(value))
      case tpe           => assertType(tpe)
    }

  /**
   * The positions where a term whose type is not a type may stand: an expression of a sort parameter where one is
   * expected (a sort's field, the argument at a binder of a sort parameter), and a definition's lambda at its own large
   * declared type. Equality with the expected type then decides as for any check, so a kind where a level is expected
   * is a `TypeMismatch`, as a term of any other type there is.
   */
  private def admitsNonType(actualTy: Value, expectedTy: Value): Boolean =
    (actualTy, expectedTy) match {
      case (_: ParameterTpe, _: ParameterTpe) => true
      case _                                  => (actualTy.tpe eq Large) && (expectedTy.tpe eq Large)
    }

  def checkTerm(term: CA.Term, env: Env): CheckedTerm =
    check(term, None, env)

  def checkTerm(term: CA.Term, expectedTy: Value, env: Env): CheckedTerm =
    check(term, Some(expectedTy), env)

  /**
   * The checker's locating boundary: an unlocated failure raised while checking `term` belongs to `term`.
   *
   * Checking is synthesis followed by equality. The term is synthesized without looking at the expectation; its type
   * must be a type unless the expected one admits otherwise, and must then equal the expected one: a term's type never
   * depends on where it stands.
   */
  private def check(term: CA.Term, expected: Option[Value], env: Env): CheckedTerm =
    at(term.span) {
      val synthed = synthesize(term, env)
      expected match {
        case Some(expectedTy) =>
          if (!admitsNonType(synthed.value.tpe, expectedTy)) requireTyped(synthed.value)
          at(typeSite(term))(checkType(synthed.value, expectedTy))
        case None => requireTyped(synthed.value)
      }
      synthed
    }

  /**
   * An application's head: the one position where a reference whose type is large may stand, since a level-polymorphic
   * declaration is used only applied (spec §2.2).
   */
  private def checkHead(term: CA.Term, env: Env): CheckedTerm = at(term.span)(synthesize(term, env))

  /** A term's own type, whatever position it stands at; the callers above decide what the position admits. */
  private def synthesize(term: CA.Term, env: Env): CheckedTerm =
    term match {
      case CA.Term.NatLit(value, span) =>
        val layout = env.nativeLiterals.natLayout.getOrElse(fail(NatLiteralUnavailable("no validated Nat layout")))
        CheckedTerm(VPacked.nat(value, layout.natTpe), CA.Term.NatLit(value, span))
      case CA.Term.StrLit(scalars, span) =>
        val layout =
          env.nativeLiterals.stringLayout.getOrElse(fail(StringLiteralUnavailable("no validated String layout")))
        val checked = CheckedTerm(Packed.evalStrLit(scalars, env), CA.Term.StrLit(scalars, span))
        if (!ValueEquivalence.defEq(checked.value.tpe, layout.stringTpe))
          wtf("String literal evaluator returned the wrong type")
        checked
      case CA.Term.Select(base, field, span) => checkSelect(checkTerm(base, env), field, span, env)
      case app: CA.Term.App =>
        val checkedFn = checkHead(app.fn, env)
        val checkedApp =
          checkApplyChecked(checkedFn.value, checkedFn.residual, app.args.map(PendingArg.term), env, app.span)
        CheckedTerm(checkedApp.value, checkedApp.residual)
      case m: CA.Term.Match => MatchChecker.checkMatch(m, env)
      case b: CA.Term.Body  => checkBody(b, env)
      case pi: CA.Term.Pi =>
        val checked = checkPi(pi, env)
        CheckedTerm(checked.vpi, checked.residual)
      case ref: CA.Term.Ref => CheckedTerm(Interpreter.evalTerm(ref, env), ref)
      case l: CA.Term.Lam   => checkLam(l, env)
      case CA.Term.Sort(level, kind, scope, span) =>
        val checkedLevel = checkTerm(level, LevelTpe, env)
        val checkedKind = checkTerm(kind, KindTpe, env)
        val checkedScope = checkTerm(scope, LifetimeTpe, env)
        val levelV = Interpreter.getLevel(checkedLevel.value)
        val kindV = Interpreter.getKind(checkedKind.value)
        if (!Sorts.admitsKind(levelV, kindV)) fail(LinearProp(kindV, levelV))
        CheckedTerm(
          Interpreter.evalSort(checkedLevel.value, checkedKind.value, checkedScope.value),
          CA.Term.Sort(checkedLevel.residual, checkedKind.residual, checkedScope.residual, span)
        )
      case CA.Term.FormOp(form, args, span) =>
        val checkedArgs = args.map(checkTerm(_, Interpreter.parameterType(form.parameter), env))
        CheckedTerm(
          Interpreter.evalFormOp(form, checkedArgs.map(_.value)),
          CA.Term.FormOp(form, checkedArgs.map(_.residual), span)
        )
    }

  /** Where a term's type comes from, for locating a mismatch: a block's type is its result's. */
  @annotation.tailrec
  private def typeSite(term: CA.Term): Span =
    term match {
      case body: CA.Term.Body => typeSite(body.res)
      case other              => other.span
    }

}
