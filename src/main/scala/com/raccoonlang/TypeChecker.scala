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
   * An argument of a checked application: its own syntax, synthesized inside the application's argument frame, or a
   * value the caller has already checked (a selected field's base). Arguments are always synthesized; the verification
   * pass then checks each one against its binder type, as any check is synthesis followed by equality.
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

  /**
   * `Sorts.isProposition` plus the validation that `value` is a type at all.
   *
   * The classification itself is deliberately not duplicated — it is the one shared predicate, so the checker can never
   * disagree with proof collapse. What this adds is the `NotAType` check in `getUniverse`, and the one caller,
   * `MatchChecker.checkPropElimination`, needs it: its `motiveTy` is the written `returning` clause, which has not been
   * asserted to be a type by the time elimination is classified. (A type is Prop-valued when it is itself a
   * proposition. The sort `Prop` is not: `Prop : Sort 1`, so `Nat -> Prop` lives in Type, and predicates are data, not
   * proofs — conflating the two made predicates proof-irrelevant and derived False.)
   */
  def isPropValuedType(value: Value): Boolean = {
    getUniverse(value)
    Sorts.isProposition(value)
  }

  private def assertNonRawRecursive(v: Value): Unit = {
    v match {
      // TerminationChecker.rawRecursiveStub always names its stubs `ValueId.Const(name)`.
      case VLam(_, ValueId.Const(name), LamBody.Native(_, _, true)) => fail(InvalidRecursiveOccurrence(name))
      case VLam(_, _, LamBody.Native(_, _, true))                   => wtf("raw-recursive stub without a constant name")
      case _                                                        =>
    }
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
            // Arguments are synthesized and verified in the final pass; see PendingArg.
            val checked =
              framed(Frame.InArgument(argumentPositions(idx), binder.name, applyHeadName(fnResidual)))(
                providedArgs(explicitIdx).synth(env)
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
  private def checkBody(body: CA.Term.Body, env: Env): CheckedTerm = {
    val checkedLets = Vector.newBuilder[CA.Let]
    var curEnv = env

    body.lets.foreach { l =>
      val checkedTy = l.ty.map(tyTerm => checkTerm(tyTerm, curEnv))
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

  def getType(term: CA.Term, env: Env): Value = {
    val res = checkTerm(term, env).value
    assertType(res)
    res
  }

  def assertType(value: Value): Unit =
    value.tpe match {
      case _: VSort =>
      case _        => fail(NotAType(value))
    }

  def checkTerm(term: CA.Term, env: Env): CheckedTerm =
    check(term, None, env)

  def checkTerm(term: CA.Term, expectedTy: Value, env: Env): CheckedTerm =
    check(term, Some(expectedTy), env)

  /**
   * The checker's locating boundary: an unlocated failure raised while checking `term` belongs to `term`.
   *
   * Checking is synthesis followed by equality. Every case synthesizes without looking at the expectation, and the
   * synthesized type must then equal the expected one: a term's type never depends on where it stands.
   */
  private def check(term: CA.Term, expected: Option[Value], env: Env): CheckedTerm =
    at(term.span) {
      val synthed = term match {
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
          val checkedFn = checkTerm(app.fn, env)
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
        case CA.Term.Sort(level, span) =>
          val checkedLevel = checkTerm(level, LevelTpe, env)
          CheckedTerm(Interpreter.evalSort(checkedLevel.value), CA.Term.Sort(checkedLevel.residual, span))
        case CA.Term.LevelOp(form, args, span) =>
          val checkedArgs = args.map(checkTerm(_, LevelTpe, env))
          CheckedTerm(
            Interpreter.evalLevelOp(form, checkedArgs.map(_.value)),
            CA.Term.LevelOp(form, checkedArgs.map(_.residual), span)
          )
      }
      expected.foreach(expectedTy => at(typeSite(term))(checkType(synthed.value, expectedTy)))
      synthed
    }

  /** Where a term's type comes from, for locating a mismatch: a block's type is its result's. */
  @annotation.tailrec
  private def typeSite(term: CA.Term): Span =
    term match {
      case body: CA.Term.Body => typeSite(body.res)
      case other              => other.span
    }

}
