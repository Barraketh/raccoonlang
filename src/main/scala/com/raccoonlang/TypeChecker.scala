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
   * `CheckFailure`, with the environment's `String` layout to print it with. An `InternalError` is never collected: it
   * aborts.
   *
   * `EvaluationTooDeep` stops checking where it arises, with the diagnostics collected so far (PROOF_BY_EVALUATION
   * §2.5): the overflow may have unwound past the restoration of the checker's state, such as the thread-local tables
   * of `ValueEquivalence` and `InductiveChecks` and the process-wide ones of `FreshVar` and `Atoms`, so nothing after
   * it is checked on that state.
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
          case diagnostic: Diagnostic if diagnostic.error == EvaluationTooDeep =>
            throw Execution.CheckFailure(diagnostics.result() :+ diagnostic, env.nativeLiterals.stringLayout)
          case diagnostic: Diagnostic =>
            diagnostics += diagnostic
            unavailable ++= decl.definedNames
        }
    }

    val collected = diagnostics.result()
    if (collected.nonEmpty) throw Execution.CheckFailure(collected, env.nativeLiterals.stringLayout)
    try
      program.body.map { body =>
        // The program's boundary, as `Interpreter.evalDecl` is a declaration's: an overflow while checking and
        // evaluating the body is `EvaluationTooDeep` at the whole body.
        try {
          val result = checkTerm(body, env).value
          // The result is outside every binder, like a global, so it may not be linear either (spec §3.2).
          if (Linearity.isLinear(result.tpe)) at(typeSite(body))(fail(LinearGlobal(None, result.tpe)))
          result
        } catch { case _: StackOverflowError => at(body.span)(fail(EvaluationTooDeep)) }
      }
    catch {
      case diagnostic: Diagnostic => throw Execution.CheckFailure(Vector(diagnostic), env.nativeLiterals.stringLayout)
    }
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
      case VLam(_, ValueId.Const(name), LamBody.Native(_, _, true, _)) => fail(InvalidRecursiveOccurrence(name))
      case VLam(_, _, LamBody.Native(_, _, true, _)) => wtf("raw-recursive stub without a constant name")
      case _                                         =>
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
   * An evidence binder's argument is supplied in the call's bracket group, `providedEvidence`, one proof per evidence
   * binder, or else the call writes none and each is discharged (Discharge; PROOF_BY_EVALUATION §1.2, §1.3). Either way
   * the final pass evaluates its type, with every earlier argument known, once: a supplied proof must fit that
   * proposition, and an omitted one is discharged from it. The residual keeps neither, since evaluation binds an
   * evidence parameter to an erased proof of the same proposition (Interpreter.residualArguments). A constructor is
   * applied here as any function is, so its evidence fields are discharged or supplied alike (§1.8).
   *
   * `span` goes onto the residual, and is where a discharge stands for sealing; failures are located by the enclosing
   * `check`.
   */
  private def checkApplyChecked(
      fnValue: Value,
      fnResidual: CA.Term,
      providedArgs: Vector[PendingArg],
      providedEvidence: Vector[CA.Term],
      env: Env,
      span: Span
  ): CheckedApply =
    fnValue.tpe match {
      case pi: VPi =>
        val binders = pi.binders
        val callee = applyHeadName(fnResidual)
        // Grouping is part of a function type's identity: a call supplies exactly this Pi's own
        // explicit binders. `(a:A) -> (b:B) -> C` takes one argument and returns a function;
        // `(a:A)(b:B) -> C` takes two. Supplying the wrong number is an arity error here, not a
        // descent into the codomain — `f(x)(y)` is how a nested group is reached.
        if (providedArgs.length != pi.numExplicit) {
          // A constructor's telescope starts with its family's parameters, implicit where later arguments determine them.
          val familyParams = fnValue match {
            case head: ConstructorHead => head.numErasedFamilyArgs
            case _                     => 0
          }
          val implicitFamily = binders.take(familyParams).filter(_.mode == BinderMode.Implicit).map(_.name)
          val explicit = binders.filter(_.mode == BinderMode.Explicit).map(_.name)
          fail(ArityMismatch(pi.numExplicit, providedArgs.length, ArityMismatch.Call(callee, explicit, implicitFamily)))
        }
        if (providedEvidence.nonEmpty && providedEvidence.length != pi.numEvidence)
          fail(ArityMismatch(pi.numEvidence, providedEvidence.length, ArityMismatch.Evidence))

        val known = new Array[Value](binders.length)
        val checkedResiduals = Vector.newBuilder[CA.Term]
        var providedValues = Vector.empty[Value]
        // Each binder's written position from 1 among the explicit arguments or the supplied evidence, as its mode
        // says, or 0 for a projected implicit or discharged evidence. Kept as ints so that frames are only built on
        // failure.
        val writtenPositions = new Array[Int](binders.length)
        def frame(idx: Int): Frame =
          binders(idx).mode match {
            case BinderMode.Evidence => Frame.InEvidence(writtenPositions(idx), binders(idx).name, callee)
            case _                   => Frame.InArgument(writtenPositions(idx), binders(idx).name, callee)
          }

        var explicitIdx = 0
        var evidenceIdx = 0
        binders.zipWithIndex.foreach { case (binder, idx) =>
          binder.mode match {
            case BinderMode.Explicit =>
              writtenPositions(idx) = explicitIdx + 1
              // Arguments are checked where they stand and verified in the final pass; see PendingArg.
              val checked = framed(frame(idx))(providedArgs(explicitIdx).check(env, binderParameter(binder, pi.env)))
              assertNonRawRecursive(checked.value)
              known(idx) = checked.value
              checkedResiduals += checked.residual
              providedValues :+= checked.value
              // Specs always root at an explicit binder, so every implicit lands during this walk.
              pi.implicitRoots.getOrElse(explicitIdx, Vector.empty).foreach { implicitIdx =>
                Projection.project(binders(implicitIdx).projection.get, providedValues) match {
                  case Right(value) => known(implicitIdx) = value
                  case Left(reason) => fail(ImplicitReconstructionFailed(binders(implicitIdx).name, callee, reason))
                }
              }
              explicitIdx += 1
            // A supplied proof is synthesized where it stands, as an argument is, and fits its proposition below.
            case BinderMode.Evidence if providedEvidence.nonEmpty =>
              writtenPositions(idx) = evidenceIdx + 1
              val checked = framed(frame(idx))(checkTerm(providedEvidence(evidenceIdx), env))
              assertNonRawRecursive(checked.value)
              known(idx) = checked.value
              evidenceIdx += 1
            case BinderMode.Evidence | BinderMode.Implicit =>
          }
        }

        // Verification pass: with the full group known, every binder type is evaluable in order
        // and each arg (provided or projected) must fit it. Projection was only a choice — this
        // pass is what makes the application well-typed. Arguments are bound as supplied.
        val calleeEnv =
          binders.indices.foldLeft(pi.env) { case (curEnv, idx) =>
            val binder = binders(idx)
            def bind: Env =
              binder.mode match {
                // The proposition is evaluated here, once, for a supplied proof and a discharge alike.
                // A supplied proof is bound as the canonical proof of the proposition, as evaluation binds one, so
                // what an evidence argument holds is determined by the arguments before it (VApp.determiningArgs).
                case BinderMode.Evidence =>
                  val proposition = Interpreter.evalTerm(binder.ty, curEnv)
                  val proof =
                    if (providedEvidence.nonEmpty) {
                      checkType(known(idx), proposition)
                      Value.canonicalizeProof(VProof(proposition))
                    } else
                      Discharge.discharge(proposition, span, env) match {
                        case Right(proof) => proof
                        case Left(failure) =>
                          fail(
                            EvidenceNotDischarged(
                              binder.name,
                              callee,
                              failure.path,
                              failure.proposition,
                              failure.reason
                            )
                          )
                      }
                  BinderOps.bindValue(curEnv, binder, proof)
                // An argument at a binder whose type is a sort is a type, confined where the application stands.
                case BinderMode.Explicit | BinderMode.Implicit =>
                  val bound = BinderOps.bindValueAndCheck(curEnv, binder, known(idx))
                  known(idx).tpe match {
                    case _: VSort => requireInScope(known(idx), env)
                    case _        =>
                  }
                  bound
              }
            if (writtenPositions(idx) == 0) bind else framed(frame(idx))(bind)
          }
        val finalArgs = binders.map(binder => calleeEnv(binder.localRef))
        val residual = CA.Term.App(fnResidual, checkedResiduals.result(), Vector.empty, span)
        CheckedApply(Interpreter.evalApply(fnValue, finalArgs), residual)

      case _ => fail(CannotApplyNonFunction(fnValue))
    }

  private def checkTelescope(pi: CA.Term.Pi, env: Env, familyParams: Int): CheckedTelescope = {
    // Implicit legality (forced-by-later-binders) and projection specs come from BinderOps.checkBinders.
    val checkedBinders = BinderOps.checkBinders(pi.binders, env, familyParams, pi.span)
    val checkedOut = checkTypeTerm(pi.out, checkedBinders.env)
    CheckedTelescope(checkedBinders.binders, checkedBinders.env, checkedOut.value, checkedOut.residual)
  }

  /**
   * The residual of the function type `source`, from its checked telescope and closure, and its value with its
   * classifier forced. The residual is `source` rebuilt, so it keeps its node identity.
   */
  private def finishPi(telescope: CheckedTelescope, closure: CA.Closure, source: CA.Term.Pi, env: Env): CheckedPi = {
    val residual =
      CA.Term.Pi(
        telescope.binders,
        telescope.out,
        closure,
        source.span,
        source.id,
        knownPropValued = Some(Sorts.isProposition(telescope.outTy))
      )
    val evaluated = evalPi(residual, env)
    // Force the classifier at declaration. Reuse the already checked fresh telescope instead of eta-expanding every
    // binder a second time.
    val classifier = Interpreter.piClassifierFromChecked(
      telescope.binders,
      telescope.bodyEnv,
      telescope.outTy,
      evaluated.closureKind,
      evaluated.closureScope,
      evaluated.mentionedScope
    )
    CheckedPi(evaluated.copy(classifier0 = () => classifier), telescope.bodyEnv, telescope.outTy, residual)
  }

  /** A written function type has no body to derive a closure from, so the elaborator writes its closure (spec §1). */
  private def checkPi(pi: CA.Term.Pi, env: Env, familyParams: Int): CheckedPi = {
    val telescope = checkTelescope(pi, env, familyParams)
    def written(field: CA.ClosureField, parameter: ParameterTpe): CA.ClosureField =
      field match {
        case CA.ClosureField.Written(term) => CA.ClosureField.Written(checkTerm(term, parameter, env).residual)
        case CA.ClosureField.Omitted | _: CA.ClosureField.Derived =>
          wtf(s"The function type $pi has an omitted closure field")
      }
    finishPi(
      telescope,
      CA.Closure(written(pi.closure.kind, KindTpe), written(pi.closure.scope, LifetimeTpe)),
      pi,
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
      checkedLets += CA.Let(l.pattern, checkedTy.map(_.residual), checkedValue.residual, l.span)
      curEnv = l.pattern match {
        case local: CA.LetPattern.Local => Interpreter.bindLet(local, checkedValue.value, curEnv)
        case fields: CA.LetPattern.Fields =>
          destructure(fields, checkedValue, checkedTy.fold(typeSite(checkedValue.residual))(_.residual.span), curEnv)
      }
    }

    val checkedRes = checkTerm(body.res, curEnv)
    val lets = checkedLets.result()
    // A let's extent is what follows it (spec §3.2). A plain let's local is reported at the let, and a destructured
    // field's at its component, a `_`'s included (PAIRS_AND_PRELUDE §3.6).
    lets.zipWithIndex.foreach { case (let, idx) =>
      val binders = let.pattern match {
        case CA.LetPattern.Local(ref)      => Vector(ref -> let.span)
        case CA.LetPattern.Fields(vars, _) => vars.map(v => v.ref -> v.span)
      }
      binders.foreach { case (ref, span) =>
        Ledger.requireUsedOnce(
          ref,
          curEnv(ref).tpe,
          span,
          lets.drop(idx + 1).flatMap(later => later.ty.toVector :+ later.value) :+ checkedRes.residual
        )
      }
    }
    CheckedTerm(checkedRes.value, CA.Term.Body(lets, checkedRes.residual, body.span))
  }

  /**
   * A destructuring binds its locals to the fields of its checked value's eta view (PAIRS_AND_PRELUDE §3). The value's
   * type must be an instance of an eta-eligible family outside `Prop` (§3.2), else `NotDestructurable` at `typeAt`,
   * where the type comes from: the annotation when one is written. At the pattern: a destructuring is a match on the
   * value, so it opens a sealed family only in its module (`SealedConstructor`, §3.7), and it has a component for each
   * stored field (`ArityMismatch`, §3.3). A field's type is its local's type at its binder, so it is confined there
   * (spec §4.2).
   */
  private def destructure(pattern: CA.LetPattern.Fields, value: CheckedTerm, typeAt: Span, env: Env): Env = {
    val tpe = value.value.tpe
    val (instance, info) =
      StructEta.eligibleInstance(tpe).getOrElse(at(typeAt)(fail(NotDestructurable(tpe))))
    at(pattern.span) {
      Sealing.requireAccessible(instance.meta.seal, None, pattern.span)
      if (pattern.vars.length != info.fieldCount)
        fail(ArityMismatch(info.fieldCount, pattern.vars.length, ArityMismatch.Fields))
    }
    val bound = Interpreter.bindLet(pattern, value.value, env)
    pattern.vars.foreach(v => at(v.span)(requireInScope(bound(v.ref).tpe, bound)))
    bound
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
    // A base outside every family has no selectors, so the selection names nothing: `base.field` is not found.
    val family = vType match {
      case InductiveFamilyValue(instance) => instance
      case _                              => fail(NotFound(s"${PrettyPrinter.printTerm(base.residual)}.$field"))
    }
    val selectorName = s"${family.head.name}.$field"
    if (!env.globals.contains(selectorName)) fail(NotFound(selectorName))
    Sealing.requireAccessibleGlobal(selectorName, span, env)
    val selector = env(selectorName)
    val applied =
      checkApplyChecked(
        selector,
        CA.Term.GlobalRef(selectorName, span),
        Vector(PendingArg.checked(base)),
        Vector.empty,
        env,
        span
      )
    CheckedTerm(applied.value, applied.residual)
  }

  /**
   * A lambda's closure is what it captures (spec §4.3). A written field must contain each capture's kind or scope, else
   * `KindExceeded` or `ScopeExceeded` naming the capture. An omitted field is derived: the residual carries the
   * captures it is derived from, and evaluating the residual derives it (spec §8), here as anywhere. Only the lambda
   * and its captures' types decide it, never where the lambda stands.
   */
  private def checkLamClosure(l: CA.Term.Lam, env: Env): CA.Closure = {
    val captures = Interpreter.lambdaCaptures(l, env)
    def checkField[P <: Value](field: CA.ClosureField, part: Sorts.Field[P]): CA.ClosureField =
      field match {
        case CA.ClosureField.Written(term) =>
          val checked = checkTerm(term, part.parameter, env)
          val written = part.normalForm(checked.value)
          captures.foreach { capture =>
            Sorts.requireContains(
              part,
              "Lambda",
              written,
              ContainedPart.Capture(capture.ref.name, capture.value.tpe),
              part.ofCapture(capture.value),
              term.span
            )
          }
          CA.ClosureField.Written(checked.residual)
        // A capture whose field is least contributes nothing under any instantiation, so the residual leaves it out.
        case CA.ClosureField.Omitted =>
          CA.ClosureField.Derived(captures.filterNot(capture => part.isLeast(part.ofCapture(capture.value))).map(_.ref))
        case _: CA.ClosureField.Derived => wtf(s"The lambda ${l.name.getOrElse("fun")} was already checked")
      }
    CA.Closure(checkField(l.ty.closure.kind, Sorts.KindField), checkField(l.ty.closure.scope, Sorts.ScopeField))
  }

  /**
   * A lambda's or definition's parameter's extent is what follows it: the later binders' types, the result type and the
   * body (spec §3.2).
   */
  private def requireParametersUsedOnce(pi: CA.Term.Pi, bodyEnv: Env, body: CA.Term): Unit =
    pi.binders.zipWithIndex.foreach { case (binder, idx) =>
      Ledger.requireUsedOnce(
        binder.localRef,
        bodyEnv(binder.localRef).tpe,
        binder.span,
        pi.binders.drop(idx + 1).map(_.ty) :+ pi.out :+ body
      )
    }

  private def checkLam(l: CA.Term.Lam, env: Env): CheckedTerm = {
    val telescope = checkTelescope(l.ty, env, familyParams = 0)
    val checkedVpi = finishPi(telescope, checkLamClosure(l, env), l.ty, env)
    val vpi = checkedVpi.vpi
    val bodyEnv = checkedVpi.bodyEnv

    // Recursive self references stay local for the whole pipeline, even if the source used a qualified name.
    // While checking, the local contains a raw recursive value that enforces the decrease and can only appear as an
    // application head, so the body cannot store it as an ordinary value. The checked lambda keeps the same self ref;
    // when the lambda runs, Interpreter.lamStep binds that ref to the final VLam. The declaration is published to
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
    requireParametersUsedOnce(checkedVpi.residual, bodyEnv, checkedBody.residual)

    val checkedLam =
      CA.Term.Lam(
        checkedVpi.residual,
        checkedBody.residual,
        l.span,
        l.id,
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
    val ambientPeerRefs = peerRefs.intersect(env.localRefs)
    if (ambientPeerRefs.nonEmpty)
      fail(InvalidRecursiveGroup(s"peer refs collide with the incoming environment: ${ambientPeerRefs.mkString(", ")}"))
    val headers = definitions.map { definition =>
      val checkedPi = checkPi(definition.ty, env, familyParams = 0)
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
      requireParametersUsedOnce(checkedPi.residual, checkedPi.bodyEnv, checkedBody.residual)
      val residual = CA.Term.Lam(
        checkedPi.residual,
        checkedBody.residual,
        definition.span,
        definition.id,
        Some(definition.name),
        // A group member has no source `recursion` of its own: the whole group's peer table is
        // what its body's recursive calls resolve through.
        recursion = None,
        recursivePeers = peers
      )
      CheckedRecursiveDef(definition.name, checkedPi.vpi, residual)
    }
  }

  /**
   * An atom's confinement (spec §4.2): a type whose sort's scope names an atom whose `scope` does not enclose the
   * position is `LifetimeEscapes`, and the sort's scope answers it, nothing else. The sort is the type's classifier,
   * and a sort's own sort is at its scope; a large type or a sort parameter is at none. An atom the type's value merely
   * holds, in a closure's code or environment or a stuck computation, does not confine it. This is the one test; the
   * checker applies it to every type it synthesizes or checks against, to each local's type at its binder, and to each
   * argument that is a type. Evaluation never makes it.
   */
  private[raccoonlang] def requireInScope(tpe: Value, env: Env): Unit = {
    // Until a program opens an atom there is nothing to confine: the per-term fast path.
    if (Atoms.all.nonEmpty) {
      val sortScope = Sorts.sortOf(tpe).fold(DepSet.empty)(_.scope.vars)
      val escaped = (sortScope & Atoms.all) -- env.openAtoms
      if (escaped.nonEmpty) {
        val atom = escaped.max
        fail(LifetimeEscapes(FreshVar.parameterName(atom).getOrElse(wtf(s"Atom $atom has no binder name")), tpe))
      }
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
   * every sort parameter, a function type's or lambda's binder only `Lifetime`, and a field site none. An evidence
   * binder's argument is a proof, so its type is a proposition, else `NotAProposition` (PROOF_BY_EVALUATION §1.1). It
   * is the type of the local the binder binds, so it is confined where the binder stands (spec §4.2).
   */
  def checkBinderType(binder: CA.Binder, env: Env): CheckedTerm =
    at(binder.ty.span) {
      val checked = synthesize(binder.ty, env)
      (binder.site, checked.value) match {
        case (CA.BinderSite.Parameter, _: ParameterTpe) =>
        case (CA.BinderSite.Function, LifetimeTpe)      =>
        case _                                          => assertType(checked.value)
      }
      if (binder.mode == BinderMode.Evidence && !Sorts.isProposition(checked.value))
        fail(NotAProposition(binder.name, checked.value))
      requireInScope(checked.value, env)
      checked
    }

  /**
   * A declaration's type: a type, or a large function type, since only a declaration's own type may bind a level (spec
   * §2.2). A definition, axiom, family or constructor may therefore be level-polymorphic.
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
          requireInScope(expectedTy, env)
          if (!admitsNonType(synthed.value.tpe, expectedTy)) requireTyped(synthed.value)
          at(typeSite(term))(checkType(synthed.value, expectedTy))
        case None => requireTyped(synthed.value)
      }
      synthed
    }

  /**
   * An application's head: the one position where a reference whose type is large may stand, since a level-polymorphic
   * declaration is used only applied (spec §2.2). A selection's base is checked as one too: whatever is not a type
   * there has no selectors, which `checkSelect` reports as the selected name not found.
   */
  private def checkHead(term: CA.Term, env: Env): CheckedTerm = at(term.span)(synthesize(term, env))

  /**
   * The first subterm of linear type, in order of completion, among the terms synthesized since the innermost
   * `synthesize` in progress began. A synthesis starts from none, and when it completes it restores what its enclosing
   * synthesis had seen, extended by its own first one, or else by itself when it is linear. A failure abandons the
   * syntheses in progress, and every later one starts from none again. Like FreshVar, it assumes a single checking
   * thread.
   */
  private var linearSubterm: Option[CheckedTerm] = None

  /** Speculative ordinary checking must restore the enclosing token trace even when synthesis rejects the term. */
  private[raccoonlang] def preservingSynthesisState[A](body: => A): A = {
    val before = linearSubterm
    try body
    finally linearSubterm = before
  }

  /**
   * A term's own type, whatever position it stands at; the callers above decide what the position admits. Every term
   * the checker sees is synthesized here, so this is where each synthesized type is confined (spec §4.2), and where a
   * type or a proof is found to contain a subterm of linear type, `LinearInType` located at that subterm (spec §3.2).
   * Types and proofs hold no tokens, since they are copied and dropped freely; `tokenInTypeOrProof` is the one test of
   * it, and until a kind other than `Kind.unr` has been built no term is linear.
   */
  private def synthesize(term: CA.Term, env: Env): CheckedTerm = {
    val enclosing = linearSubterm
    linearSubterm = None
    val synthed = synthesizeTerm(term, env)
    requireInScope(synthed.value.tpe, env)
    val inner = linearSubterm
    inner.foreach { subterm =>
      val holdsNoTokens = synthed.value.tpe match {
        case _: VSort => true
        case tpe      => Sorts.isProposition(tpe)
      }
      if (holdsNoTokens) tokenInTypeOrProof(subterm)
    }
    linearSubterm =
      if (enclosing.isDefined) enclosing
      else if (inner.isDefined) inner
      else if (Linearity.isLinear(synthed.value.tpe)) Some(synthed)
      else None
    synthed
  }

  /**
   * `subterm`, of linear type, stands inside a type or a proof, which hold no tokens (spec §3.2): `LinearInType`,
   * located at it. Besides `synthesize`, a match's named equation, a proposition about its scrutinee, raises it there
   * (MatchChecker).
   */
  private[raccoonlang] def tokenInTypeOrProof(subterm: CheckedTerm): Nothing =
    at(subterm.residual.span)(fail(LinearInType(subterm.residual, subterm.value.tpe)))

  private def synthesizeTerm(term: CA.Term, env: Env): CheckedTerm =
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
      case CA.Term.Select(base, field, span) => checkSelect(checkHead(base, env), field, span, env)
      case app: CA.Term.App =>
        val checkedFn = checkHead(app.fn, env)
        val checkedApp =
          checkApplyChecked(
            checkedFn.value,
            checkedFn.residual,
            app.args.map(PendingArg.term),
            app.evidence,
            env,
            app.span
          )
        CheckedTerm(checkedApp.value, checkedApp.residual)
      case m: CA.Term.Match => MatchChecker.checkMatch(m, env)
      case b: CA.Term.Body  => checkBody(b, env)
      case pi: CA.Term.Pi =>
        val checked = checkPi(pi, env, familyParams = 0)
        CheckedTerm(checked.vpi, checked.residual)
      case global: CA.Term.GlobalRef =>
        Sealing.requireAccessibleGlobal(global.name, global.span, env)
        CheckedTerm(Interpreter.evalTerm(global, env), global)
      case local: CA.Term.LocalRef => CheckedTerm(Interpreter.evalTerm(local, env), local)
      case l: CA.Term.Lam          => checkLam(l, env)
      // The body is checked with the binder denoting the atom, open there (spec §4.1). The construct's type is its
      // body's, which `synthesize` then confines at the scope's own position, where the atom is no longer open.
      case scope: CA.Term.Scope =>
        val checkedBody = checkTerm(scope.body, env.openScope(scope.ref, Atoms.of(scope)))
        CheckedTerm(checkedBody.value, CA.Term.Scope(scope.ref, checkedBody.residual, scope.span, scope.id))
      case CA.Term.Prop(scope, span) =>
        val checkedScope = checkTerm(scope, LifetimeTpe, env)
        CheckedTerm(Sorts.prop(Interpreter.getLifetime(checkedScope.value)), CA.Term.Prop(checkedScope.residual, span))
      case CA.Term.Sort(level, kind, scope, span) =>
        val checkedLevel = checkTerm(level, LevelTpe, env)
        val checkedKind = checkTerm(kind, KindTpe, env)
        val checkedScope = checkTerm(scope, LifetimeTpe, env)
        CheckedTerm(
          Sorts.sort(
            Interpreter.getLevel(checkedLevel.value),
            Interpreter.getKind(checkedKind.value),
            Interpreter.getLifetime(checkedScope.value)
          ),
          CA.Term.Sort(checkedLevel.residual, checkedKind.residual, checkedScope.residual, span)
        )
      case CA.Term.FormOp(form, args, span) =>
        val checkedArgs = args.map(checkTerm(_, Interpreter.parameterType(form.parameter), env))
        CheckedTerm(
          Interpreter.evalFormOp(form, checkedArgs.map(_.value)),
          CA.Term.FormOp(form, checkedArgs.map(_.residual), span)
        )
    }

  /** Where a term's type comes from, for locating a mismatch: a block's type is its result's, a scope's its body's. */
  @annotation.tailrec
  private def typeSite(term: CA.Term): Span =
    term match {
      case body: CA.Term.Body   => typeSite(body.res)
      case scope: CA.Term.Scope => typeSite(scope.body)
      case other                => other.span
    }

}
