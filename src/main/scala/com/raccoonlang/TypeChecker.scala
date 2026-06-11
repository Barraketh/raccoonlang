package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang.ValueQuote.{quoteContext, quoteTerm, quoteType}
import com.raccoonlang.telescope.{BinderOps, TypePatternMatcher}
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

object TypeChecker {
  private final case class CheckedPi(vpi: VPi, bodyEnv: Env, outTy: Value, residual: EA.Term.Pi)
  final case class CheckedTerm(value: Value, residual: EA.Term)

  def sortLeq(a: Value, b: Value): Boolean = {
    (a, b) match {
      case (Value.VSort(u), Value.VSort(v)) => Level.leq(u, v)
      case (l1: Level, l2: Level)           => Level.leq(l1, l2)
      case (l1: Level, v: Var)              => Level.leq(l1, Level.mk(v.id))
      case (v: Var, l2: Level)              => Level.leq(Level.mk(v.id), l2)
      case _                                => false
    }
  }

  def checkFits(actual: Value, expected: Value, normalizerMap: Normalizers.NormalizerMap): Unit =
    if (
      !ValueEquivalence.defEq(actual, expected, normalizerMap, propIrrelevant = true) &&
      !sortLeq(actual, expected) &&
      !patternInstantiates(actual, expected, normalizerMap)
    )
      throw TypeMismatch(expected, actual)

  // Directional instantiation (docs/type-patterns.md section 7): a pattern-typed value fits a more specific
  // Pi, and a value fits a pattern-typed expectation, when the pattern side matches the other side with
  // closed solutions. Both directions instantiate the pattern; neither solves into the non-pattern side.
  private def patternInstantiates(actual: Value, expected: Value, normalizerMap: Normalizers.NormalizerMap): Boolean =
    (actual, expected) match {
      case (actualPi: VPi, expectedPi: VPi) if actualPi.binders.length == expectedPi.binders.length =>
        (hasPatternBinders(actualPi) && TypePatternMatcher.instantiates(actualPi, expectedPi, normalizerMap)) ||
        (hasPatternBinders(expectedPi) && TypePatternMatcher.instantiates(expectedPi, actualPi, normalizerMap))
      case _ => false
    }

  private def hasPatternBinders(pi: VPi): Boolean = pi.binders.exists(_.captures.nonEmpty)

  def checkType(value: Value, tyVal: Value, normalizerMap: Normalizers.NormalizerMap): Unit =
    checkFits(value.tpe, tyVal, normalizerMap)

  def getUniverse(value: Value): VSort = {
    value.tpe match {
      case u: VSort => u
      case _        => throw NotAType(value.tpe)
    }
  }

  def isPropValue(value: Value): Boolean = value match {
    case PropTpe => true
    case _       => false
  }

  def isPropValuedType(value: Value): Boolean =
    isPropValue(value) || getUniverse(value) == PropTpe

  private def checkApplyValue(fn: Value, args: Vector[Value], env: Env): Value =
    fn.tpe match {
      case pi: VPi =>
        BinderOps.checkAndInstantiate(pi.binders, pi.env, args, env.normalizers)
        Interpreter.evalApply(fn, args, env)
      case _ =>
        val selectorName =
          inductiveFamilyOf(fn.tpe)
            .collect { case family if family.meta.isStruct => s"${family.head.name}.apply" }
            .getOrElse(throw CannotApplyNonFunction(fn))
        val applyField = checkApplyValue(env(selectorName), Vector(fn), env)
        checkApplyValue(applyField, args, env)
    }

  private def elabRef(ref: CA.Term.Ref): EA.Term.Ref =
    ref match {
      case CA.Term.GlobalRef(name, span) => EA.Term.GlobalRef(name, span)
      case CA.Term.LocalRef(ref, span)   => EA.Term.LocalRef(ref, span)
    }

  private def rejectStoredAppHeadOnlyRefs(term: EA.Term, env: Env): Unit = {
    def loop(t: EA.Term, appHead: Boolean): Unit =
      t match {
        case EA.Term.LocalRef(ref, span) =>
          if (ref.id >= 0 && ref.id < env.locals.length) {
            val binding = env.localBinding(ref)
            binding.residualPolicy match {
              case LocalResidualPolicy.AppHeadOnly(name) if !appHead =>
                throw CannotQuoteValue(binding.value, s"$name is only available as an application head", Some(span))
              case _ =>
            }
          }
        case EA.Term.GlobalRef(_, _) =>
        case EA.Term.App(fn, args, _) =>
          loop(fn, appHead = true)
          args.foreach(arg => loop(arg, appHead = false))
        case EA.Term.Pi(binders, out, _, _) =>
          binders.foreach(b => loopTypePattern(b.ty))
          loop(out, appHead = false)
        case EA.Term.Body(lets, res, _) =>
          lets.foreach { l =>
            l.ty.foreach(loop(_, appHead = false))
            loop(l.value, appHead = false)
          }
          loop(res, appHead = false)
        case EA.Term.Lam(_, _, _, _, _, _) =>
        case EA.Term.Match(scrut, motive, cases, _) =>
          loop(scrut, appHead = false)
          motive.foreach(loop(_, appHead = false))
          cases.foreach(c => loop(c.body, appHead = false))
      }

    def loopTypePattern(t: EA.TypePattern): Unit =
      t match {
        case EA.TypePattern.Type(term) => loop(term, appHead = false)
        case EA.TypePattern.App(fn, args, _) =>
          loop(fn, appHead = true)
          args.foreach(loopTypePattern)
        case EA.TypePattern.Pi(binders, out, _, _) =>
          binders.foreach(b => loopTypePattern(b.ty))
          loopTypePattern(out)
        case EA.TypePattern.Capture(_, _) =>
        case EA.TypePattern.ConstrainedCapture(_, constraint, _) =>
          loopTypePattern(constraint)
      }

    loop(term, appHead = false)
  }

  private def checkPi(pi: CA.Term.Pi, env: Env): CheckedPi = {
    val (vBinders, checkedBinders) = BinderOps.toVBinders(pi.binders, env)
    val binderEnv = BinderOps.freshen(vBinders, env)
    val checkedOut = checkTypeExpr(pi.out, binderEnv)
    val outV = checkedOut.value
    val freshArgs = vBinders.map(binder => binderEnv(binder.localRef))
    val classifier =
      if (isPropValuedType(outV)) PropTpe
      else {
        getUniverse(outV) match {
          case VSort(outLevel) =>
            val domLevels: Vector[Level] = freshArgs
              .map(v => getUniverse(v.tpe))
              .collect { case VSort(level) => level }

            VSort(Level.max(domLevels :+ outLevel))
        }
      }
    val checkedPi =
      EA.Term.Pi(checkedBinders, checkedOut.residual, classifier, pi.span)
    CheckedPi(evalPi(checkedPi, env, vBinders), binderEnv, outV, checkedPi)
  }

  private[raccoonlang] def checkTypeExpr(term: CA.Term, env: Env): CheckedTerm = {
    val checked = checkTerm(term, env)
    assertType(checked.value)
    checked
  }

  // Returning the residual term lets callers preserve checked let/lambda structure instead of re-checking.
  private def checkBody(body: CA.Term.Body, env: Env): CheckedTerm = {
    val checkedLets = Vector.newBuilder[EA.Let]
    var curEnv = env

    body.lets.foreach { l =>
      val checkedValue = checkTerm(l.value, curEnv)
      rejectStoredAppHeadOnlyRefs(checkedValue.residual, curEnv)

      var resTyTerm: Option[EA.Term] = None
      val withType = l.ty
        .map { tyTerm =>
          val checkedTy = checkTypeExpr(tyTerm, curEnv)
          val tyV = checkedTy.value
          checkType(checkedValue.value, tyV, curEnv.normalizers)
          resTyTerm = Some(checkedTy.residual)
          Value.ascribe(checkedValue.value, tyV)
        }
        .getOrElse(checkedValue.value)

      checkedLets += EA.Let(l.localRef, resTyTerm, checkedValue.residual, l.span, l.isInstance)
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.name, withType)) else None
      curEnv = curEnv.putLocal(l.localRef, withType, instanceKey)
    }

    val checkedRes = checkTerm(body.res, curEnv)
    CheckedTerm(checkedRes.value, EA.Term.Body(checkedLets.result(), checkedRes.residual, body.span))
  }

  def inductiveFamilyOf(value: Value): Option[InductiveFamilyInstance] =
    value match {
      case InductiveFamilyValue(instance) => Some(instance)
      case _                              => None
    }

  private def checkSelect(baseValue: Value, field: String, span: Span, env: Env): (String, Value) = {
    val vType = baseValue.tpe
    val family = inductiveFamilyOf(vType).getOrElse(throw NotAType(vType))
    val indName = family.head.name
    val meta = family.meta

    if (!meta.isStruct) throw NotAStruct(indName)

    val selectorName = s"$indName.$field"
    val selector = env(selectorName)
    (selectorName, checkApplyValue(selector, Vector(baseValue), env))
  }

  private def checkLam(l: CA.Term.Lam, env: Env): CheckedTerm = {
    val envWithNormalizers = l.uses.foldLeft(env) { case (curEnv, nextUse) =>
      val normalizer = checkTerm(nextUse.normalizer, curEnv).value
      normalizer match {
        case n: Value.Normalizer => curEnv.useNormalizer(n)
        case _ =>
          throw TypeMismatch(normalizer, NormalizerType)
      }
    }

    val checkedVpi = checkPi(l.ty, envWithNormalizers)
    val vpi = checkedVpi.vpi
    val bodyEnv = checkedVpi.bodyEnv

    // Recursive self references stay local for the whole pipeline, even if the source used a qualified name.
    // While checking, the local contains a raw recursive value that enforces the decrease and can only appear as an
    // application head, so the body cannot store it as an ordinary value. The checked lambda keeps the same self ref;
    // when the lambda runs, Interpreter.runLam patches that slot with the final VLam. The declaration is published to
    // globals separately after the body has checked.
    val recurEnv =
      l.recursion match {
        case Some(CA.Recursion(ref, decreaseSpec)) =>
          val name = l.name.getOrElse(throw WTF("Recursive lambda must have a name", Some(l.span)))
          val recursiveSelf = TerminationChecker.rawRecursiveSelf(name, vpi, decreaseSpec, bodyEnv, l.isStable)
          bodyEnv.putLocal(ref, recursiveSelf, residualPolicy = LocalResidualPolicy.AppHeadOnly(name))
        case None => bodyEnv
      }

    val checkedBody = l.body match {
      case b: CA.Term.Body => checkBody(b, recurEnv)
      case _               => checkTerm(l.body, recurEnv)
    }

    checkType(checkedBody.value, checkedVpi.outTy, recurEnv.normalizers)
    rejectStoredAppHeadOnlyRefs(checkedBody.residual, recurEnv)
    val checkedLam =
      EA.Term.Lam(
        checkedVpi.residual,
        checkedBody.residual,
        l.span,
        l.name,
        l.isStable,
        l.recursion.map(_.selfRef)
      )
    CheckedTerm(Interpreter.evalLam(checkedLam, vpi, env), checkedLam)
  }

  def getType(term: CA.Term, env: Env): Value = checkTypeExpr(term, env).value

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

  def checkTerm(term: CA.Term, env: Env): CheckedTerm =
    try {
      term match {
        case CA.Term.Select(base, field, span) =>
          val checkedBase = checkTerm(base, env)
          val (selectorName, value) = checkSelect(checkedBase.value, field, span, env)
          CheckedTerm(value, EA.Term.App(EA.Term.GlobalRef(selectorName, span), Vector(checkedBase.residual), span))
        case l: CA.Term.Lam => checkLam(l, env)
        case app: CA.Term.App =>
          val checkedFn = checkTerm(app.fn, env)
          val checkedArgs = app.args.map(arg => checkTerm(arg, env))
          val value = checkApplyValue(checkedFn.value, checkedArgs.map(_.value), env)
          val residual = EA.Term.App(checkedFn.residual, checkedArgs.map(_.residual), app.span)
          CheckedTerm(value, residual)
        case derive: CA.Term.Derive =>
          val goal = getType(derive.goal, env)
          val value = InstanceSearch.solve(goal, env)
          CheckedTerm(value, quoteTerm(value, quoteContext(env), derive.span))
        case pi: CA.Term.Pi =>
          val checked = checkPi(pi, env)
          CheckedTerm(checked.vpi, checked.residual)
        case m: CA.Term.Match => MatchChecker.checkMatch(m, env)
        case b: CA.Term.Body  => checkBody(b, env)
        case ref: CA.Term.Ref =>
          val residual = elabRef(ref)
          CheckedTerm(Interpreter.evalTerm(residual, env), residual)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }

}
