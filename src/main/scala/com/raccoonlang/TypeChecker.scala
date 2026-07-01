package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang.ValueQuote.{quoteContext, quoteTerm, quoteType}
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

object TypeChecker {
  private final case class CheckedPi(vpi: VPi, bodyEnv: Env, outTy: Value, residual: EA.Term.Pi)
  final case class CheckedTerm(value: Value, residual: EA.Term)
  private[raccoonlang] final case class CheckedTypeTerm(value: Value, residual: EA.TypeTerm)

  def sortLeq(a: Value, b: Value): Boolean = {
    (a, b) match {
      case (Value.VSort(u), Value.VSort(v)) => Level.leq(u, v)
      case (l1: Level, l2: Level)           => Level.leq(l1, l2)
      case (l1: Level, v: Var)              => Level.leq(l1, Level.mk(v.id))
      case (v: Var, l2: Level)              => Level.leq(Level.mk(v.id), l2)
      case _                                => false
    }
  }

  def checkFits(actual: Value, expected: Value): Unit =
    if (!ValueEquivalence.defEq(actual, expected, propIrrelevant = true) && !sortLeq(actual, expected))
      throw TypeMismatch(expected, actual)

  def checkType(value: Value, tyVal: Value): Unit =
    checkFits(value.tpe, tyVal)

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

  private def assertNonRawRecursive(v: Value): Unit = {
    v match {
      case VLam(_, id, LamBody.Native(_, _, true)) => throw InvalidRecursiveOccurrence(s"$id")
      case _                                       =>
    }
  }

  private def checkApplyValue(fn: Value, args: Vector[Value]): Value =
    fn.tpe match {
      case pi: VPi =>
        args.foreach(arg => assertNonRawRecursive(arg))
        BinderOps.checkAndInstantiate(pi.binders, pi.env, args)
        Interpreter.evalApply(fn, args)
      case _ => throw CannotApplyNonFunction(fn)
    }

  private def elabRef(ref: CA.Term.Ref): EA.Term.Ref =
    ref match {
      case CA.Term.GlobalRef(name, span) => EA.Term.GlobalRef(name, span)
      case CA.Term.LocalRef(ref, span)   => EA.Term.LocalRef(ref, span)
    }

  private def checkPi(pi: CA.Term.Pi, env: Env): CheckedPi = {
    val (vBinders, checkedBinders) = BinderOps.toVBinders(pi.binders, env)
    val binderEnv = BinderOps.freshen(vBinders, env)
    val checkedOut = checkTypeTerm(pi.out, binderEnv)
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

  private[raccoonlang] def checkTypeTerm(term: CA.TypeTerm, env: Env): CheckedTypeTerm =
    term match {
      case t: CA.Term.TApp =>
        val fn = checkTypeTerm(t.fn, env)
        val args = t.args.map(arg => checkTypeTerm(arg, env))
        val value = checkApplyValue(fn.value, args.map(_.value))
        val residual = EA.Term.App(fn.residual, args.map(_.residual), t.span)
        CheckedTypeTerm(value, residual)
      case CA.Term.TSelect(base, field, span) =>
        val checkedBase = checkTypeTerm(base, env)
        val (selectorName, value) = checkSelect(checkedBase.value, field, span, env)
        CheckedTypeTerm(value, EA.Term.App(EA.Term.GlobalRef(selectorName, span), Vector(checkedBase.residual), span))
      case derive: CA.Term.Derive =>
        val goal = getType(derive.goal, env)
        val value = InstanceSearch.solve(goal, env)
        CheckedTypeTerm(value, quoteType(value, quoteContext(env), derive.span))
      case pi: CA.Term.Pi =>
        val checked = checkPi(pi, env)
        CheckedTypeTerm(checked.vpi, checked.residual)
      case ref: CA.Term.Ref =>
        val residual = elabRef(ref)
        CheckedTypeTerm(Interpreter.evalTypeTerm(residual, env), residual)
    }

  // Returning the residual term lets callers preserve checked let/lambda structure instead of re-checking.
  private def checkBody(body: CA.Term.Body, env: Env): CheckedTerm = {
    val checkedLets = Vector.newBuilder[EA.Let]
    var curEnv = env

    body.lets.foreach { l =>
      val checkedValue = checkTerm(l.value, curEnv)

      var resTyTerm: Option[EA.TypeTerm] = None
      val withType = l.ty
        .map { tyTerm =>
          val checkedTy = checkTypeTerm(tyTerm, curEnv)
          val tyV = checkedTy.value
          checkType(checkedValue.value, tyV)
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
    (selectorName, checkApplyValue(selector, Vector(baseValue)))
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

    val checkedBody = l.body match {
      case b: CA.Term.Body => checkBody(b, recurEnv)
      case _               => checkTerm(l.body, recurEnv)
    }
    assertNonRawRecursive(checkedBody.value)

    checkType(checkedBody.value, checkedVpi.outTy)
    val checkedLam =
      EA.Term.Lam(
        checkedVpi.residual,
        checkedBody.residual,
        l.span,
        l.name,
        l.recursion.map(_.selfRef)
      )
    CheckedTerm(Interpreter.evalLam(checkedLam, vpi, env), checkedLam)
  }

  def getType(term: CA.TypeTerm, env: Env): Value = {
    val res = checkTypeTerm(term, env).value
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
          val value = checkApplyValue(checkedFn.value, checkedArgs.map(_.value))
          val residual = EA.Term.App(checkedFn.residual, checkedArgs.map(_.residual), app.span)
          CheckedTerm(value, residual)
        case derive: CA.Term.Derive =>
          val goal = getType(derive.goal, env)
          val value = InstanceSearch.solve(goal, env)
          CheckedTerm(value, quoteTerm(value, quoteContext(env), derive.span))
        case m: CA.Term.Match => MatchChecker.checkMatch(m, env)
        case b: CA.Term.Body  => checkBody(b, env)
        case term: CA.TypeTerm =>
          val checked = checkTypeTerm(term, env)
          CheckedTerm(checked.value, checked.residual)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }

}
