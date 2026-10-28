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

  def checkFits(actual: Value, expected: Value): Unit = {
    if (actual == PropTpe && expected.isInstanceOf[VSort])
      throw PropositionAsTypeCarrier()
    if (!ValueEquivalence.defEq(actual, expected) && !sortLeq(actual, expected))
      throw TypeMismatch(expected, actual)
  }

  def checkType(value: Value, tyVal: Value): Unit =
    checkFits(value.tpe, tyVal)

  def getUniverse(value: Value): Universe = {
    value.tpe match {
      case u: Universe => u
      case _           => throw NotAType(value.tpe)
    }
  }

  private def checkApplyValue(fn: Value, args: Vector[Value]): Value =
    fn.tpe match {
      case pi: VPi =>
        BinderOps.checkAndInstantiate(pi.binders, pi.env, args)
        Interpreter.evalApply(fn, args)
      case _ => throw CannotApplyNonFunction(fn)
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
        case EA.Term.NatLit(_, _)    =>
        case EA.Term.StrLit(_, _)    =>
        case EA.Term.Word(_, pieces, _) =>
          pieces.foreach {
            case EA.Term.WordPiece.Layer(before, after) => (before ++ after).foreach(loop(_, appHead = false))
            case EA.Term.WordPiece.Splice(list)         => loop(list, appHead = false)
          }
        case EA.Term.App(fn, args, _) =>
          loop(fn, appHead = true)
          args.foreach(arg => loop(arg, appHead = false))
        case EA.Term.Pi(binders, out, _, _, _) =>
          binders.foreach(b => loopBinderType(b.ty))
          loop(out, appHead = false)
        case EA.Term.Body(lets, res, _) =>
          lets.foreach { l =>
            l.ty.foreach(loop(_, appHead = false))
            loop(l.value, appHead = false)
          }
          loop(res, appHead = false)
        case EA.Term.Lam(_, _, _, _, _, _) =>
        case EA.Term.Match(scrut, motive, cases, _, _) =>
          loop(scrut, appHead = false)
          motive.foreach(loop(_, appHead = false))
          cases.foreach(c => loop(c.body, appHead = false))
      }

    def loopBinderType(t: EA.BinderType): Unit =
      t match {
        case EA.BinderType.TypePattern(tp, _)                   => loopTypePattern(tp)
        case EA.BinderType.ConstrainedCapture(_, constraint, _) => loopTypePattern(constraint)
      }

    def loopTypePattern(t: EA.TypePattern): Unit =
      t match {
        case EA.TypePattern.Type(term) => loop(term, appHead = false)
        case EA.TypePattern.App(fn, args, _) =>
          loop(fn, appHead = true)
          args.foreach(loopTypePattern)
        case EA.TypePattern.Capture(_, _) =>
      }

    loop(term, appHead = false)
  }

  private def checkPi(pi: CA.Term.Pi, env: Env): CheckedPi = {
    val (vBinders, checkedBinders) = BinderOps.toVBinders(pi.binders, env)
    val binderEnv = BinderOps.freshen(vBinders, env)
    val checkedOut = checkTypeTerm(pi.out, binderEnv)
    val outV = checkedOut.value
    val freshArgs = vBinders.map(binder => binderEnv(binder.localRef))
    val classifier =
      getUniverse(outV) match {
        case PropTpe => PropTpe
        case VSort(outLevel) =>
          val domLevels: Vector[Level] = freshArgs
            .map(v => getUniverse(v.tpe))
            .collect { case VSort(level) => level }

          VSort(Level.max(domLevels :+ outLevel))
      }

    val checkedPi =
      EA.Term.Pi(checkedBinders, checkedOut.residual, classifier, pi.span, pi.nodeId)
    CheckedPi(evalPi(checkedPi, env, vBinders), binderEnv, outV, checkedPi)
  }

  private[raccoonlang] def checkTypeTerm(term: CA.TypeTerm, env: Env): CheckedTypeTerm =
    term match {
      case app: CA.Term.App =>
        val fn = checkTerm(app.fn, env)
        val args = app.args.map(arg => checkTerm(arg, env))
        val value = checkApplyValue(fn.value, args.map(_.value))
        val residual = EA.Term.App(fn.residual, args.map(_.residual), app.span)
        CheckedTypeTerm(value, residual)
      case CA.Term.Select(base, field, span) =>
        val checkedBase = checkTerm(base, env)
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
      case CA.Term.StrLit(text, span) =>
        // A literal's type is kernel String whatever is expected.
        val residual = EA.Term.StrLit(text, span)
        CheckedTypeTerm(residual.value, residual)
    }

  // Returning the residual term lets callers preserve checked let/lambda structure instead of re-checking.
  private def checkBody(
      body: CA.Term.Body,
      env: Env,
      expected: Option[CheckedTypeTerm] = None
  ): CheckedTerm = {
    val checkedLets = Vector.newBuilder[EA.Let]
    var curEnv = env

    body.lets.foreach { l =>
      val checkedAnnotation = l.ty.map(checkTypeTerm(_, curEnv))
      checkedAnnotation.foreach(checked => assertType(checked.value))
      val checkedValue = checkedAnnotation match {
        case Some(annotation) => checkTermAgainst(l.value, curEnv, annotation)
        case None             => checkTerm(l.value, curEnv)
      }
      rejectStoredAppHeadOnlyRefs(checkedValue.residual, curEnv)

      val resTyTerm = checkedAnnotation.map(_.residual)
      val withType = checkedValue.value

      checkedLets += EA.Let(l.localRef, resTyTerm, checkedValue.residual, l.span, l.isInstance)
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.name, withType)) else None
      curEnv = curEnv.putLocal(l.localRef, withType, instanceKey)
    }

    val checkedRes = expected match {
      case Some(motive) => checkTermAgainst(body.res, curEnv, motive)
      case None         => checkTerm(body.res, curEnv)
    }
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
    // when the lambda runs, Interpreter.runLam patches that slot with the final VLam. The declaration is published to
    // globals separately after the body has checked.
    val recurEnv =
      l.recursion match {
        case Some(CA.Recursion(ref, decreaseSpec)) =>
          val name = l.name.getOrElse(throw WTF("Recursive lambda must have a name", Some(l.span)))
          val recursiveSelf = TerminationChecker.rawRecursiveSelf(name, vpi, decreaseSpec, bodyEnv)
          bodyEnv.putLocal(ref, recursiveSelf, residualPolicy = LocalResidualPolicy.AppHeadOnly(name))
        case None => bodyEnv
      }

    val checkedBody = checkTermAgainst(
      l.body,
      recurEnv,
      CheckedTypeTerm(checkedVpi.outTy, checkedVpi.residual.out)
    )
    rejectStoredAppHeadOnlyRefs(checkedBody.residual, recurEnv)
    val checkedLam =
      EA.Term.Lam(
        checkedVpi.residual,
        checkedBody.residual,
        l.span,
        l.name,
        l.recursion.map(_.selfRef),
        l.nodeId
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
        case l: CA.Term.Lam => checkLam(l, env)
        case derive: CA.Term.Derive =>
          val goal = getType(derive.goal, env)
          val value = InstanceSearch.solve(goal, env)
          CheckedTerm(value, quoteTerm(value, quoteContext(env), derive.span))
        case m: CA.Term.MatchTerm => MatchChecker.checkMatch(m, env)
        case b: CA.Term.Body      => checkBody(b, env)
        case term: CA.TypeTerm =>
          val checked = checkTypeTerm(term, env)
          CheckedTerm(checked.value, checked.residual)
      }
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }

  private[raccoonlang] def checkTermAgainst(
      term: CA.Term,
      env: Env,
      expected: CheckedTypeTerm
  ): CheckedTerm =
    try {
      val checked = term match {
        case body: CA.Term.Body           => checkBody(body, env, Some(expected))
        case matchTerm: CA.Term.MatchTerm => MatchChecker.checkMatch(matchTerm, env, Some(expected))
        case _                            => checkTerm(term, env)
      }
      checkType(checked.value, expected.value)
      checked
    } catch {
      case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, term.span)
    }

}
