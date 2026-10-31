package com.raccoonlang

import com.raccoonlang.Interpreter._
import com.raccoonlang.Value._
import com.raccoonlang.ValueQuote.{quoteContext, quoteTerm, quoteType}
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.Ledger.{Input, LinearInfo}
import com.raccoonlang.{CoreAst => CA, ElabAst => EA}

import scala.collection.immutable.BitSet

object TypeChecker {
  private final case class CheckedPi(vpi: VPi, bodyEnv: Env, outTy: Value, residual: EA.Term.Pi)

  /**
   * A checked term: its value, its residual, and what it does with tracked locals (`Ledger.LinearInfo`), which the
   * ledger and the read rules combine bottom-up. A type or a proof is a read extent: its info keeps nothing.
   */
  final case class CheckedTerm(value: Value, residual: EA.Term, lin: LinearInfo)

  /** A checked type term, with `lin` as for `CheckedTerm`. */
  private[raccoonlang] final case class CheckedTypeTerm(value: Value, residual: EA.TypeTerm, lin: LinearInfo)

  /**
   * The level a type in universe `u` contributes to a function type's classifier (F1) or to a family argument's size:
   * `v` for `Univ(k, v)` of any kind, and nothing, so zero, for a proposition. Kinds cost nothing.
   */
  def classifierLevel(u: Universe): Level =
    u match {
      case PropTpe         => Level.zero
      case VUniv(_, level) => level
    }

  /**
   * A term checked as a read extent of its own, though its value need not be a type or a proof, such as a `measure`:
   * its violations of the read rules are reported here.
   */
  private[raccoonlang] def readBoundary(lin: LinearInfo): Unit = lin.pending.foreach(error => throw error)

  /**
   * Runs `body`, locating at `span` a type error it raises without a location: the innermost checked node that carries
   * a span gives every error its place.
   */
  private[raccoonlang] def at[A](span: Span)(body: => A): A =
    try body
    catch { case e: TypeError if e.span.isEmpty => throw TypeError.withSpan(e, span) }

  /**
   * A term's whole source span. An application's or a projection's own span covers only its trailer, the argument list
   * or `.field`, so errors that name a whole term, such as a linear subterm, extend it back over the head.
   */
  def sourceSpan(term: CA.Term): Span =
    term match {
      case CA.Term.App(fn, _, span)      => Span(sourceSpan(fn).start, span.end, span.source)
      case CA.Term.Select(base, _, span) => Span(sourceSpan(base).start, span.end, span.source)
      case other                         => other.span
    }

  /**
   * An environment that has consumed what `lin` uses, for the terms checked after it on the same path: the roots of the
   * tracked locals it uses.
   */
  private[raccoonlang] def after(env: Env, lin: LinearInfo): Env =
    if (lin.uses.locals.isEmpty) env
    else {
      val roots = lin.uses.consumed.iterator.flatMap(id => env.localBinding(CA.LocalRef(id, "")).provenance.roots)
      env.withDeadLocals(BitSet.fromSpecific(roots))
    }

  def checkFits(actual: Value, expected: Value): Unit = {
    if (actual == PropTpe && expected.isInstanceOf[VUniv]) throw PropositionAsTypeCarrier()
    if (!ValueEquivalence.defEq(actual, expected)) throw TypeMismatch(expected, actual)
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
        case EA.Term.Proj(base, _, _, _, _) => loop(base, appHead = false)
        case EA.Term.Pi(binders, out, _, _, _) =>
          binders.foreach(b => loopBinderType(b.ty))
          loop(out, appHead = false)
        case EA.Term.Body(lets, res, _) =>
          lets.foreach { l =>
            l.ty.foreach(loop(_, appHead = false))
            loop(l.value, appHead = false)
          }
          loop(res, appHead = false)
        case _: EA.Term.Lam =>
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
        case EA.TypePattern.Capture(_, _, constraint) => constraint.foreach(loopTypePattern)
      }

    loop(term, appHead = false)
  }

  /**
   * A function type's classifier: `Prop` when its codomain is a proposition, whatever its domains (F2), and otherwise
   * `Sort` of the maximum of its domains' and codomain's levels, `Lin` ones included (F1). Every function value is
   * unrestricted. The codomain and later binder types are read extents, so they may read linear binders (F3).
   *
   * When the codomain's level depends on a `Level` or `Kind` binder, as in `(u: Level) -> Sort(u)`, the classifier
   * level mentions that binder's fresh variable, which is out of scope above the `VPi`. Such a classifier is sound but
   * inert: the dangling variable converts with no concrete level, so the type is never a value of a universe (passing
   * it where a `Sort(l)` is expected is `TypeMismatch`), only the declared type of a global, which needs no universe
   * membership. It therefore cannot be fixed to a level and smuggled into `Type`, so it gives no Girard paradox; see
   * KindsAttackTests "lvl-*".
   */
  private def checkPi(pi: CA.Term.Pi, env: Env): CheckedPi = {
    val (vBinders, checkedBinders) = BinderOps.toVBinders(pi.binders, env)
    val binderEnv = BinderOps.freshen(vBinders, env)
    val checkedOut = checkTypeTerm(pi.out, binderEnv)
    val outV = checkedOut.value
    val domainUniverses = vBinders.map(binder => getUniverse(binderEnv(binder.localRef).tpe))
    val classifier =
      getUniverse(outV) match {
        case PropTpe => PropTpe
        // F1: a function type is copyable, whatever the kinds of its domains and codomain.
        case out: VUniv =>
          VSort(Level.max(domainUniverses.map(classifierLevel) :+ classifierLevel(out)))
      }

    val checkedPi =
      EA.Term.Pi(checkedBinders, checkedOut.residual, classifier, pi.span, pi.nodeId)
    CheckedPi(evalPi(checkedPi, env, vBinders), binderEnv, outV, checkedPi)
  }

  private[raccoonlang] def checkTypeTerm(term: CA.TypeTerm, env: Env): CheckedTypeTerm =
    at(term.span)(checkTypeTermHere(term, env))

  private def checkTypeTermHere(term: CA.TypeTerm, env: Env): CheckedTypeTerm =
    term match {
      case app: CA.Term.App =>
        fieldSelector(app.fn, env) match {
          case Some(selector) => checkFieldCall(app, selector, env)
          case None           => checkApplication(app, env)
        }
      case select: CA.Term.Select => checkSelect(select, env)
      case derive: CA.Term.Derive =>
        val goal = getType(derive.goal, env)
        val value = InstanceSearch.solve(goal, env)
        // Quotation refuses a linear value and names no tracked local, so the result reads and uses nothing.
        CheckedTypeTerm(value, quoteType(value, quoteContext(env), derive.span), LinearInfo.empty)
      case pi: CA.Term.Pi =>
        val checked = checkPi(pi, env)
        CheckedTypeTerm(checked.vpi, checked.residual, LinearInfo.empty)
      // A lambda inside a type, such as a predicate argument: a function value, which uses nothing (F5).
      case l: CA.Term.Lam => checkLam(l, env)
      case ref: CA.Term.Ref =>
        val residual = elabRef(ref)
        val value = Interpreter.evalTypeTerm(residual, env)
        // A tracked local is a use with its binding's provenance; a global holds no tracked local.
        val lin = residual match {
          case EA.Term.LocalRef(local, _) =>
            val binding = env.localBinding(local)
            if (binding.linear) LinearInfo.tracked(local.id, ref.span, binding.provenance).at(value)
            else LinearInfo.empty
          case _: EA.Term.GlobalRef => LinearInfo.empty
        }
        CheckedTypeTerm(value, residual, lin)
      case CA.Term.NatLit(number, span) =>
        // A literal's type is kernel Nat whatever is expected.
        val residual = EA.Term.NatLit(number, span)
        CheckedTypeTerm(residual.value, residual, LinearInfo.empty)
      case CA.Term.StrLit(text, span) =>
        // A literal's type is kernel String whatever is expected.
        val residual = EA.Term.StrLit(text, span)
        CheckedTypeTerm(residual.value, residual, LinearInfo.empty)
    }

  /**
   * Returning the residual term lets callers preserve checked let/lambda structure instead of re-checking. A let of
   * linear type is tracked: it is used at most once in the later lets and the result (the ledger), or only read when
   * the block is a read extent, and is no instance (L7). A let aliases its value's provenance, so a block's provenance
   * is its result's.
   */
  private def checkBody(
      body: CA.Term.Body,
      env: Env,
      expected: Option[CheckedTypeTerm] = None
  ): CheckedTerm = {
    val checkedLets = Vector.newBuilder[EA.Let]
    val letInfos = Vector.newBuilder[LinearInfo]
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
      val linear = Linearity.isLinear(withType.tpe)
      if (linear && l.isInstance) throw LinearInstance(l.name, Some(l.span))

      checkedLets += EA.Let(l.localRef, resTyTerm, checkedValue.residual, l.span, l.isInstance)
      letInfos += checkedValue.lin
      val instanceKey = if (l.isInstance) Some(InstanceSearch.instanceKey(l.name, withType)) else None
      curEnv = after(curEnv, checkedValue.lin)
        .putLocal(l.localRef, withType, instanceKey, linear = linear, alias = Some(checkedValue.lin.provenance))
    }

    val checkedRes = expected match {
      case Some(motive) => checkTermAgainst(body.res, curEnv, motive)
      case None         => checkTerm(body.res, curEnv)
    }
    val lets = checkedLets.result()
    val infos = letInfos.result()
    val value = checkedRes.value
    val read = Linearity.role(value) == Linearity.Role.TypeOrProof
    val parts = infos :+ checkedRes.lin
    val sequenced = parts.foldLeft(Ledger.Summary.empty)((sum, part) => sum.andThen(part.uses))
    // Only tracked lets have uses, so binding the others changes nothing.
    val uses = lets.foldLeft(sequenced)((sum, let) => Ledger.bind(let.localRef, sum, read))
    val pending = parts.iterator.flatMap(_.pending).nextOption()
    CheckedTerm(
      value,
      EA.Term.Body(lets, checkedRes.residual, body.span),
      LinearInfo(uses, checkedRes.lin.provenance, pending).at(value)
    )
  }

  /**
   * An application whose head is not a field selector. Each argument sees what the head and the earlier arguments
   * consumed, for the bindings it makes; a read among them still reads the locals live at the start of the application,
   * by joint liveness.
   */
  private def checkApplication(app: CA.Term.App, env: Env): CheckedTypeTerm = {
    val fn = checkTerm(app.fn, env)
    var argEnv = after(env, fn.lin)
    val args = app.args.map { arg =>
      val checked = checkTerm(arg, argEnv)
      argEnv = after(argEnv, checked.lin)
      checked
    }
    val value = checkApplyValue(fn.value, args.map(_.value))
    val residual = EA.Term.App(fn.residual, args.map(_.residual), app.span)
    val inputs = Input(fn.lin, sourceSpan(app.fn)) +: app.args.zip(args).map { case (arg, checked) =>
      Input(checked.lin, sourceSpan(arg))
    }
    CheckedTypeTerm(value, residual, Ledger.call(value, inputs, sourceSpan(app), env))
  }

  def inductiveFamilyOf(value: Value): Option[InductiveFamilyInstance] =
    value match {
      case InductiveFamilyValue(instance) => Some(instance)
      case _                              => None
    }

  /** The field `index` of the record `info` of the family whose head is `family`, written `Fam.field`. */
  private final case class FieldSelector(family: VConst, info: RecordInfo, index: Int)

  /** `field` of `head` when it is a record family's head with that field. */
  private def recordField(head: Value, field: String): Option[FieldSelector] =
    head match {
      case family @ VConst(_, Inductive(meta), _) =>
        meta.record.flatMap(info => info.fieldIndex(field).map(FieldSelector(family, info, _)))
      case _ => None
    }

  /**
   * The field `fn` names when it is `Fam.field` for a field of the record `Fam`, as the elaborator resolves a field of
   * a record's namespace (`Elaborator.NameNode`): the selection of the field from the family's global.
   */
  private def fieldSelector(fn: CA.Term, env: Env): Option[FieldSelector] =
    fn match {
      case CA.Term.Select(CA.Term.GlobalRef(name, _), field, _) => recordField(env(name), field)
      case _                                                    => None
    }

  /**
   * `Fam.field(r)`, sugar for `r.field` that also requires `r` to be of the family `Fam`. A field is no function value,
   * so it takes exactly the record.
   */
  private def checkFieldCall(app: CA.Term.App, selector: FieldSelector, env: Env): CheckedTypeTerm = {
    if (app.args.length != 1) throw ArityMismatch(1, app.args.length, Some(app.span))
    val record = app.args.head
    val checked = checkTerm(record, env)
    val family = inductiveFamilyOf(checked.value.tpe).filter(_.head.name == selector.family.name).getOrElse {
      throw TypeMismatch(selector.family, checked.value.tpe, Some(sourceSpan(record)))
    }
    checkProjection(checked, family, selector.info, selector.index, app.span, env)
  }

  /** `base.field`: the projection of that field, when the family of `base` 's type is a record that has one. */
  private def checkSelect(select: CA.Term.Select, env: Env): CheckedTypeTerm = {
    val checked = checkTerm(select.base, env)
    val projected = for {
      family <- inductiveFamilyOf(checked.value.tpe)
      info <- family.meta.record
      index <- info.fieldIndex(select.field)
    } yield checkProjection(checked, family, info, index, select.span, env)
    projected.getOrElse(throw noField(select, checked.value))
  }

  /**
   * Field `index` of the record `info` of `family`, the type of the value `checked` checked to, at `span`
   * (docs/kernel.md, "Structure eta and projections"): the one-branch match that returns the field, as a node of its
   * own (`EA.Term.Proj`). Its type is the field's at the value, which the family's arguments must determine unless the
   * value is constructor-headed (`InvalidStruct`), and projecting out of a proof is checked as that match's elimination
   * would be (`MatchChecker.checkProjectionElimination`). In the ledger it is that match too (`Ledger.project`).
   */
  private def checkProjection(
      checked: CheckedTerm,
      family: InductiveFamilyInstance,
      info: RecordInfo,
      index: Int,
      span: Span,
      env: Env
  ): CheckedTypeTerm = {
    val base = checked.value
    val field = info.fieldNames(index)
    val value = StructEta.project(base, index)
    if (StructEta.undetermined(info, value.tpe))
      throw InvalidStruct(
        family.head.name,
        s"the type ${value.tpe} of its field $field depends on a capture that ${base.tpe} does not determine",
        Some(span)
      )
    MatchChecker.checkProjectionElimination(base, family, info, index, env, span)
    CheckedTypeTerm(
      value,
      EA.Term.Proj(checked.residual, family.head.name, field, index, span),
      Ledger.project(checked.lin, index, value)
    )
  }

  /**
   * `base.field` where `base` 's type has no such field. `Fam.field` unapplied, for a field of the record `Fam`, is no
   * function value (`UnappliedField`). Otherwise it is `NotFound`: a base that is a type former, a family or an opaque
   * type such as `Protocol.Tok` in `Protocol.Tok.mk`, has no constructor of that name, since a constructor would have
   * resolved as the family's member; anything else has no field of that name.
   */
  private def noField(select: CA.Term.Select, baseValue: Value): TypeError = {
    def typeFormer(tpe: Value): Boolean =
      tpe match {
        case _: Universe => true
        case pi: VPi     => typeFormer(pi.codomain(BinderOps.freshen(pi)))
        case _           => false
      }
    val field = select.field
    recordField(baseValue, field) match {
      case Some(selector) => UnappliedField(selector.family.name, field)
      case None =>
        baseValue match {
          case VConst(name, Inductive(_) | Symbol, tpe) if typeFormer(tpe) =>
            NotFound(s"$name.$field", reason = Some(s"$name has no constructor $field"))
          case _ =>
            val text = PrettyPrinter.printTerm(select.base)
            val fields =
              if (inductiveFamilyOf(baseValue.tpe).isEmpty) "is no family, so has no fields" else s"has no field $field"
            NotFound(s"$text.$field", reason = Some(s"$text is of type ${baseValue.tpe}, which $fields"))
        }
    }
  }

  private def checkLam(l: CA.Term.Lam, env: Env): CheckedTypeTerm = {
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

    val checkedLam = checkLamBody(l, checkedVpi, recurEnv, Vector.empty)
    val capturedIndexes = CapturedIndexes.getCapturedIndexes(checkedLam, env)
    rejectLinearCaptures(checkedLam, capturedIndexes, env)
    val value = Interpreter.evalLam(checkedLam, vpi, env, capturedIndexes)
    // A function value uses nothing of its context (F5), and its body is its own extent, whose violations the ledger
    // has reported.
    CheckedTypeTerm(value, checkedLam, LinearInfo.empty)
  }

  /**
   * The members of a mutual block of definitions (docs/kernel.md, "Mutual blocks"), checked in `env`, which holds none
   * of them: each one's type, then each body with every member bound at its peer slots to the raw call from it to that
   * member, which checks that the call decreases from its own metric (`TerminationChecker.rawRecursiveCall`). Returns
   * each member's checked lambda and type; `Interpreter` publishes them together.
   */
  private[raccoonlang] def checkMutualDefs(members: Vector[CA.MutualDef], env: Env): Vector[(EA.Term.Lam, VPi)] = {
    val headers = members.map { member =>
      val checkedVpi = checkPi(member.lam.ty, env)
      (member, checkedVpi, TerminationChecker.metric(member.name, checkedVpi.vpi, member.decreases, checkedVpi.bodyEnv))
    }
    TerminationChecker.requireCompatible(headers.map(_._3))
    val names = members.map(_.name)
    headers.map { case (member, checkedVpi, callerMetric) =>
      val recurEnv =
        member.peers.zip(headers).foldLeft(checkedVpi.bodyEnv) { case (current, (ref, (callee, _, calleeMetric))) =>
          val raw = TerminationChecker.rawRecursiveCall(calleeMetric, callerMetric, checkedVpi.bodyEnv)
          current.putLocal(ref, raw, residualPolicy = LocalResidualPolicy.AppHeadOnly(callee.name))
        }
      (checkLamBody(member.lam, checkedVpi, recurEnv, member.peers.zip(names)), checkedVpi.vpi)
    }
  }

  /**
   * A lambda's body, checked in `recurEnv`, its parameters' environment with its recursive slots bound, and the checked
   * lambda, whose `recursivePeers` are given for a member of a mutual block.
   */
  private def checkLamBody(
      l: CA.Term.Lam,
      checkedVpi: CheckedPi,
      recurEnv: Env,
      recursivePeers: Vector[(CA.LocalRef, String)]
  ): EA.Term.Lam = {
    val checkedBody = checkTermAgainst(
      l.body,
      recurEnv,
      CheckedTypeTerm(checkedVpi.outTy, checkedVpi.residual.out, LinearInfo.empty)
    )
    rejectStoredAppHeadOnlyRefs(checkedBody.residual, recurEnv)
    // F4: a parameter of linear type, tracked from its binder's type, is used at most once in the body, or only read
    // when the body is a read extent, as for a function returning a proposition (F2). Its later binder types and the
    // codomain may read it (F3); the ledger does not count reads.
    val bodyIsRead = Linearity.role(checkedBody.value) == Linearity.Role.TypeOrProof
    checkedVpi.residual.binders.foreach(binder => Ledger.bind(binder.localRef, checkedBody.lin.uses, bodyIsRead))
    EA.Term.Lam(
      checkedVpi.residual,
      checkedBody.residual,
      l.span,
      l.name,
      l.recursion.map(_.selfRef),
      l.nodeId,
      recursivePeers
    )
  }

  /**
   * F5: a lambda, every function value being unrestricted, captures no linear local of `env`, its outer environment, in
   * its body or its type, read or not. A read in either would run when the function is applied, where nothing ties the
   * captured local's liveness to the arguments'. It reads only the captured bindings, which `evalLam` reads too.
   */
  private def rejectLinearCaptures(
      lam: EA.Term.Lam,
      capturedIndexes: org.roaringbitmap.RoaringBitmap,
      env: Env
  ): Unit = {
    val it = capturedIndexes.getIntIterator
    while (it.hasNext) {
      val binding = env.localBinding(CA.LocalRef(it.next(), ""))
      if (binding.linear)
        throw LinearCapture(binding.name, Some(Ledger.firstReference(binding.id, lam).getOrElse(lam.span)))
    }
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
          case _: VUniv | PropTpe =>
          case _                  => throw NotAType(value)
        }
    }
  }

  def checkTerm(term: CA.Term, env: Env): CheckedTerm =
    at(term.span) {
      term match {
        case derive: CA.Term.Derive =>
          val goal = getType(derive.goal, env)
          val value = InstanceSearch.solve(goal, env)
          // Quotation refuses a linear value and names no tracked local, so the result reads and uses nothing.
          CheckedTerm(value, quoteTerm(value, quoteContext(env), derive.span), LinearInfo.empty)
        case m: CA.Term.MatchTerm => MatchChecker.checkMatch(m, env)
        case b: CA.Term.Body      => checkBody(b, env)
        case term: CA.TypeTerm =>
          val checked = checkTypeTerm(term, env)
          CheckedTerm(checked.value, checked.residual, checked.lin)
      }
    }

  private[raccoonlang] def checkTermAgainst(
      term: CA.Term,
      env: Env,
      expected: CheckedTypeTerm
  ): CheckedTerm =
    at(term.span) {
      val checked = term match {
        case body: CA.Term.Body           => checkBody(body, env, Some(expected))
        case matchTerm: CA.Term.MatchTerm => MatchChecker.checkMatch(matchTerm, env, Some(expected))
        case _                            => checkTerm(term, env)
      }
      checkType(checked.value, expected.value)
      checked
    }

}
