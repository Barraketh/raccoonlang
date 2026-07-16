package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

object ValueQuote {
  type QuoteMap = Map[ValueKey.Key, ElabAst.Term]
  final case class QuoteContext(quote: QuoteMap)

  private final case class OpenedPi(
      term: ElabAst.Term.Pi,
      freshArgs: Vector[Value],
      context: QuoteContext
  )

  private final class ClosedEnvInliner(env: Env, context: QuoteContext) {
    private def inlineLocal(ref: CoreAst.LocalRef, refSpan: Span): ElabAst.Term =
      if (env.locals.contains(ref)) quoteTerm(env(ref), context, refSpan)
      else ElabAst.Term.LocalRef(ref, refSpan)

    private def inlineAppHead(t: ElabAst.Term): ElabAst.Term =
      t match {
        case ElabAst.Term.LocalRef(ref, refSpan) =>
          if (env.locals.contains(ref)) quoteAppHead(env(ref), context, refSpan)
          else ElabAst.Term.LocalRef(ref, refSpan)
        case other => inlineTerm(other)
      }

    def inlineTerm(t: ElabAst.Term): ElabAst.Term =
      t match {
        case _: ElabAst.Term.NatLit              => t
        case ElabAst.Term.Proof(tpe, proofSpan)  => ElabAst.Term.Proof(inlineTerm(tpe), proofSpan)
        case ElabAst.Term.GlobalRef(_, _)        => t
        case ElabAst.Term.LocalRef(ref, refSpan) => inlineLocal(ref, refSpan)
        case ElabAst.Term.App(fn, args, appSpan) =>
          ElabAst.Term.App(inlineAppHead(fn), args.map(inlineTerm), appSpan)
        case pi: ElabAst.Term.Pi => inlinePi(pi)
        case ElabAst.Term.Body(lets, res, bodySpan) =>
          val nextLets = lets.map { l =>
            ElabAst.Let(l.localRef, l.ty.map(inlineTerm), inlineTerm(l.value), l.span)
          }
          ElabAst.Term.Body(nextLets, inlineTerm(res), bodySpan)
        case ElabAst.Term.Lam(ty, body, lamSpan, name, recursiveSelf, lamNodeId) =>
          ElabAst.Term.Lam(
            inlinePi(ty),
            inlineTerm(body),
            lamSpan,
            name,
            recursiveSelf,
            lamNodeId
          )
        case ElabAst.Term.Match(scrut, motive, cases, matchSpan, matchNodeId) =>
          ElabAst.Term.Match(
            inlineTerm(scrut),
            motive.map(inlineTerm),
            cases.map(inlineCase),
            matchSpan,
            matchNodeId
          )
      }

    def inlinePi(pi: ElabAst.Term.Pi): ElabAst.Term.Pi = {
      val nextBinders = pi.binders.map { b =>
        b.copy(ty = inlineTerm(b.ty))
      }
      ElabAst.Term.Pi(nextBinders, inlineTerm(pi.out), pi.span, pi.nodeId)
    }

    def inlineCase(c: ElabAst.Case): ElabAst.Case =
      ElabAst.Case(c.ctorName, c.argRefs, inlineTerm(c.body), c.span)
  }

  def quoteContext(env: Env): QuoteContext = {
    val quote = env.locals.foldLeft(Map.empty[ValueKey.Key, ElabAst.Term]) { case (quote, (ref, value)) =>
      withLocalQuote(quote, ref, value)
    }
    QuoteContext(quote)
  }

  def quotePi(pi: VPi, context: QuoteContext, span: Span): ElabAst.Term.Pi =
    quotePiOpened(pi, context, span).term

  def quoteTerm(value: Value, context: QuoteContext, span: Span): ElabAst.Term = {
    // Erased proofs have a canonical residual independent of the local quote map. In particular,
    // a proof hypothesis quotes as `proof(P)`, never by recovering a discarded witness or by
    // choosing an arbitrary proof-irrelevant local representative.
    value match {
      case p: VProof => return ElabAst.Term.Proof(quoteTerm(p.tpe, context, span), span)
      case _         =>
    }

    context.quote.get(value.key).foreach(return _)

    value match {
      case lam: VLam if isRawRecursive(lam) => throw CannotQuoteValue(lam, "raw recursive self", Some(span))
      case _                                =>
    }

    value match {
      case v: Var => throw CannotQuoteValue(v, "escaping variable", Some(span))

      case VSort(level) =>
        if (level == Level.zero) ElabAst.Term.GlobalRef("Prop", span)
        else if (level == Level.one) ElabAst.Term.GlobalRef("Type", span)
        else ElabAst.Term.App(ElabAst.Term.GlobalRef("Sort", span), Vector(quoteLevel(level, context, span)), span)

      case LevelTpe => ElabAst.Term.GlobalRef("Level", span)

      case VConst(name, _, _) => ElabAst.Term.GlobalRef(name, span)

      case p: VPacked =>
        p.codec match {
          case NatCodec => ElabAst.Term.NatLit(p.payload, span)
        }

      case VCtor(head, fields, tpe) => quoteCtor(head, fields, tpe, context, span)

      case VApp(head, args, _, _) =>
        val fn = quoteAppHead(head, context, span)
        val explicit = explicitArgs(head.tpe, args)
        ElabAst.Term.App(fn, explicit.map(arg => quoteTerm(arg, context, span)), span)

      case NeutralThunk(term, env, _, _, _) => quoteClosedMatch(term, env, context, span)

      case lam: VLam => quoteLam(lam, context, span)

      case pi: VPi => quotePiOpened(pi, context, span).term

      case head: ConstructorHead => ElabAst.Term.GlobalRef(head.name, span)

      case level: Level => quoteLevel(level, context, span)

      case other => throw CannotQuoteValue(other, "no quoted syntax", Some(span))
    }
  }

  private def quoteAppHead(value: Value, context: QuoteContext, span: Span): ElabAst.Term =
    context.quote.get(value.key).getOrElse(quoteTerm(value, context, span))

  /**
   * Residual applications carry only the explicit args — the same arity convention as source-checked syntax — so
   * evaluation has a single rule: implicit args are always reconstructed by projection
   * (Interpreter.reconstructImplicits).
   */
  private def explicitArgs(headTpe: Value, args: Vector[Value]): Vector[Value] =
    headTpe match {
      case pi: VPi if pi.binders.length == args.length && pi.binders.exists(_.isImplicit) =>
        pi.binders.zip(args).collect { case (binder, arg) if !binder.isImplicit => arg }
      case _ => args
    }

  private def quoteClosedMatch(
      term: ElabAst.Term.Match,
      env: Env,
      context: QuoteContext,
      span: Span
  ): ElabAst.Term.Match = {
    val inliner = new ClosedEnvInliner(env, context)

    ElabAst.Term.Match(
      quoteTerm(Interpreter.evalTerm(term.scrut, env), context, term.scrut.span),
      term.motive.map(motive => quoteTerm(Interpreter.evalTerm(motive, env), context, motive.span)),
      term.cases.map(inliner.inlineCase),
      span,
      AstNodeId.synthetic()
    )
  }

  private def quoteCtor(
      head: ConstructorHead,
      fields: Vector[Value],
      tpe: Value,
      context: QuoteContext,
      span: Span
  ): ElabAst.Term = {
    val args = recoverConstructorArgs(head, fields, tpe, span)

    if (args.length != head.totalArity)
      throw WTF(s"Constructor ${head.name} has ${args.length} args, expected ${head.totalArity}", Some(span))

    // Erased-but-demoted (explicit) family args must appear in the spine, so recovery still runs;
    // implicit positions are then dropped per the explicit-only residual convention.
    val quotedArgs = explicitArgs(head.tpe, args).map(arg => quoteTerm(arg, context, span))
    val fn = ElabAst.Term.GlobalRef(head.name, span)
    if (quotedArgs.isEmpty) fn else ElabAst.Term.App(fn, quotedArgs, span)
  }

  /**
   * Erased family args are recovered structurally from the stored result type: constructor param discipline
   * (InductiveChecks.checkConstructorParamDiscipline) forces output param i to be binder var i, so spine slot i of the
   * family instance *is* family arg i. No unification involved.
   */
  private def recoverConstructorArgs(
      head: ConstructorHead,
      fields: Vector[Value],
      tpe: Value,
      span: Span
  ): Vector[Value] = {
    val expectedFields = head.totalArity - head.numErasedFamilyArgs
    if (fields.length != expectedFields)
      throw WTF(s"Constructor ${head.name} stores ${fields.length} args, expected $expectedFields", Some(span))

    if (head.numErasedFamilyArgs == 0) fields
    else
      tpe match {
        case ConstSpine(_, args) if args.length >= head.numErasedFamilyArgs =>
          args.take(head.numErasedFamilyArgs) ++ fields
        case other =>
          throw WTF(s"Constructor ${head.name} result type $other is not a family instance", Some(span))
      }
  }

  private def quoteLam(lam: VLam, context: QuoteContext, span: Span): ElabAst.Term = {
    (lam.id, lam.body) match {
      case _ if isRawRecursive(lam) =>
        // Note: this check has to come before the ValueId.Const shortcut for TerminationChecking
        throw CannotQuoteValue(lam, "raw recursive self", Some(span))
      case (ValueId.Const(name), _) => ElabAst.Term.GlobalRef(name, span)
      case (_, LamBody.Core(term, _)) =>
        val opened = quotePiOpened(lam.tpe, context, span)
        val bodyValue = Interpreter.runLam(lam, opened.freshArgs)
        val bodyTerm = quoteTerm(bodyValue, opened.context, span)
        val name = lam.id match {
          case ValueId.Const(globalName) => Some(globalName)
          case _                         => term.name
        }
        ElabAst.Term.Lam(opened.term, bodyTerm, span, name, term.recursiveSelf, AstNodeId.synthetic())
      case (_, LamBody.ProofEta) =>
        val opened = quotePiOpened(lam.tpe, context, span)
        val bodyTerm = quoteTerm(Interpreter.runLam(lam, opened.freshArgs), opened.context, span)
        ElabAst.Term.Lam(opened.term, bodyTerm, span, None, None, AstNodeId.synthetic())
      case (_, LamBody.Native(_, _, _)) => throw CannotQuoteValue(lam, "native lambda has no quoted syntax", Some(span))
    }
  }

  private def isRawRecursive(lam: VLam): Boolean =
    lam.body match {
      case LamBody.Native(_, _, true) => true
      case _                          => false
    }

  private def rawRecursiveAlias(value: Value): Option[Value] =
    value match {
      case lam: VLam if isRawRecursive(lam) =>
        lam.id match {
          case ValueId.Const(name) => Some(VConst(name, Symbol, lam.tpe))
          case _                   => None
        }
      case _ => None
    }

  private def withLocalQuote(quote: QuoteMap, ref: CoreAst.LocalRef, value: Value): QuoteMap = {
    val term = ElabAst.Term.LocalRef(ref, Span(0, 0))
    val withLocal = withQuotedValueInMap(quote, value, term)
    rawRecursiveAlias(value) match {
      case Some(alias) => withQuotedValueInMap(withLocal, alias, term)
      case None        => withLocal
    }
  }

  private def quotePiOpened(pi: VPi, context: QuoteContext, span: Span): OpenedPi = {
    val freshEnv = BinderOps.freshen(pi)
    val freshArgs = pi.binders.map(b => freshEnv(b.localRef))
    val freshLocals = freshEnv.locals.filterNot { case (ref, _) => pi.env.locals.contains(ref) }

    val nextQuote = freshLocals.foldLeft(context.quote) { case (quote, (ref, value)) =>
      withQuotedValueInMap(
        quote,
        value,
        ElabAst.Term.LocalRef(ref, Span(0, 0))
      )
    }
    val nextContext = QuoteContext(nextQuote)
    val result = pi.codomain(freshEnv)
    val quotedOut = quoteTerm(result, nextContext, span)
    val inliner = new ClosedEnvInliner(pi.env, context)

    val quotedBinders = pi.binders.map { b =>
      b.copy(ty = inliner.inlineTerm(b.ty))
    }

    OpenedPi(
      ElabAst.Term.Pi(quotedBinders, quotedOut, span, AstNodeId.synthetic()),
      freshArgs,
      nextContext
    )
  }

  private def quoteLevel(level: Level, context: QuoteContext, span: Span): ElabAst.Term = {
    def succ(term: ElabAst.Term, count: Int): ElabAst.Term =
      if (count == 0) term
      else {
        var cur = term
        var remaining = count
        while (remaining > 0) {
          cur = ElabAst.Term.App(ElabAst.Term.GlobalRef("Level.succ", span), Vector(cur), span)
          remaining -= 1
        }
        cur
      }

    def const(c: Int): ElabAst.Term =
      if (c == 0) ElabAst.Term.GlobalRef("Level.zero", span)
      else if (c == 1) ElabAst.Term.GlobalRef("Level.one", span)
      else succ(ElabAst.Term.GlobalRef("Level.zero", span), c)

    val atomTerms = level.terms.toVector.sortBy { case (atom, _) => ValueKey.levelAtomKey(atom) }.map {
      case (Level.ParamAtom(id), offset) =>
        val atom = Level.mk(id)
        val base =
          context.quote.get(atom.key).getOrElse(throw CannotQuoteValue(atom, "escaping level variable", Some(span)))
        succ(base, offset)
      case (Level.IMaxAtom(lhs, rhs), offset) =>
        val base = ElabAst.Term.App(
          ElabAst.Term.GlobalRef("Level.imax", span),
          Vector(quoteLevel(lhs, context, span), quoteLevel(rhs, context, span)),
          span
        )
        succ(base, offset)
    }

    val pieces =
      if (level.c == 0 && atomTerms.nonEmpty) atomTerms
      else atomTerms :+ const(level.c)

    pieces.reduceLeft { (left, right) =>
      ElabAst.Term.App(ElabAst.Term.GlobalRef("Level.max", span), Vector(left, right), span)
    }
  }

  private def withQuotedValueInMap(
      quote: QuoteMap,
      value: Value,
      term: ElabAst.Term
  ): QuoteMap = {
    val withValue = quote + (value.key -> term)
    value match {
      case Value.Var(_, id, Value.LevelTpe) => withValue + (Value.Level.mk(id).key -> term)
      case Value.VCtor(_, fields, tpe)      =>
        // An expanded struct binder (StructEta) carries fresh field witnesses with no syntax of
        // their own; register each as a selector application of the parent term so field vars,
        // proof fields, and nested expansions quote as projections. Strictly a fallback: fields
        // whose key already has an entry keep it, and fields with syntax of their own (concrete
        // data — no fresh vars, not proofs) are skipped entirely.
        StructEta.eligibleInstance(tpe) match {
          case Some((inst, info)) =>
            info.fieldNames.zip(fields).foldLeft(withValue) { case (curQuote, (fieldName, field)) =>
              val needsProjectionSyntax = field match {
                case _: Value.VProof => true // use canonical proof syntax rather than a fresh projection
                case _: Value.Var | _: Value.Level | Value.VCtor(_, _, _) => field.synDeps.nonEmpty
                case _                                                    => false
              }
              if (!needsProjectionSyntax || curQuote.contains(field.key)) curQuote
              else {
                val fieldTerm = ElabAst.Term.App(
                  ElabAst.Term.GlobalRef(s"${inst.head.name}.$fieldName", term.span),
                  Vector(term),
                  term.span
                )
                withQuotedValueInMap(curQuote, field, fieldTerm)
              }
            }
          case None => withValue
        }
      case _ => withValue
    }
  }
}
