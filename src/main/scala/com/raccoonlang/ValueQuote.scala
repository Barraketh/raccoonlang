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

  private final class ClosedEnvInliner(env: Env[Value], context: QuoteContext) {
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
        case ElabAst.Term.GlobalRef(_, _)        => t
        case ElabAst.Term.LocalRef(ref, refSpan) => inlineLocal(ref, refSpan)
        case ElabAst.Term.App(fn, args, appSpan) =>
          ElabAst.Term.App(inlineAppHead(fn), args.map(inlineTerm), appSpan)
        case ElabAst.Term.Pi(binders, out, piSpan, piNodeId) =>
          val nextBinders = binders.map { b =>
            b.copy(ty = inlineTypeTerm(b.ty))
          }
          ElabAst.Term.Pi(nextBinders, inlineTypeTerm(out), piSpan, piNodeId)
        case ElabAst.Term.Body(lets, res, bodySpan) =>
          val nextLets = lets.map { l =>
            ElabAst.Let(l.localRef, l.ty.map(inlineTypeTerm), inlineTerm(l.value), l.span)
          }
          ElabAst.Term.Body(nextLets, inlineTerm(res), bodySpan)
        case ElabAst.Term.Lam(ty, body, lamSpan, name, recursiveSelf, lamNodeId) =>
          ElabAst.Term.Lam(
            inlineTypeTerm(ty).asInstanceOf[ElabAst.Term.Pi],
            inlineTerm(body),
            lamSpan,
            name,
            recursiveSelf,
            lamNodeId
          )
        case ElabAst.Term.Match(scrut, motive, cases, matchSpan, matchNodeId) =>
          ElabAst.Term.Match(
            inlineTerm(scrut),
            motive.map(inlineTypeTerm),
            cases.map(inlineCase),
            matchSpan,
            matchNodeId
          )
      }

    def inlineTypeTerm(t: ElabAst.TypeTerm): ElabAst.TypeTerm =
      t match {
        case ElabAst.Term.GlobalRef(_, _) => t
        case ElabAst.Term.LocalRef(ref, refSpan) =>
          inlineLocal(ref, refSpan) match {
            case tt: ElabAst.TypeTerm => tt
            case other                => throw CannotQuoteValue(env(ref), s"$other is not a type term", Some(refSpan))
          }
        case ElabAst.Term.App(fn, args, appSpan) =>
          ElabAst.Term.App(inlineAppHead(fn), args.map(inlineTerm), appSpan)
        case ElabAst.Term.Pi(binders, out, piSpan, piNodeId) =>
          val nextBinders = binders.map { b =>
            b.copy(ty = inlineTypeTerm(b.ty))
          }
          ElabAst.Term.Pi(nextBinders, inlineTypeTerm(out), piSpan, piNodeId)
      }

    def inlineCase(c: ElabAst.Case): ElabAst.Case =
      ElabAst.Case(c.ctorName, c.argRefs, inlineTerm(c.body), c.span)
  }

  def quoteContext(env: Env[Value]): QuoteContext = {
    val quote = env.locals.foldLeft(Map.empty[ValueKey.Key, ElabAst.Term]) { case (quote, (ref, value)) =>
      withLocalQuote(quote, ref, value)
    }
    QuoteContext(quote)
  }

  def quoteType(value: Value, context: QuoteContext, span: Span): ElabAst.TypeTerm =
    quoteTerm(value, context, span) match {
      case tpe: ElabAst.TypeTerm => tpe
      case other                 => throw CannotQuoteValue(value, s"$other is not a type term", Some(span))
    }

  def quotePiType(pi: VPi, context: QuoteContext, span: Span): ElabAst.Term.Pi =
    quotePiOpened(pi, context, span).term

  def quoteTerm(value: Value, context: QuoteContext, span: Span): ElabAst.Term = {
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

      case VCtor(head, fields, tpe) => quoteCtor(head, fields, tpe, context, span)

      case VApp(head, args, _, _) =>
        val fn = quoteAppHead(head, context, span)
        ElabAst.Term.App(fn, args.map(arg => quoteTerm(arg, context, span)), span)

      case NeutralThunk(term, env, _, _, _) => quoteClosedMatch(term, env, context, span)

      case lam: VLam => quoteLam(lam, context, span)

      case pi: VPi => quotePiOpened(pi, context, span).term

      case head: ConstructorHead => ElabAst.Term.GlobalRef(head.name, span)

      case level: Level => quoteLevel(level, context, span)

      // A collapsed proof has no syntax of its own; all proofs of the proposition share a key, so
      // the context lookup above already resolved it to any in-scope proof term. Otherwise fall
      // back to the erased witness it was collapsed from (a global constant, a constructor
      // application, ...). Materialization may have re-wrapped the witness; recursion unwraps.
      case p: VProof => quoteTerm(p.witness, context, span)

      case other => throw CannotQuoteValue(other, "no quoted syntax", Some(span))
    }
  }

  private def quoteAppHead(value: Value, context: QuoteContext, span: Span): ElabAst.Term =
    context.quote.get(value.key).getOrElse(quoteTerm(value, context, span))

  private def quoteClosedMatch(
      term: ElabAst.Term.Match,
      env: Env[Value],
      context: QuoteContext,
      span: Span
  ): ElabAst.Term.Match = {
    val inliner = new ClosedEnvInliner(env, context)

    ElabAst.Term.Match(
      quoteTerm(Interpreter.evalTerm(term.scrut, env), context, term.scrut.span),
      term.motive.map(motive => quoteType(Interpreter.evalTypeTerm(motive, env), context, motive.span)),
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

    val quotedArgs = args.map(arg => quoteTerm(arg, context, span))
    val fn = ElabAst.Term.GlobalRef(head.name, span)
    if (quotedArgs.isEmpty) fn else ElabAst.Term.App(fn, quotedArgs, span)
  }

  /**
   * Erased family args are recovered structurally from the stored result type: constructor param
   * discipline (InductiveChecks.checkConstructorParamDiscipline) forces output param i to be binder
   * var i, so spine slot i of the family instance *is* family arg i. No unification involved.
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
    val quotedOut = quoteType(result, nextContext, span)
    val inliner = new ClosedEnvInliner(pi.env, context)

    val quotedBinders = pi.binders.map { b =>
      ElabAst.Binder(b.localRef, inliner.inlineTypeTerm(b.ty), Span(0, 0), b.isImplicit, b.projection)
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

    val atomTerms = level.atoms.toVector.sortBy(_._1).map { case (id, offset) =>
      val atom = Level.mk(id)
      val base =
        context.quote.get(atom.key).getOrElse(throw CannotQuoteValue(atom, "escaping level variable", Some(span)))
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
      case _                                => withValue
    }
  }
}
