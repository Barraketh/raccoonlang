package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

object ValueQuote {
  final case class QuoteEntry(term: ElabAst.Term, residualPolicy: LocalResidualPolicy)

  type QuoteMap = Map[ValueKey.Key, QuoteEntry]
  final case class QuoteContext(quote: QuoteMap, localEnvLength: Int)

  private final case class OpenedPi(
      term: ElabAst.Term.Pi,
      freshArgs: Vector[Value],
      context: QuoteContext
  )

  private final class ClosedEnvInliner(env: Env, context: QuoteContext) {
    private val envLength = env.locals.length

    def reindex(ref: CoreAst.LocalRef): CoreAst.LocalRef =
      ref.copy(id = ref.id - envLength + context.localEnvLength)

    private def inlineLocal(ref: CoreAst.LocalRef, refSpan: Span): ElabAst.Term =
      if (ref.id < envLength) quoteTerm(env(ref), context, refSpan)
      else ElabAst.Term.LocalRef(reindex(ref), refSpan)

    private def inlineAppHead(t: ElabAst.Term): ElabAst.Term =
      t match {
        case ElabAst.Term.LocalRef(ref, refSpan) =>
          if (ref.id < envLength) quoteAppHead(env(ref), context, refSpan)
          else ElabAst.Term.LocalRef(reindex(ref), refSpan)
        case other => inlineTerm(other)
      }

    def inlineTerm(t: ElabAst.Term): ElabAst.Term =
      t match {
        case ElabAst.Term.GlobalRef(_, _)        => t
        case ElabAst.Term.LocalRef(ref, refSpan) => inlineLocal(ref, refSpan)
        case ElabAst.Term.App(fn, args, appSpan) =>
          ElabAst.Term.App(inlineAppHead(fn), args.map(inlineTerm), appSpan)
        case ElabAst.Term.Pi(binders, out, classifier, piSpan) =>
          val nextBinders = binders.map { b =>
            b.copy(localRef = reindex(b.localRef), ty = inlineTopLevelTP(b.ty))
          }
          ElabAst.Term.Pi(nextBinders, inlineTypeTerm(out), classifier, piSpan)
        case ElabAst.Term.Body(lets, res, bodySpan) =>
          val nextLets = lets.map { l =>
            ElabAst.Let(reindex(l.localRef), l.ty.map(inlineTypeTerm), inlineTerm(l.value), l.span, l.isInstance)
          }
          ElabAst.Term.Body(nextLets, inlineTerm(res), bodySpan)
        case ElabAst.Term.Lam(ty, body, lamSpan, name, isStable, recursiveSelf) =>
          ElabAst.Term.Lam(
            inlineTypeTerm(ty).asInstanceOf[ElabAst.Term.Pi],
            inlineTerm(body),
            lamSpan,
            name,
            isStable,
            recursiveSelf
          )
        case ElabAst.Term.Match(scrut, motive, cases, matchSpan) =>
          ElabAst.Term.Match(
            inlineTerm(scrut),
            motive.map(inlineTypeTerm),
            cases.map(inlineCase),
            matchSpan
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
        case ElabAst.Term.Pi(binders, out, classifier, piSpan) =>
          val nextBinders = binders.map { b =>
            b.copy(localRef = reindex(b.localRef), ty = inlineTopLevelTP(b.ty))
          }
          ElabAst.Term.Pi(nextBinders, inlineTypeTerm(out), classifier, piSpan)
      }

    private def inlineTypePattern(tp: ElabAst.TypePattern): ElabAst.TypePattern =
      tp match {
        case top: ElabAst.TopLevelTP                       => inlineTopLevelTP(top)
        case ElabAst.TypePattern.Capture(ref, captureSpan) => ElabAst.TypePattern.Capture(reindex(ref), captureSpan)
      }

    def inlineTopLevelTP(tp: ElabAst.TopLevelTP): ElabAst.TopLevelTP =
      tp match {
        case ElabAst.TypePattern.Type(tpe) => ElabAst.TypePattern.Type(inlineTypeTerm(tpe))
        case ElabAst.TypePattern.App(fn, args, appSpan) =>
          val nextFn =
            inlineAppHead(fn) match {
              case ref: ElabAst.Term.Ref => ref
              case other                 => throw WTF(s"Failed to inline ref $fn, got $other")
            }
          ElabAst.TypePattern.App(nextFn, args.map(inlineTypePattern), appSpan)
        case ElabAst.TypePattern.ConstrainedCapture(ref, constraint, captureSpan) =>
          ElabAst.TypePattern.ConstrainedCapture(reindex(ref), inlineTopLevelTP(constraint), captureSpan)
      }

    def inlineCase(c: ElabAst.Case): ElabAst.Case =
      ElabAst.Case(c.ctorName, c.argRefs.map(_.map(reindex)), inlineTerm(c.body), c.span)
  }

  def quoteContext(env: Env): QuoteContext = {
    val quote = env.locals.zipWithIndex.foldLeft(Map.empty[ValueKey.Key, QuoteEntry]) { case (quote, (binding, idx)) =>
      withLocalQuote(quote, binding, idx)
    }
    QuoteContext(quote, env.locals.length)
  }

  def quoteType(value: Value, context: QuoteContext, span: Span): ElabAst.TypeTerm =
    quoteTerm(value, context, span) match {
      case tpe: ElabAst.TypeTerm => tpe
      case other                 => throw CannotQuoteValue(value, s"$other is not a type term", Some(span))
    }

  def quoteTerm(value: Value, context: QuoteContext, span: Span): ElabAst.Term = {
    quotedTermFor(context.quote, value, span).foreach(return _)

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

      case LevelTpe       => ElabAst.Term.GlobalRef("Level", span)
      case NormalizerType => ElabAst.Term.GlobalRef("Normalizer", span)

      case const @ VConst(name, _, _) =>
        if (
          const.constType == Symbol &&
          const.tpe == KernelObject &&
          const.name.startsWith("match#")
        ) throw CannotQuoteValue(const, "internal synthetic constant", Some(span))
        else ElabAst.Term.GlobalRef(name, span)

      case VCtor(head, fields, tpe) => quoteCtor(head, fields, tpe, context, span)

      case VApp(head, args, _, _) =>
        val fn = quoteAppHead(head, context, span)
        ElabAst.Term.App(fn, args.map(arg => quoteTerm(arg, context, span)), span)

      case NeutralThunk(term, env, _, _, _) => quoteClosedMatch(term, env, context, span)

      case lam: VLam => quoteLam(lam, context, span)

      case pi: VPi => quotePiOpened(pi, context, span).term

      case head: ConstructorHead => ElabAst.Term.GlobalRef(head.name, span)

      case level: Level => quoteLevel(level, context, span)

      case other => throw CannotQuoteValue(other, "no quoted syntax", Some(span))
    }
  }

  private def quoteAppHead(value: Value, context: QuoteContext, span: Span): ElabAst.Term =
    quotedAppHeadFor(context.quote, value).getOrElse(quoteTerm(value, context, span))

  private def quoteClosedMatch(
      term: ElabAst.Term.Match,
      env: Env,
      context: QuoteContext,
      span: Span
  ): ElabAst.Term.Match = {
    val inliner = new ClosedEnvInliner(env, context)

    ElabAst.Term.Match(
      quoteTerm(Interpreter.evalTerm(term.scrut, env), context, term.scrut.span),
      term.motive.map(motive => quoteType(Interpreter.evalTypeTerm(motive, env), context, motive.span)),
      term.cases.map(inliner.inlineCase),
      span
    )
  }

  private def quoteCtor(
      head: ConstructorHead,
      fields: Vector[Value],
      tpe: Value,
      context: QuoteContext,
      span: Span
  ): ElabAst.Term = {
    val erasedArgs =
      if (head.erasedFamilyArgIndexes.isEmpty) Vector.empty
      else {
        tpe match {
          case ConstSpine(_, args) => head.erasedFamilyArgIndexes.map(idx => args(idx))
          case _ => throw WTF(s"Cannot recover erased constructor args for ${head.name} from $tpe", Some(span))
        }
      }

    val args = erasedArgs ++ fields

    if (args.length != head.totalArity)
      throw WTF(s"Constructor ${head.name} has ${args.length} args, expected ${head.totalArity}", Some(span))

    val quotedArgs = args.map(arg => quoteTerm(arg, context, span))
    val fn = ElabAst.Term.GlobalRef(head.name, span)
    if (quotedArgs.isEmpty) fn else ElabAst.Term.App(fn, quotedArgs, span)
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
        ElabAst.Term.Lam(opened.term, bodyTerm, span, name, lam.isStable, term.recursiveSelf)
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

  private def withLocalQuote(quote: QuoteMap, binding: Binding, idx: Int): QuoteMap =
    binding.valueOption match {
      case Some(value) =>
        val ref = CoreAst.LocalRef(idx, binding.name)
        val term = ElabAst.Term.LocalRef(ref, Span(0, 0))
        val withLocal = withQuotedValueInMap(quote, value, term, binding.residualPolicy)
        rawRecursiveAlias(value) match {
          case Some(alias) => withQuotedValueInMap(withLocal, alias, term, binding.residualPolicy)
          case None        => withLocal
        }
      case None => quote
    }

  private def quotePiOpened(pi: VPi, context: QuoteContext, span: Span): OpenedPi = {
    val freshEnv = BinderOps.freshen(pi)
    val freshArgs = pi.binders.map(b => freshEnv(b.localRef))
    val piEnvLength = pi.env.locals.length
    val freshLocals = freshEnv.locals.slice(piEnvLength, freshEnv.locals.length)

    val nextQuote = freshLocals.zipWithIndex.foldLeft(context.quote) { case (quote, (lb, idx)) =>
      val ref = CoreAst.LocalRef(context.localEnvLength + idx, lb.name)
      withQuotedValueInMap(quote, lb.value, ElabAst.Term.LocalRef(ref, Span(0, 0)), LocalResidualPolicy.Residualizable)
    }
    val nextContext = QuoteContext(nextQuote, context.localEnvLength + freshLocals.length)
    val result = pi.codomain(freshEnv)
    val quotedOut = quoteType(result, nextContext, span)
    val inliner = new ClosedEnvInliner(pi.env, context)

    val quotedBinders = pi.binders.map { b =>
      ElabAst.Binder(inliner.reindex(b.localRef), inliner.inlineTopLevelTP(b.ty), Span(0, 0), b.isInstance)
    }

    OpenedPi(ElabAst.Term.Pi(quotedBinders, quotedOut, pi.tpe, span), freshArgs, nextContext)
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
      val base = quotedTermFor(context.quote, Level.mk(id), span)
        .getOrElse(throw CannotQuoteValue(Level.mk(id), "escaping level variable", Some(span)))
      succ(base, offset)
    }

    val pieces =
      if (level.c == 0 && atomTerms.nonEmpty) atomTerms
      else atomTerms :+ const(level.c)

    pieces.reduceLeft { (left, right) =>
      ElabAst.Term.App(ElabAst.Term.GlobalRef("Level.max", span), Vector(left, right), span)
    }
  }

  private def quotedTermFor(
      quote: QuoteMap,
      value: Value,
      span: Span
  ): Option[ElabAst.Term] =
    quote.get(value.key).map { entry =>
      entry.residualPolicy match {
        case LocalResidualPolicy.Residualizable => entry.term
        case LocalResidualPolicy.AppHeadOnly(name) =>
          throw CannotQuoteValue(value, s"$name is only available as an application head", Some(span))
      }
    }

  private def quotedAppHeadFor(quote: QuoteMap, value: Value): Option[ElabAst.Term] =
    quote.get(value.key).map(_.term)

  private def withQuotedValueInMap(
      quote: QuoteMap,
      value: Value,
      term: ElabAst.Term,
      residualPolicy: LocalResidualPolicy
  ): QuoteMap = {
    val entry = QuoteEntry(term, residualPolicy)
    val withValue = quote + (value.key -> entry)
    value match {
      case Value.Var(_, id, Value.LevelTpe) => withValue + (Value.Level.mk(id).key -> entry)
      case _                                => withValue
    }
  }
}
