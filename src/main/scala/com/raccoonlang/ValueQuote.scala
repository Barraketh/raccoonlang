package com.raccoonlang

import com.raccoonlang.ElabAst.{BinderType, Term, TypePattern}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

object ValueQuote {
  type QuoteMap = Map[ValueKey.Key, ElabAst.Term]
  final case class QuoteContext(quote: QuoteMap, localEnvLength: Int)

  private final case class OpenedPi(
      term: ElabAst.Term.Pi,
      freshArgs: Vector[Value],
      context: QuoteContext
  )

  def quoteContext(env: EnvLike[_])(implicit eqStore: EqStore): QuoteContext = {
    val quote = env.locals.zipWithIndex.foldLeft(Map.empty[ValueKey.Key, ElabAst.Term]) {
      case (quote, (binding, idx)) =>
        binding.valueOption match {
          case Some(value) =>
            val ref = CoreAst.LocalRef(idx, binding.name)
            withQuotedValue(quote, value, ElabAst.Term.LocalRef(ref, Span(0, 0)))
          case None => quote
        }
    }
    QuoteContext(quote, env.locals.length)
  }

  def quoteType(value: Value, context: QuoteContext, span: Span)(implicit eqStore: EqStore): ElabAst.TypeTerm =
    quoteTerm(value, context, span) match {
      case tpe: ElabAst.TypeTerm => tpe
      case other                 => throw CannotQuoteValue(value, s"$other is not a type term", Some(span))
    }

  def quoteTerm(value: Value, context: QuoteContext, span: Span)(implicit eqStore: EqStore): ElabAst.Term = {
    val materialized = ValueOps.materialize(value, eqStore)

    quotedTermFor(context.quote, materialized).foreach(return _)

    materialized match {
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
          (const.name.startsWith("select.") || const.name.startsWith("match#"))
        ) throw CannotQuoteValue(const, "internal synthetic constant", Some(span))
        else ElabAst.Term.GlobalRef(name, span)

      case VApp(VConst(name, Symbol, KernelObject), Vector(base), tpe)
          if name.startsWith("select.") && name.length > "select.".length =>
        quoteSelect(base, name.substring("select.".length), tpe, context, span)

      case VApp(head, args, _) =>
        val fn = quoteTerm(head, context, span)
        ElabAst.Term.App(fn, args.map(arg => quoteTerm(arg, context, span)), span)

      case VBlockedThunk(BlockedThunkBody.Select(base, field, _, _), _, tpe, _) =>
        quoteSelect(base, field, tpe, context, span)

      case VBlockedApp(head, args, _, _) =>
        ElabAst.Term.App(quoteTerm(head, context, span), args.map(arg => quoteTerm(arg, context, span)), span)

      case lam: VLam => quoteLam(lam, context, span)

      case pi: VPi => quotePiOpened(pi, context, span).term

      case head: ConstructorHead => ElabAst.Term.GlobalRef(head.name, span)

      case ctor: VCtor => quoteCtor(ctor, context, span)

      case level: Level => quoteLevel(level, context, span)

      case other => throw CannotQuoteValue(other, "no quoted syntax", Some(span))
    }
  }

  private def quoteSelect(
      base: Value,
      field: String,
      resultTy: Value,
      context: QuoteContext,
      span: Span
  )(implicit eqStore: EqStore): ElabAst.Term.Select =
    ElabAst.Term.Select(quoteTerm(base, context, span), field, quoteType(resultTy, context, span), span)

  private def quoteCtor(ctor: VCtor, context: QuoteContext, span: Span)(implicit eqStore: EqStore): ElabAst.Term = {
    val VCtor(head, args, _) = ctor

    if (args.length != head.totalArity)
      throw WTF(s"Constructor ${head.name} has ${args.length} args, expected ${head.totalArity}", Some(span))

    val quotedArgs = args.map(arg => quoteTerm(arg, context, span))
    val fn = ElabAst.Term.GlobalRef(head.name, span)
    if (quotedArgs.isEmpty) fn else ElabAst.Term.App(fn, quotedArgs, span)
  }

  private def quoteLam(lam: VLam, context: QuoteContext, span: Span)(implicit eqStore: EqStore): ElabAst.Term =
    lam.id match {
      case ValueId.Const(name) => ElabAst.Term.GlobalRef(name, span)
      case _ =>
        lam.body match {
          case LamBody.Core(term, _) =>
            val opened = quotePiOpened(lam.tpe, context, span)
            val bodyValue = Interpreter.runLam(lam, opened.freshArgs)
            val bodyTerm = quoteTerm(bodyValue, opened.context, span)
            val name = lam.id match {
              case ValueId.Const(globalName) => Some(globalName)
              case _                         => term.name
            }
            ElabAst.Term.Lam(opened.term, term.uses, bodyTerm, span, name, lam.isStable)

          case LamBody.Native(_) => throw CannotQuoteValue(lam, "native lambda has no quoted syntax", Some(span))
        }
    }

  private def quotePiOpened(pi: VPi, context: QuoteContext, span: Span)(implicit eqStore: EqStore): OpenedPi = {
    val freshEnv = BinderOps.freshen(pi)
    val freshArgs = pi.binders.map(b => freshEnv(b.localRef))
    val piEnvLength = pi.env.locals.length
    val freshLocals = freshEnv.locals.slice(piEnvLength, freshEnv.locals.length)

    val nextQuote = freshLocals.zipWithIndex.foldLeft(context.quote) { case (quote, (lb, idx)) =>
      val ref = CoreAst.LocalRef(context.localEnvLength + idx, lb.name)
      withQuotedValue(quote, lb.value, ElabAst.Term.LocalRef(ref, Span(0, 0)))
    }
    val nextContext = QuoteContext(nextQuote, context.localEnvLength + freshLocals.length)
    val result = pi.codomain(freshEnv, eqStore)
    val quotedOut = quoteType(result, nextContext, span)

    def reindex(l: CoreAst.LocalRef): CoreAst.LocalRef = l.copy(id = l.id - piEnvLength + context.localEnvLength)

    def inlineTerm(term: ElabAst.Term): ElabAst.Term = term match {
      case tt: ElabAst.TypeTerm => inlineTypeTerm(tt)
      case other                => throw WTF(s"Non type-term $other in binder")
    }

    // Inline localRefs with id < pi.env.length, and reindex refs introduced by the opened Pi.
    def inlineTypeTerm(term: ElabAst.TypeTerm): ElabAst.TypeTerm = term match {
      case ref: Term.Ref =>
        ref match {
          case ref: Term.GlobalRef => ref
          case ref: Term.LocalRef =>
            if (ref.ref.id < piEnvLength) quoteType(pi.env.locals(ref.ref.id).value, context, ref.span)
            else ref.copy(ref = reindex(ref.ref))
        }
      case s: Term.Select           => s.copy(base = inlineTerm(s.base), resultTy = inlineTypeTerm(s.resultTy))
      case Term.App(fn, args, span) => Term.App(inlineTerm(fn), args.map(inlineTerm), span)
      case pi: Term.Pi =>
        val newBinders = pi.binders.map(b => b.copy(localRef = reindex(b.localRef), ty = inlineBinderType(b.ty)))
        pi.copy(binders = newBinders, out = inlineTypeTerm(pi.out))
    }

    def inlineTopLevelTP(tp: ElabAst.TopLevelTP): ElabAst.TopLevelTP = tp match {
      case TypePattern.Type(term) => TypePattern.Type(inlineTypeTerm(term))
      case TypePattern.App(fn, args, span) =>
        val newRef = inlineTypeTerm(fn) match {
          case r: ElabAst.Term.Ref => r
          case other               => throw WTF(s"Failed to inline ref $fn, got $other")
        }
        TypePattern.App(newRef, args.map(inlineTypePattern), span)
    }

    def inlineTypePattern(tp: ElabAst.TypePattern): ElabAst.TypePattern = tp match {
      case p: ElabAst.TopLevelTP  => inlineTopLevelTP(p)
      case c: TypePattern.Capture => c.copy(localRef = reindex(c.localRef))
    }

    def inlineBinderType(b: ElabAst.BinderType): ElabAst.BinderType = b match {
      case b: BinderType.TypePattern => b.copy(tp = inlineTopLevelTP(b.tp))
      case b: BinderType.ConstrainedCapture =>
        b.copy(localRef = reindex(b.localRef), constraint = inlineTopLevelTP(b.constraint))
    }

    val quotedBinders = pi.binders.map { b =>
      ElabAst.Binder(reindex(b.localRef), inlineBinderType(b.ty), Span(0, 0), b.isInstance)
    }

    OpenedPi(ElabAst.Term.Pi(quotedBinders, quotedOut, pi.tpe, span), freshArgs, nextContext)
  }

  private def quoteLevel(level: Level, context: QuoteContext, span: Span)(implicit eqStore: EqStore): ElabAst.Term = {
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
      val base = quotedTermFor(context.quote, Level.mk(id))
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

  private def quotedTermFor(quote: QuoteMap, value: Value)(implicit eqStore: EqStore): Option[ElabAst.Term] =
    quote.get(ValueOps.materialize(value, eqStore).key)

  def withQuotedValue(quote: QuoteMap, value: Value, term: ElabAst.Term)(implicit
      eqStore: EqStore
  ): QuoteMap = {
    val materialized = ValueOps.materialize(value, eqStore)
    val withValue = quote + (materialized.key -> term)
    materialized match {
      case Value.Var(_, id, Value.LevelTpe) => withValue + (Value.Level.mk(id).key -> term)
      case _                                => withValue
    }
  }

  def withQuotedValue(context: QuoteContext, value: Value, term: ElabAst.Term)(implicit
      eqStore: EqStore
  ): QuoteContext =
    context.copy(quote = withQuotedValue(context.quote, value, term))
}
