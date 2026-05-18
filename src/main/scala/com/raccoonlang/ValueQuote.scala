package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.{BinderOps, ConstructorOps}

object ValueQuote {
  final case class Context(projectedVars: Map[VarId, ElabAst.Term] = Map.empty) {
    def withValue(value: Value, term: ElabAst.Term)(implicit eqStore: EqStore): Context =
      varId(value) match {
        case Some(id) => copy(projectedVars = projectedVars + (id -> term))
        case None     => this
      }
  }

  object Context {
    val empty: Context = Context()
  }

  def quoteType(
      value: Value,
      env: TypecheckEnv,
      span: Span,
      context: Context = Context.empty
  )(implicit eqStore: EqStore, typecheckCtx: TypecheckContext): ElabAst.TypeTerm =
    quoteTerm(value, env, span, context) match {
      case tpe: ElabAst.TypeTerm => tpe
      case other                 => throw CannotQuoteValue(value, s"$other is not a type term", Some(span))
    }

  def quoteTerm(
      value: Value,
      env: TypecheckEnv,
      span: Span,
      context: Context = Context.empty
  )(implicit eqStore: EqStore, typecheckCtx: TypecheckContext): ElabAst.Term = {
    val materialized = ValueOps.materialize(value, eqStore)

    materialized match {
      case v @ Var(_, id, _) =>
        context.projectedVars
          .get(id)
          .orElse(localRefFor(v, env, span))
          .getOrElse(throw CannotQuoteValue(v, "escaping variable", Some(span)))

      case VSort(level) =>
        if (level == Level.zero) ElabAst.Term.GlobalRef("Prop", span)
        else if (level == Level.one) ElabAst.Term.GlobalRef("Type", span)
        else ElabAst.Term.App(ElabAst.Term.GlobalRef("Sort", span), Vector(quoteLevel(level, env, span, context)), span)

      case LevelTpe       => ElabAst.Term.GlobalRef("Level", span)
      case NormalizerType => ElabAst.Term.GlobalRef("Normalizer", span)

      case const @ VConst(name, _, _) =>
        if (env.globals.contains(name)) ElabAst.Term.GlobalRef(name, span)
        else localRefOrFail(const, env, span)

      case app @ VApp(head, args, tpe) =>
        quoteInternalSelect(head, args, tpe, env, span, context).getOrElse {
          if (env.globals.contains(head.name)) {
            val fn = quoteTerm(head, env, span, context)
            ElabAst.Term.App(fn, args.map(arg => quoteTerm(arg, env, span, context)), span)
          } else {
            localRefOrFail(app, env, span)
          }
        }

      case VBlockedThunk(BlockedThunkBody.Select(base, field, _, _), _, tpe, _) =>
        quoteSelect(base, field, tpe, env, span, context)

      case VBlockedApp(head, args, _, _) =>
        ElabAst.Term.App(
          quoteTerm(head, env, span, context),
          args.map(arg => quoteTerm(arg, env, span, context)),
          span
        )

      case pi: VPi => quotePi(pi, env, span, context)

      case head: ConstructorHead =>
        if (env.globals.contains(head.name)) ElabAst.Term.GlobalRef(head.name, span)
        else localRefOrFail(head, env, span)

      case ctor: VCtor => quoteCtor(ctor, env, span, context)

      case level: Level => quoteLevel(level, env, span, context)

      case other => localRefOrFail(other, env, span)
    }
  }

  private def quoteInternalSelect(
      head: VConst,
      args: Vector[Value],
      tpe: Value,
      env: TypecheckEnv,
      span: Span,
      context: Context
  )(implicit eqStore: EqStore, typecheckCtx: TypecheckContext): Option[ElabAst.Term.Select] =
    args match {
      case Vector(base) =>
        internalSelectField(head, env).map(field => quoteSelect(base, field, tpe, env, span, context))
      case _ => None
    }

  private def quoteSelect(
      base: Value,
      field: String,
      resultTy: Value,
      env: TypecheckEnv,
      span: Span,
      context: Context
  )(implicit eqStore: EqStore, typecheckCtx: TypecheckContext): ElabAst.Term.Select =
    ElabAst.Term.Select(
      quoteTerm(base, env, span, context),
      field,
      quoteType(resultTy, env, span, context),
      span
    )

  private def quoteCtor(
      ctor: VCtor,
      env: TypecheckEnv,
      span: Span,
      context: Context
  )(implicit eqStore: EqStore, typecheckCtx: TypecheckContext): ElabAst.Term = {
    val VCtor(head, fields, tpe) = ctor
    if (!env.globals.contains(head.name)) return localRefOrFail(ctor, env, span)

    val fresh = ConstructorOps.freshSpine(head)
    if (fresh.fields.length != fields.length)
      throw CannotQuoteValue(ctor, "constructor field arity mismatch", Some(span))

    val refined =
      try {
        val start = ValueEquivalence.unify(fresh.tpe, tpe, eqStore.copy(refinable = fresh.synDeps))
        fresh.fields.zip(fields).foldLeft(start) { case (cur, (freshField, field)) =>
          ValueEquivalence.unify(freshField, field, cur)
        }
      } catch {
        case _: UnificationFailed | _: OccursCheckFailed =>
          throw CannotQuoteValue(ctor, "cannot recover constructor arguments", Some(span))
      }

    val quotedArgs = fresh.args.map(arg => quoteTerm(arg, env, span, context)(refined, typecheckCtx))
    val fn = ElabAst.Term.GlobalRef(head.name, span)
    if (quotedArgs.isEmpty) fn else ElabAst.Term.App(fn, quotedArgs, span)
  }

  private def internalSelectField(head: VConst, env: TypecheckEnv): Option[String] = {
    val prefix = "select."
    if (
      head.constType == Symbol &&
      head.tpe == KernelObject &&
      !env.globals.contains(head.name) &&
      head.name.startsWith(prefix) &&
      head.name.length > prefix.length
    ) Some(head.name.substring(prefix.length))
    else None
  }

  private def quotePi(
      pi: VPi,
      env: TypecheckEnv,
      span: Span,
      context: Context
  )(implicit eqStore: EqStore, typecheckCtx: TypecheckContext): ElabAst.Term.Pi = {
    val freshEnv = BinderOps.freshen(pi)
    val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))

    var quoteEnv = env
    var quoteContext = context
    val quotedBinders = Vector.newBuilder[ElabAst.Binder]

    pi.binders.zip(freshArgs).foreach { case (binder, freshArg) =>
      val ref = CoreAst.LocalRef(quoteEnv.locals.length, binder.name)
      val domain = quoteType(freshArg.tpe, quoteEnv, span, quoteContext)
      val binderType = ElabAst.BinderType.TypePattern(ElabAst.TypePattern.Type(domain), span)
      val quotedBinder = ElabAst.Binder(ref, binderType, span, binder.isInstance)

      quotedBinders += quotedBinder
      quoteContext = quoteContext.withValue(freshArg, ElabAst.Term.LocalRef(ref, span))
      quoteEnv = quoteEnv.putLocal(ref, freshArg)
    }

    val outValue = pi.codomain(freshEnv, eqStore)
    val quotedOut = quoteType(outValue, quoteEnv, span, quoteContext)
    ElabAst.Term.Pi(quotedBinders.result(), quotedOut, pi.tpe, span)
  }

  private def quoteLevel(
      level: Level,
      env: TypecheckEnv,
      span: Span,
      context: Context
  )(implicit eqStore: EqStore): ElabAst.Term = {
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

    val atomTerms =
      level.atoms.toVector.sortBy(_._1).map { case (id, offset) =>
        val base = context.projectedVars
          .get(id)
          .orElse(localRefForVar(id, env, span))
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

  private def varId(value: Value)(implicit eqStore: EqStore): Option[VarId] =
    ValueOps.materialize(value, eqStore) match {
      case Var(_, id, _) => Some(id)
      case _             => None
    }

  private def localRefForVar(id: VarId, env: TypecheckEnv, span: Span)(implicit
      eqStore: EqStore
  ): Option[ElabAst.Term.LocalRef] =
    env.locals.zipWithIndex.reverseIterator.collectFirst {
      case (binding, idx) if binding.valueOption.exists(value => varId(value).contains(id)) =>
        ElabAst.Term.LocalRef(CoreAst.LocalRef(idx, binding.name), span)
    }

  private def localRefFor(value: Value, env: TypecheckEnv, span: Span)(implicit
      eqStore: EqStore
  ): Option[ElabAst.Term.LocalRef] = {
    val materialized = ValueOps.materialize(value, eqStore)
    env.locals.zipWithIndex.reverseIterator.collectFirst {
      case (binding, idx) if binding.valueOption.exists(localValue => sameQuotedValue(materialized, localValue)) =>
        ElabAst.Term.LocalRef(CoreAst.LocalRef(idx, binding.name), span)
    }
  }

  private def localRefOrFail(value: Value, env: TypecheckEnv, span: Span)(implicit
      eqStore: EqStore
  ): ElabAst.Term =
    localRefFor(value, env, span).getOrElse(throw CannotQuoteValue(value, "no in-scope syntax", Some(span)))

  private def sameQuotedValue(a: Value, b: Value)(implicit eqStore: EqStore): Boolean = {
    val a0 = ValueOps.materialize(a, eqStore)
    val b0 = ValueOps.materialize(b, eqStore)
    (a0.asInstanceOf[AnyRef] eq b0.asInstanceOf[AnyRef]) || a0.key == b0.key
  }
}
