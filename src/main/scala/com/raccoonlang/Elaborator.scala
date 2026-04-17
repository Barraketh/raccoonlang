package com.raccoonlang

import com.raccoonlang.CoreAst.UnfoldStrategy
import com.raccoonlang.Util.NEL

object Elaborator {
  val SA = SurfaceAst
  val CA = CoreAst

  private def elabPi(pi: SA.Term.Pi): CA.Term.Pi = {
    val binder = elab(pi.binder)
    val body = elab(pi.body)
    val span = Span(binder.span.start, body.span.end)
    body match {
      case pi: CA.Term.Pi => CA.Term.Pi(binder :: pi.binders, pi.out, span)
      case other          => CA.Term.Pi(NEL.one(binder), other, span)
    }
  }

  private def elab(i: SA.Term.Ident): CA.Term.Ident = CA.Term.Ident(i.name, i.span)

  private def elab(ty: SA.TypeTerm): CA.TypeTerm = ty match {
    case i: SA.Term.Ident                 => elab(i)
    case SA.Term.TApp(fn, args, sp)       => CoreAst.Term.TApp(elab(fn), args.map(_.map(elab)), sp)
    case pi: SA.Term.Pi                   => elabPi(pi)
    case SA.Term.TSelect(base, field, sp) => CA.Term.TSelect(elab(base), field, sp)
    case SA.Term.Capture(name, sp)        => throw new RuntimeException(s"$$ cannot be used here: $name")
  }

  private def elabPattern(ty: SA.TypeTerm): CA.TypePattern = ty match {
    case i: SA.Term.Ident                 => elab(i)
    case SA.Term.TApp(fn, args, sp)       => CoreAst.Term.PatternApp(elab(fn), args.map(_.map(elabPattern)), sp)
    case pi: SA.Term.Pi                   => elabPi(pi)
    case SA.Term.TSelect(base, field, sp) => CA.Term.TSelect(elab(base), field, sp)
    case SA.Term.Capture(name, sp)        => CA.Term.Capture(name, sp)
  }

  private def elab(use: SA.Use): CA.Use = CA.Use(elab(use.normalizer), use.span)

  private def elab(body: SA.Term.Body): CA.Term.Body = {
    if (body.uses.nonEmpty) throw new RuntimeException("Use statements only allowed at top of fn declaration")

    CA.Term.Body(body.lets.map(l => CA.Let(l.name, l.ty.map(elab), elab(l.value), l.span)), elab(body.out), body.span)
  }

  private def elabLam(
      pi: CA.Term.Pi,
      body: SA.Term,
      name: Option[String],
      isStable: Boolean,
      span: Span
  ): CA.Term.Lam = {
    val (uses, newBody) = body match {
      case b: SA.Term.Body => (b.uses, b.copy(uses = Vector.empty))
      case _               => (Vector.empty, body)
    }
    CA.Term.Lam(pi, uses.map(elab), elab(newBody), span, name, isStable)
  }

  private def elab(l: SA.Term.Lam): CA.Term.Lam = {
    getType(l.header) match {
      case pi: CA.Term.Pi =>
        elabLam(pi, l.body, None, isStable = false, l.span)
      case _ => throw new RuntimeException("WTF")
    }
  }

  private def elab(term: SurfaceAst.Term): CA.Term = term match {
    case SA.Term.Ident(name, sp)         => CA.Term.Ident(name, sp)
    case SA.Term.App(fn, args, sp)       => CA.Term.App(elab(fn), args.map(_.map(elab)), sp)
    case SA.Term.Select(base, field, sp) => CA.Term.Select(elab(base), field, sp)
    case pi: SA.Term.Pi                  => elabPi(pi)
    case l: SA.Term.Lam                  => elab(l)
    case b: SA.Term.Body                 => elab(b)
    case SA.Term.Match(scrut, motive, cases, sp) =>
      CA.Term.Match(
        elab(scrut),
        motive.map(elab),
        cases.map(c => CA.Case(c.ctorName, c.argNames, elab(c.body), c.span)),
        sp
      )
  }

  private def elab(b: SA.Binder): CA.Binder = CA.Binder(b.name, elabPattern(b.ty), b.span)

  def getType(header: SA.FuncHeader): CA.TypeTerm = {
    val outTy = elab(header.ty)
    if (header.params.isEmpty) outTy
    else CoreAst.Term.Pi(NEL.mk(header.params.map(elab)), outTy, header.span)
  }

  def elab(surface: SurfaceAst.Decl): CoreAst.Decl = {
    surface match {
      case c: SurfaceAst.Decl.ConstDecl =>
        val typeTerm = getType(c.header.funcHeader)
        val body = typeTerm match {
          case pi: CA.Term.Pi =>
            elabLam(pi, c.body, Some(c.header.name), c.unfoldStrategy.contains(UnfoldStrategy.Stable), c.span)
          case _ => elab(c.body)
        }
        CoreAst.Decl.ConstDecl(c.unfoldStrategy, c.header.name, typeTerm, body, c.span)
      case c: SurfaceAst.Decl.InductiveDecl =>
        val header = CA.InductiveHeader(
          c.header.name,
          c.header.params.map(elab),
          c.header.indices.map(elab),
          elab(c.header.resultTy),
          c.span
        )

        val ctors =
          c.ctors.map { ctor =>
            CA.ConstructorDecl(
              name = c.header.name + "::" + ctor.name,
              fields = ctor.fields.map(elab),
              resultTy = elab(ctor.resultTy),
              span = ctor.span
            )
          }
        CoreAst.Decl.InductiveDecl(header, ctors, c.isStruct, c.span)
    }
  }

  def elab(p: SA.Program): CA.Program = CA.Program(p.decls.map(elab), p.body.map(elab))

}
