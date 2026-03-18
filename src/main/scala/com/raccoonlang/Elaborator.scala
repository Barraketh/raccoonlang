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

  private def elab(ty: SA.TypeTerm): CA.TypeTerm = ty match {
    case SA.Term.Ident(name, sp)    => CoreAst.Term.Ident(name, sp)
    case SA.Term.TApp(fn, args, sp) => CoreAst.Term.TApp(elab(fn), args.map(elab), sp)
    case SA.Term.Sort(level, span)  => CA.Term.Sort(elab(level), span)
    case pi: SA.Term.Pi             => elabPi(pi)
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
    case SA.Term.Ident(name, sp)   => CA.Term.Ident(name, sp)
    case SA.Term.App(fn, args, sp) => CA.Term.App(elab(fn), args.map(elab), sp)
    case l: SA.Term.Lam            => elab(l)
    case b: SA.Term.Body           => elab(b)
    case SA.Term.Match(scrut, scrutName, motive, cases, sp) =>
      CA.Term.Match(
        elab(scrut),
        scrutName,
        elab(motive),
        cases.map(c => CA.Case(c.ctorName, c.argNames, elab(c.body), c.span)),
        sp
      )
  }

  private def elab(b: SA.Binder): CA.Binder = CA.Binder(b.name, elab(b.ty), b.span)

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
        CoreAst.Decl.InductiveDecl(
          c.header.name,
          getType(c.header.funcHeader),
          c.ctors.map(ctor => CA.Constructor(c.header.name + "." + ctor.name, getType(ctor.funcHeader), ctor.span)),
          c.span
        )
    }
  }

  def elab(p: SA.Program): CA.Program = CA.Program(p.decls.map(elab), elab(p.body))

}
