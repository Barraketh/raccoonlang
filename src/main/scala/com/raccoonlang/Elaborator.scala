package com.raccoonlang

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
    case pi: SA.Term.Pi             => elabPi(pi)
  }

  private def elab(body: SA.Body): CA.Body =
    CA.Body(body.lets.map(l => CA.Let(l.name, l.ty.map(elab), elab(l.value), l.span)), elab(body.out), body.span)

  private def elab(term: SurfaceAst.Term): CA.Term = term match {
    case SA.Term.Ident(name, sp)   => CA.Term.Ident(name, sp)
    case SA.Term.App(fn, args, sp) => CA.Term.App(elab(fn), args.map(elab), sp)
    case SA.Term.Lam(header, body, sp) =>
      getType(header) match {
        case pi: CA.Term.Pi => CA.Term.Lam(pi, elab(body), sp)
        case _              => throw new RuntimeException("WTF")
      }
    case SA.Term.Match(scrut, binder, motive, cases, sp) =>
      CA.Term.Match(
        elab(scrut),
        elab(binder),
        elab(motive),
        cases.map(c => CA.Case(c.ctorName, c.argNames, elab(c.body), c.span)),
        sp
      )
  }

  private def elab(b: SA.Binder): CA.Binder = CA.Binder(b.name, elab(b.ty), b.span)

  private def getType(header: SA.FuncHeader): CA.TypeTerm = {
    val outTy = elab(header.ty)
    if (header.params.isEmpty) outTy
    else CoreAst.Term.Pi(NEL.mk(header.params.map(elab)), outTy, header.span)
  }

  def elab(surface: SurfaceAst.Decl): CoreAst.Decl = {
    surface match {
      case c: SurfaceAst.Decl.ConstDecl =>
        val typeTerm = getType(c.header.funcHeader)
        val body = c.body.map { b =>
          typeTerm match {
            case pi: CA.Term.Pi => CA.Term.Lam(pi, elab(b), c.span)
            case _ =>
              if (b.lets.nonEmpty) throw new RuntimeException("Can't do that")
              elab(b.out)
          }
        }
        CoreAst.Decl.ConstDecl(c.isInline, c.header.name, typeTerm, body, c.span)
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
