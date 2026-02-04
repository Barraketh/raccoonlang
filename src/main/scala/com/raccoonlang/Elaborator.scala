package com.raccoonlang

object Elaborator {
  val SA = SurfaceAst
  val CA = CoreAst

  private def elab(ty: SA.TypeTerm): CA.TypeTerm = ty match {
    case SA.Term.Ident(name)      => CoreAst.Term.Ident(name)
    case SA.Term.TApp(fn, arg)    => CoreAst.Term.TApp(elab(fn), elab(arg))
    case SA.Term.Pi(binder, body) => CoreAst.Term.Pi(elab(binder), elab(body))
  }

  private def elab(body: SA.Body): CA.Body =
    CA.Body(body.lets.map(l => CA.Let(l.name, l.ty.map(elab), elab(l.value))), elab(body.out))

  private def elabLam(params: Vector[SA.Binder], body: SA.Body): CA.Term.Lam = {
    params.reverse.tail.foldLeft(CA.Term.Lam(elab(params.head), elab(body))) { case (acc, param) =>
      CA.Term.Lam(elab(param), CA.Body(Vector.empty, acc))
    }
  }

  private def elab(term: SurfaceAst.Term): CA.Term = term match {
    case SA.Term.Ident(name)       => CA.Term.Ident(name)
    case SA.Term.App(fn, arg)      => CA.Term.App(elab(fn), elab(arg))
    case SA.Term.Lam(params, body) => elabLam(params, body)
    case SA.Term.Match(scrut, scrutName, motive, cases) =>
      CA.Term.Match(elab(scrut), scrutName, elab(motive), cases.map(c => CA.Case(c.ctorName, c.argNames, elab(c.body))))
  }

  private def elab(b: SA.Binder): CA.Binder = CA.Binder(b.name, elab(b.ty))

  private def getType(header: SA.DeclHeader): CA.TypeTerm = {
    val caParams = header.params.map(elab)
    caParams.foldRight(elab(header.ty)) { case (param, acc) => CA.Term.Pi(param, acc) }
  }

  def elab(surface: SurfaceAst.Decl): CoreAst.Decl = {
    surface match {
      case c: SurfaceAst.Decl.ConstDecl =>
        val typeTerm = getType(c.header)
        val body = c.body.map { b =>
          c.header.params.foldRight(elab(b)) { case (binder, acc) =>
            CA.Body(Vector.empty, CA.Term.Lam(elab(binder), acc))
          }
        }
        CoreAst.Decl.ConstDecl(c.isInline, c.header.name, typeTerm, body)
      case c: SurfaceAst.Decl.InductiveDecl =>
        CoreAst.Decl.InductiveDecl(
          c.header.name,
          getType(c.header),
          c.ctors.map(ctor => CA.Constructor(c.header.name + "." + ctor.name, getType(ctor)))
        )
    }
  }

  def elab(p: SA.Program): CA.Program = CA.Program(p.decls.map(elab), elab(p.body))

}
