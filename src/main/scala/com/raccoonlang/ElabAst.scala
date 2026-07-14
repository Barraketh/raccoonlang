package com.raccoonlang

// Checked AST. Instance search expressions have already been resolved, and all local names are CoreAst.LocalRefs.
object ElabAst {
  sealed trait Ast {
    def span: Span

    override def toString: String = PrettyPrinter.printElabTerm(this)
  }

  sealed trait Term extends Ast

  sealed trait TypeTerm extends Term

  object Term {
    sealed trait Ref extends Term with TypeTerm

    final case class GlobalRef(name: String, span: Span) extends Ref

    final case class LocalRef(ref: CoreAst.LocalRef, span: Span) extends Ref

    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term with TypeTerm

    // No classifier field: a Pi's universe is env-dependent (level-polymorphic binder types), so
    // it is derived at evaluation time (Interpreter.piClassifier), never baked into the residual.
    final case class Pi(
        binders: Vector[Binder],
        out: TypeTerm,
        span: Span,
        nodeId: AstNodeId
    ) extends Term
      with TypeTerm {
      require(binders.nonEmpty, "Pi requires at least one binder")
    }

    final case class Body(lets: Vector[Let], res: Term, span: Span) extends Term

    final case class Lam(
        ty: Pi,
        body: Term,
        span: Span,
        name: Option[String],
        recursiveSelf: Option[CoreAst.LocalRef],
        nodeId: AstNodeId
    ) extends Term

    final case class Match(
        scrut: Term,
        motive: Option[TypeTerm],
        cases: Vector[Case],
        span: Span,
        nodeId: AstNodeId
    ) extends Term
  }

  // isImplicit binders are never present in checked App syntax: applications carry only the
  // explicit args, and evaluation reconstructs the implicits by running `projection` against them.
  final case class Binder(
      localRef: CoreAst.LocalRef,
      ty: TypeTerm,
      span: Span,
      isInstance: Boolean = false,
      isImplicit: Boolean = false,
      projection: Option[telescope.Projection.Spec] = None
  ) {
    def name: String = localRef.name

    override def toString: String = PrettyPrinter.printElabBinder(this)
  }

  final case class Let(
      localRef: CoreAst.LocalRef,
      ty: Option[TypeTerm],
      value: Term,
      span: Span,
      isInstance: Boolean = false
  ) {
    def name: String = localRef.name
  }

  final case class Case(ctorName: String, argRefs: Vector[Option[CoreAst.LocalRef]], body: Term, span: Span)
}
