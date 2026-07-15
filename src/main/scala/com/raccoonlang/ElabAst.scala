package com.raccoonlang

// Checked AST. All local names are CoreAst.LocalRefs. Types are terms — binder types, let
// annotations, and match motives are ordinary Terms; "is a type" was verified by the checker.
object ElabAst {
  sealed trait Ast {
    def span: Span

    override def toString: String = PrettyPrinter.printElabTerm(this)
  }

  sealed trait Term extends Ast

  object Term {
    sealed trait Ref extends Term

    final case class GlobalRef(name: String, span: Span) extends Ref

    final case class LocalRef(ref: CoreAst.LocalRef, span: Span) extends Ref

    final case class NatLit(value: BigInt, span: Span) extends Term

    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term

    // No classifier field: a Pi's universe is env-dependent (level-polymorphic binder types), so
    // it is derived at evaluation time (Interpreter.piClassifier), never baked into the residual.
    final case class Pi(
        binders: Vector[Binder],
        out: Term,
        span: Span,
        nodeId: AstNodeId
    ) extends Term {
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
        motive: Option[Term],
        cases: Vector[Case],
        span: Span,
        nodeId: AstNodeId
    ) extends Term
  }

  // isImplicit binders are never present in checked App syntax: applications carry only the
  // explicit args, and evaluation reconstructs the implicits by running `projection` against them.
  final case class Binder(
      localRef: CoreAst.LocalRef,
      ty: Term,
      span: Span,
      isImplicit: Boolean = false,
      projection: Option[telescope.Projection.Spec] = None
  ) {
    def name: String = localRef.name

    override def toString: String = PrettyPrinter.printElabBinder(this)
  }

  final case class Let(
      localRef: CoreAst.LocalRef,
      ty: Option[Term],
      value: Term,
      span: Span
  ) {
    def name: String = localRef.name
  }

  final case class Case(ctorName: String, argRefs: Vector[Option[CoreAst.LocalRef]], body: Term, span: Span)
}
