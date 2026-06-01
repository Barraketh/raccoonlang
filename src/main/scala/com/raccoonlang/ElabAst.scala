package com.raccoonlang

import com.raccoonlang.Value.VSort

// Checked AST. Instance search expressions have already been resolved, and all local names are CoreAst.LocalRef slots.
object ElabAst {
  sealed trait Ast {
    def span: Span

    override def toString: String = PrettyPrinter.printElabTerm(this)
  }

  sealed trait Term extends Ast

  sealed trait TypePattern extends Ast

  sealed trait TopLevelTP extends TypePattern

  sealed trait TypeTerm extends Term

  object TypePattern {
    final case class Type(term: TypeTerm) extends TopLevelTP {
      override def span: Span = term.span
    }

    final case class App(fn: Term.Ref, args: Vector[TypePattern], span: Span) extends TopLevelTP {
      require(args.nonEmpty, "Type pattern application requires at least one argument")
    }

    final case class Capture(localRef: CoreAst.LocalRef, span: Span) extends TypePattern
  }

  sealed trait BinderType extends Ast

  object BinderType {
    final case class TypePattern(tp: TopLevelTP, span: Span) extends BinderType
    final case class ConstrainedCapture(localRef: CoreAst.LocalRef, constraint: TopLevelTP, span: Span)
      extends BinderType
  }

  object Term {
    sealed trait Ref extends Term with TypeTerm

    final case class GlobalRef(name: String, span: Span) extends Ref

    final case class LocalRef(ref: CoreAst.LocalRef, span: Span) extends Ref

    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term with TypeTerm

    final case class Pi(binders: Vector[Binder], out: TypeTerm, classifier: VSort, span: Span)
      extends Term
      with TypeTerm {
      require(binders.nonEmpty, "Pi requires at least one binder")
    }

    final case class Body(lets: Vector[Let], res: Term, span: Span) extends Term

    final case class Lam(
        ty: Pi,
        uses: Vector[Use],
        body: Term,
        span: Span,
        name: Option[String],
        isStable: Boolean,
        recursiveSelf: Option[CoreAst.LocalRef]
    ) extends Term

    final case class Match(
        scrut: Term,
        motive: Option[TypeTerm],
        cases: Vector[Case],
        span: Span
    ) extends Term
  }

  final case class Binder(
      localRef: CoreAst.LocalRef,
      ty: BinderType,
      span: Span,
      isInstance: Boolean = false
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

  final case class Use(normalizer: Term, span: Span)

  final case class Case(ctorName: String, argRefs: Vector[Option[CoreAst.LocalRef]], body: Term, span: Span)
}
