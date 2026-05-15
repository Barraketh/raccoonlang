package com.raccoonlang
// Core AST for RaccoonCore (trusted kernel language)

object CoreAst {
  final case class LocalRef(id: Int, name: String)

  sealed trait UnfoldStrategy
  object UnfoldStrategy {
    // Unfold computation as far as you can and return the result
    case object Inline extends UnfoldStrategy

    // Try to unfold, but if the result is blocked and does not have a stable head then treat as opaque (which will
    // return VBlockedApp(thisFn, args), which WILL have a stable head since thisFn is stable. The goal of this strategy
    // is to allow normalizers to rewrite expressions - if foo calls bar calls baz, and the normalizers only knows about
    // foo then even if baz gets blocked, I want to return VBlockedApp(foo, ...).  Technically this information should
    // probably live on the normalizer itself, but that's more complicated to implement, so for now it will be a
    // property of the function, and we'll see if it causes any trouble.
    case object Stable extends UnfoldStrategy
  }

  sealed trait Ast {
    def span: Span

    override def toString: String = PrettyPrinter.printTerm(this)
  }

  // Terms that can appear in function bodies
  sealed trait Term extends Ast

  // Terms that can appear in args
  sealed trait TypePattern extends Ast

  sealed trait TopLevelTP extends TypePattern

  // Terms that can appear in type expressions
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

    // Projection in type position: base[field]
    final case class TSelect(base: TypeTerm, field: String, span: Span) extends TypeTerm

    // Projection in term position: base[field]
    final case class Select(base: Term, field: String, span: Span) extends Term

    // Explicit instance search expression: derive[Goal]
    final case class Derive(goal: TypeTerm, span: Span) extends Term

    // Application in type position
    final case class TApp(fn: Ref, args: Vector[TypeTerm], span: Span) extends TypeTerm {
      require(args.nonEmpty, "Type application requires at least one argument")
    }

    // Pi (x: A) -> B x
    final case class Pi(binders: Vector[Binder], out: TypeTerm, span: Span) extends Term with TypeTerm {
      require(binders.nonEmpty, "Pi requires at least one binder")
    }

    // Application: f(a) (term-level)
    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term

    final case class Body(lets: Vector[Let], res: Term, span: Span) extends Term

    // Lambda: fun (x : A): B => body
    final case class Lam(
        ty: Pi,
        uses: Vector[Use],
        body: Term,
        span: Span,
        name: Option[String],
        isStable: Boolean
    ) extends Term

    final case class Match(
        scrut: Term,
        motive: Option[TypeTerm],
        cases: Vector[Case],
        span: Span
    ) extends Term

  }

  // Let: let x := foo
  final case class Let(
      localRef: LocalRef,
      ty: Option[TypeTerm],
      value: Term,
      span: Span,
      isInstance: Boolean = false
  ) {
    def name: String = localRef.name
  }

  // Use directive (first-class normalizer application)
  final case class Use(normalizer: Term, span: Span)

  final case class Binder(
      localRef: LocalRef,
      ty: BinderType,
      span: Span,
      isInstance: Boolean = false
  ) {
    def name: String = localRef.name

    override def toString: String = PrettyPrinter.printBinder(this)
  }

  case class InductiveHeader(
      name: String,
      params: Vector[Binder],
      indices: Vector[Binder],
      resultTy: TypeTerm,
      span: Span
  ) {
    def arity: Int = params.length + indices.length
  }

  case class ConstructorDecl(
      canonicalName: String,
      shortName: String,
      fields: Vector[Binder],
      resultTy: TypeTerm,
      span: Span
  ) {
    def name: String = canonicalName
  }

  final case class Case(
      ctorName: String,
      isFullyQualified: Boolean,
      argRefs: Vector[Option[LocalRef]],
      body: Term,
      span: Span
  )

  // Global declarations and environment entries
  sealed trait Decl {
    def span: Span
  }

  object Decl {
    // Constant: name : type [:= value], with transparency (Opaque | Inline)
    final case class ConstDecl(
        unfoldStrategy: Option[UnfoldStrategy],
        name: String,
        ty: TypeTerm,
        body: Term,
        span: Span,
        isInstance: Boolean = false
    ) extends Decl

    final case class AxiomDecl(
        name: String,
        ty: TypeTerm,
        span: Span,
        isInstance: Boolean = false
    ) extends Decl

    // Inductive type declaration (structured)
    final case class InductiveDecl(
        header: InductiveHeader,
        ctors: Vector[ConstructorDecl],
        isStruct: Boolean,
        span: Span
    ) extends Decl
  }

  case class Program(decls: Vector[Decl], body: Option[Term])
}
