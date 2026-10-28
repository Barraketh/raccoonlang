package com.raccoonlang
// Core AST for RaccoonCore (trusted kernel language)

object CoreAst {
  final case class LocalRef(id: Int, name: String)

  sealed trait Ast {
    def span: Span

    override def toString: String = PrettyPrinter.printTerm(this)
  }

  // Terms that can appear in function bodies
  sealed trait Term extends Ast

  // Terms that can appear in args
  sealed trait TypePattern extends Ast

  sealed trait TopLevelTP extends TypePattern

  sealed trait ConstBody {
    def span: Span
  }

  sealed trait DecreaseSpec extends Ast

  object ConstBody {
    final case class TermBody(term: Term) extends ConstBody {
      override def span: Span = term.span
    }

    final case class Builtin(span: Span) extends ConstBody
  }

  object DecreaseSpec {
    final case class Lexicographic(args: Vector[LocalRef], span: Span) extends DecreaseSpec
    final case class Measure(term: Term, span: Span) extends DecreaseSpec
  }

  final case class Recursion(selfRef: LocalRef, decreases: DecreaseSpec)

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

    // String literal: its decoded text, which holds only Unicode scalar values
    final case class StrLit(text: String, span: Span) extends TypeTerm

    // Projection in either term or type position: base[field]
    final case class Select(base: Term, field: String, span: Span) extends Term with TypeTerm

    // Explicit instance search expression: derive[Goal]
    final case class Derive(goal: TypeTerm, span: Span) extends TypeTerm

    // Pi (x: A) -> B x
    final case class Pi(binders: Vector[Binder], out: TypeTerm, span: Span, nodeId: NodeId) extends Term with TypeTerm {
      require(binders.nonEmpty, "Pi requires at least one binder")
    }

    // Application in either term or type position.
    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term with TypeTerm

    final case class Body(lets: Vector[Let], res: Term, span: Span) extends Term

    // Lambda: fun (x : A): B => body
    final case class Lam(
        ty: Pi,
        uses: Vector[Use],
        body: Term,
        span: Span,
        name: Option[String],
        recursion: Option[Recursion],
        nodeId: NodeId
    ) extends Term

    sealed trait MatchTerm extends Term {
      def scrut: Term
      def motive: Option[TypeTerm]
      def span: Span
      def nodeId: NodeId
    }

    final case class Match(
        scrut: Term,
        motive: Option[TypeTerm],
        cases: Vector[Case],
        span: Span,
        nodeId: NodeId
    ) extends MatchTerm

    final case class MatchOne(
        scrut: Term,
        motive: Option[TypeTerm],
        fieldRefs: Vector[CoreAst.LocalRef],
        body: Term,
        span: Span,
        nodeId: NodeId
    ) extends MatchTerm

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
    def binders: Vector[Binder] = params ++ indices
    def arity: Int = params.length + indices.length
  }

  case class ConstructorDecl(
      canonicalName: String,
      shortName: String,
      erasedBinders: Vector[Binder],
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
    // Constant: name : type [:= value]. None means explicitly opaque; term definitions otherwise default to Inline.
    final case class ConstDecl(
        name: String,
        ty: TypeTerm,
        body: ConstBody,
        span: Span,
        isInstance: Boolean = false,
        lazyGlobal: Boolean = false
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
