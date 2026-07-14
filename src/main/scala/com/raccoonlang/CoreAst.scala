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

  object Term {
    sealed trait Ref extends Term with TypeTerm

    final case class GlobalRef(name: String, span: Span) extends Ref

    final case class LocalRef(ref: CoreAst.LocalRef, span: Span) extends Ref

    // Projection in type position: base[field]
    final case class TSelect(base: TypeTerm, field: String, span: Span) extends TypeTerm

    // Projection in term position: base[field]
    final case class Select(base: Term, field: String, span: Span) extends Term

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
        body: Term,
        span: Span,
        name: Option[String],
        recursion: Option[Recursion]
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
      span: Span
  ) {
    def name: String = localRef.name
  }

  final case class Binder(
      localRef: LocalRef,
      ty: TypeTerm,
      span: Span,
      isImplicit: Boolean = false
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
      binders: Vector[Binder],
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
    // Constant: name : type [:= value]. Opaque definitions keep only their symbolic head in the environment.
    final case class ConstDecl(
        isOpaque: Boolean,
        name: String,
        ty: TypeTerm,
        body: ConstBody,
        span: Span,
        lazyGlobal: Boolean = false
    ) extends Decl

    final case class AxiomDecl(
        name: String,
        ty: TypeTerm,
        span: Span
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
