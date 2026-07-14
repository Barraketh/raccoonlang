package com.raccoonlang
// Core AST for RaccoonCore (trusted kernel language).
// Types are terms: "is a type" is a semantic judgment (TypeChecker.assertType), not a syntactic
// class, so binder types, motives, and declared types are ordinary Terms.

object CoreAst {
  final case class LocalRef(id: Int, name: String)

  sealed trait Ast {
    def span: Span

    override def toString: String = PrettyPrinter.printTerm(this)
  }

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

  object Term {
    sealed trait Ref extends Term

    final case class GlobalRef(name: String, span: Span) extends Ref

    final case class LocalRef(ref: CoreAst.LocalRef, span: Span) extends Ref

    // Projection: base[field]
    final case class Select(base: Term, field: String, span: Span) extends Term

    // Pi (x: A) -> B x
    final case class Pi(binders: Vector[Binder], out: Term, span: Span) extends Term {
      require(binders.nonEmpty, "Pi requires at least one binder")
    }

    // Application: f(a)
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
        motive: Option[Term],
        cases: Vector[Case],
        span: Span
    ) extends Term

  }

  // Let: let x := foo
  final case class Let(
      localRef: LocalRef,
      ty: Option[Term],
      value: Term,
      span: Span
  ) {
    def name: String = localRef.name
  }

  final case class Binder(
      localRef: LocalRef,
      ty: Term,
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
      resultTy: Term,
      span: Span
  ) {
    def binders: Vector[Binder] = params ++ indices
    def arity: Int = params.length + indices.length
  }

  case class ConstructorDecl(
      canonicalName: String,
      shortName: String,
      binders: Vector[Binder],
      resultTy: Term,
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
        ty: Term,
        body: ConstBody,
        span: Span,
        lazyGlobal: Boolean = false
    ) extends Decl

    final case class AxiomDecl(
        name: String,
        ty: Term,
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
