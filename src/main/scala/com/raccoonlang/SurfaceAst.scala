package com.raccoonlang

import com.raccoonlang.Util.NEL

// Surface AST for RaccoonLang.  Will be elaborated into CoareAst
object SurfaceAst {

  // Terms that can appear in function bodies
  sealed trait Term {
    def span: Span
  }

  // Terms that can appear in type expressions
  sealed trait TypeTerm {
    def span: Span
  }

  object Term {
    // Identifier (either type or term)
    final case class Ident(name: String, span: Span) extends Term with TypeTerm

    // Application in type position
    final case class TApp(fn: TypeTerm, args: NEL[TypeTerm], span: Span) extends TypeTerm

    // Pi (x: A) -> B x
    final case class Pi(binder: Binder, body: TypeTerm, span: Span) extends TypeTerm

    // Application: f a (term-level)
    final case class App(fn: Term, args: NEL[Term], span: Span) extends Term

    // Lambda: fun (x : A)(y: B): B => body
    final case class Lam(header: FuncHeader, body: Term, span: Span) extends Term

    final case class Match(
        scrut: Term,
        binder: Binder,
        motive: TypeTerm,
        cases: Vector[Case],
        span: Span
    ) extends Term

    case class Body(lets: Vector[Let], out: Term, span: Span) extends Term
  }

  // Let: let x := foo
  final case class Let(name: String, ty: Option[TypeTerm], value: Term, span: Span)

  case class Binder(name: String, ty: TypeTerm, span: Span)

  case class FuncHeader(params: Vector[Binder], ty: TypeTerm, span: Span)

  case class DeclHeader(name: String, funcHeader: FuncHeader, span: Span)

  case class Case(ctorName: String, argNames: Vector[String], body: Term, span: Span)

  // Global declarations and environment entries
  sealed trait Decl

  object Decl {
    // Constant: name : type [:= value], with transparency (Opaque | Inline)
    final case class ConstDecl(isInline: Boolean, header: DeclHeader, body: Option[Term], span: Span) extends Decl

    // Inductive type declaration
    final case class InductiveDecl(header: DeclHeader, ctors: Vector[DeclHeader], span: Span) extends Decl
  }

  case class Program(decls: Vector[Decl], body: Term)

}
