package com.raccoonlang

import com.raccoonlang.Util.NEL
// Core AST for RaccoonCore (trusted kernel language)

object CoreAst {

  // Terms that can appear in function bodies
  sealed trait Term {
    def span: Span
  }

  sealed trait TypeTerm extends Term // Terms that can appear in type expressions

  object Term {
    // Identifier (either type or term)
    final case class Ident(name: String, span: Span) extends Term with TypeTerm

    // Application in type position
    final case class TApp(fn: TypeTerm, args: NEL[TypeTerm], span: Span) extends TypeTerm

    // Pi (x: A) -> B x
    final case class Pi(binders: NEL[Binder], out: TypeTerm, span: Span) extends TypeTerm

    final case class Bind(name: String, span: Span) extends TypeTerm

    final case class NatLit(int: Int, span: Span) extends TypeTerm

    // Application: f a (term-level)
    final case class App(fn: Term, args: NEL[Term], span: Span) extends Term

    case class Body(lets: Vector[Let], res: Term, span: Span) extends Term

    // Lambda: fun (x : A): B => body
    final case class Lam(ty: Pi, body: Term, span: Span, name: Option[String]) extends Term

    final case class Match(
        scrut: Term,
        scrutName: String,
        motive: TypeTerm,
        cases: Vector[Case],
        span: Span
    ) extends Term
  }

  // Let: let x := foo
  final case class Let(name: String, ty: Option[TypeTerm], value: Term, span: Span)

  case class Binder(name: String, ty: TypeTerm, span: Span)

  case class Constructor(name: String, ty: TypeTerm, span: Span)

  case class Case(ctorName: String, argNames: Vector[String], body: Term, span: Span)

  // Global declarations and environment entries
  sealed trait Decl {
    def span: Span
  }

  object Decl {
    // Constant: name : type [:= value], with transparency (Opaque | Inline)
    final case class ConstDecl(isInline: Boolean, name: String, ty: TypeTerm, body: Option[Term], span: Span)
      extends Decl

    // Inductive type declaration
    final case class InductiveDecl(name: String, ty: TypeTerm, ctors: Vector[Constructor], span: Span) extends Decl
  }

  case class Program(decls: Vector[Decl], body: Term)
}
