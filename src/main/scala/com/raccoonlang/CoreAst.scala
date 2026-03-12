package com.raccoonlang

import com.raccoonlang.Util.NEL
// Core AST for RaccoonCore (trusted kernel language)

object CoreAst {

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

  // Terms that can appear in function bodies
  sealed trait Term {
    def span: Span

    override def toString: String = PrettyPrinter.printTerm(this)
  }

  sealed trait TypeTerm extends Term // Terms that can appear in type expressions

  object Term {
    // Identifier (either type or term)
    final case class Ident(name: String, span: Span) extends Term with TypeTerm

    // Application in type position
    final case class TApp(fn: TypeTerm, args: NEL[TypeTerm], span: Span) extends TypeTerm

    // Pi (x: A) -> B x
    final case class Pi(binders: NEL[Binder], out: TypeTerm, span: Span) extends TypeTerm

    // Application: f a (term-level)
    final case class App(fn: Term, args: NEL[Term], span: Span) extends Term

    case class Body(lets: Vector[Let], res: Term, span: Span) extends Term

    // Lambda: fun (x : A): B => body
    final case class Lam(ty: Pi, body: Term, span: Span, name: Option[String], isStable: Boolean) extends Term

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
    final case class ConstDecl(
        unfoldStrategy: Option[UnfoldStrategy],
        name: String,
        ty: TypeTerm,
        body: Term,
        span: Span
    ) extends Decl

    // Inductive type declaration
    final case class InductiveDecl(name: String, ty: TypeTerm, ctors: Vector[Constructor], span: Span) extends Decl
  }

  case class Program(decls: Vector[Decl], body: Term)
}
