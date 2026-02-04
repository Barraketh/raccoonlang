package com.raccoonlang
// Core AST for RaccoonCore (trusted kernel language)

object CoreAst {

  sealed trait Term // Terms that can appear in function bodies
  sealed trait TypeTerm // Terms that can appear in type expressions

  object Term {
    // Identifier (either type or term)
    final case class Ident(name: String) extends Term with TypeTerm

    final case class TypeVar(name: String) extends TypeTerm

    // Application in type position
    final case class TApp(fn: TypeTerm, arg: TypeTerm) extends TypeTerm

    // Pi (x: A) -> B x
    final case class Pi(binder: Binder, body: TypeTerm) extends TypeTerm

    // Application: f a (term-level)
    final case class App(fn: Term, arg: Term) extends Term

    // Lambda: fun (x : A): B => body
    final case class Lam(binder: Binder, body: Body) extends Term

    final case class Match(
        scrut: Term,
        scrutName: String,
        motive: TypeTerm,
        cases: Vector[Case]
    ) extends Term
  }

  // Let: let x := foo
  final case class Let(name: String, ty: Option[TypeTerm], value: Term)

  case class Body(lets: Vector[Let], res: Term)

  case class Binder(name: String, ty: TypeTerm)

  case class Constructor(name: String, ty: TypeTerm)

  case class Case(ctorName: String, argNames: Vector[String], body: Term)

  // Global declarations and environment entries
  sealed trait Decl

  object Decl {
    // Constant: name : type [:= value], with transparency (Opaque | Inline)
    final case class ConstDecl(isInline: Boolean, name: String, ty: TypeTerm, body: Option[Body]) extends Decl

    // Inductive type declaration
    final case class InductiveDecl(name: String, ty: TypeTerm, ctors: Vector[Constructor]) extends Decl
  }

  case class Program(decls: Vector[Decl], body: Body)
}
