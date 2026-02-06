package com.raccoonlang

import com.raccoonlang.Util.NEL

// Surface AST for RaccoonLang.  Will be elaborated into CoareAst
object SurfaceAst {

  sealed trait Term // Terms that can appear in function bodies
  sealed trait TypeTerm // Terms that can appear in type expressions

  object Term {
    // Identifier (either type or term)
    final case class Ident(name: String) extends Term with TypeTerm

    // Application in type position
    final case class TApp(fn: TypeTerm, args: NEL[TypeTerm]) extends TypeTerm

    // Pi (x: A) -> B x
    final case class Pi(binder: Binder, body: TypeTerm) extends TypeTerm

    // Application: f a (term-level)
    final case class App(fn: Term, args: NEL[Term]) extends Term

    // Lambda: fun (x : A)(y: B): B => body
    final case class Lam(header: FuncHeader, body: Body) extends Term

    final case class Match(
        scrut: Term,
        scrutName: String,
        motive: TypeTerm,
        cases: Vector[Case]
    ) extends Term
  }

  // Let: let x := foo
  final case class Let(name: String, ty: Option[TypeTerm], value: Term)

  case class Body(lets: Vector[Let], out: Term)

  case class Binder(name: String, ty: TypeTerm)

  case class FuncHeader(params: Vector[Binder], ty: TypeTerm)

  case class DeclHeader(name: String, funcHeader: FuncHeader)

  case class Case(ctorName: String, argNames: Vector[String], body: Term)

  // Global declarations and environment entries
  sealed trait Decl

  object Decl {
    // Constant: name : type [:= value], with transparency (Opaque | Inline)
    final case class ConstDecl(isInline: Boolean, header: DeclHeader, body: Option[Body]) extends Decl

    // Inductive type declaration
    final case class InductiveDecl(header: DeclHeader, ctors: Vector[DeclHeader]) extends Decl
  }

  case class Program(decls: Vector[Decl], body: Body)

}
