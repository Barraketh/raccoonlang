package com.raccoonlang

import com.raccoonlang.CoreAst.UnfoldStrategy
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

    // Projection: base[field]
    final case class TSelect(base: TypeTerm, field: String, span: Span) extends TypeTerm
    final case class Select(base: Term, field: String, span: Span) extends Term

    // Application in type position
    final case class TApp(fn: Ident, args: NEL[TypeTerm], span: Span) extends TypeTerm

    // Pi (x: A) -> B x
    final case class Pi(binder: Binder, body: TypeTerm, span: Span) extends Term with TypeTerm

    // Capture: `$name` binds a fresh variable in the type pattern
    final case class Capture(name: String, span: Span) extends TypeTerm

    // Application: f(a) (term-level)
    final case class App(fn: Term, args: NEL[Term], span: Span) extends Term

    // Lambda: fun (x : A)(y: B): B => body
    final case class Lam(header: FuncHeader, body: Term, span: Span) extends Term

    final case class Match(
        scrut: Term,
        motive: Option[TypeTerm],
        cases: Vector[Case],
        span: Span
    ) extends Term

    case class Body(uses: Vector[Use], lets: Vector[Let], out: Term, span: Span) extends Term
  }

  // Use a first-class normalizer value within a body scope
  final case class Use(normalizer: Term, span: Span)

  // Let: let x := foo
  final case class Let(name: String, ty: Option[TypeTerm], value: Term, span: Span)

  case class Binder(name: String, ty: TypeTerm, span: Span)

  case class FuncHeader(params: Vector[Binder], ty: TypeTerm, span: Span)

  case class DeclHeader(name: String, funcHeader: FuncHeader, span: Span)

  case class InductiveHeader(
      name: String,
      params: Vector[Binder],
      indices: Vector[Binder],
      resultTy: TypeTerm,
      span: Span
  )

  case class ConstructorDecl(
      name: String,
      fields: Vector[Binder],
      resultTy: TypeTerm,
      span: Span
  )

  case class Case(ctorName: String, argNames: Vector[String], body: Term, span: Span)

  // Global declarations and environment entries
  sealed trait Decl

  object Decl {
    // Constant: name : type [:= value], with transparency (Opaque | Inline)
    final case class ConstDecl(
        unfoldStrategy: Option[UnfoldStrategy],
        header: DeclHeader,
        body: Term,
        span: Span
    ) extends Decl

    // Inductive type declaration
    final case class InductiveDecl(
        header: InductiveHeader,
        ctors: Vector[ConstructorDecl],
        isStruct: Boolean,
        span: Span
    ) extends Decl
  }

  case class Program(decls: Vector[Decl], body: Option[Term])

}
