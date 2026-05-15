package com.raccoonlang

import com.raccoonlang.CoreAst.UnfoldStrategy

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

  sealed trait TypePattern {
    def span: Span
  }

  sealed trait TopLevelTP extends TypePattern

  object TypePattern {
    final case class Type(term: TypeTerm) extends TopLevelTP {
      override def span: Span = term.span
    }

    final case class App(fn: TypeTerm, args: Vector[TypePattern], span: Span) extends TopLevelTP {
      require(args.nonEmpty, "Type pattern application requires at least one argument")
    }

    final case class Capture(name: String, span: Span) extends TypePattern
  }

  sealed trait BinderType {
    def span: Span
  }

  object BinderType {
    final case class TypePattern(tp: TopLevelTP, span: Span) extends BinderType
    final case class ConstrainedCapture(name: String, constraint: TopLevelTP, span: Span) extends BinderType
  }

  object Term {
    // Identifier (either type or term)
    final case class Ident(name: String, span: Span) extends Term with TypeTerm

    // Projection: base[field]
    final case class TSelect(base: TypeTerm, field: String, span: Span) extends TypeTerm
    final case class Select(base: Term, field: String, span: Span) extends Term

    // Application in type position
    final case class TApp(fn: TypeTerm, args: Vector[TypeTerm], span: Span) extends TypeTerm {
      require(args.nonEmpty, "Type application requires at least one argument")
    }

    // Pi (x: A) -> B x
    final case class Pi(binder: Binder, body: TypeTerm, span: Span) extends Term with TypeTerm

    // Explicit instance search expression: derive[Goal]
    final case class Derive(goal: TypeTerm, span: Span) extends Term

    // Application: f(a) (term-level)
    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term

    // Lambda: fun (x : A)(y: B): B => body
    final case class Lam(header: FuncHeader, body: Term, span: Span) extends Term

    final case class Match(
        scrut: Term,
        motive: Option[TypeTerm],
        cases: Vector[Case],
        span: Span
    ) extends Term

    // Let: let x := foo
    final case class Let(name: String, ty: Option[TypeTerm], value: Term, span: Span, isInstance: Boolean = false)

    sealed trait BodyStmt {
      def span: Span
    }
    final case class UseStmt(use: Use) extends BodyStmt {
      override def span: Span = use.span
    }
    final case class OpenStmt(open: Command.Open) extends BodyStmt {
      override def span: Span = open.span
    }
    final case class LetStmt(let: Let) extends BodyStmt {
      override def span: Span = let.span
    }
    final case class Body(statements: Vector[BodyStmt], out: Term, span: Span) extends Term
    final case class Case(
        ctorPath: Vector[String],
        useShortName: Boolean,
        argNames: Vector[String],
        body: Term,
        span: Span
    )
  }

  // Use a first-class normalizer value within a body scope
  final case class Use(normalizer: Term, span: Span)

  case class Binder(name: String, ty: BinderType, span: Span, isInstance: Boolean = false)

  case class FuncHeader(params: Vector[Binder], ty: TypeTerm, span: Span)

  case class Import(path: Vector[String], span: Span)

  sealed trait Command

  object Command {

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

    // Global declarations and environment entries
    sealed trait Decl extends Command

    object Decl {
      // Constant: name : type [:= value], with transparency (Opaque | Inline)
      final case class ConstDecl(
          unfoldStrategy: Option[UnfoldStrategy],
          header: DeclHeader,
          body: Term,
          span: Span,
          isInstance: Boolean = false
      ) extends Decl

      final case class AxiomDecl(
          header: DeclHeader,
          span: Span,
          isInstance: Boolean = false
      ) extends Decl

      // Inductive type declaration
      final case class InductiveDecl(
          header: InductiveHeader,
          ctors: Vector[ConstructorDecl],
          isStruct: Boolean,
          span: Span
      ) extends Decl
    }

    case class Namespace(path: Vector[String], body: Vector[Command], span: Span) extends Command

    case class Open(namespace: Vector[String], root: Boolean, rules: Vector[AliasRule], span: Span) extends Command

    case class Block(body: Vector[Command], span: Span) extends Command

    sealed trait AliasRule
    object AliasRule {
      case object Wildcard extends AliasRule
      final case class Include(name: String, as: Option[String]) extends AliasRule
      final case class Exclude(name: String) extends AliasRule
    }

    case class DeclHeader(name: String, funcHeader: FuncHeader, span: Span)
  }

  case class Program(imports: Vector[Import], decls: Vector[Command], body: Option[Term])

}
