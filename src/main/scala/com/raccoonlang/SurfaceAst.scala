package com.raccoonlang

// Surface AST for RaccoonLang.  Will be elaborated into CoreAst.
// Types are terms: type positions have their own grammar in the parser, but produce ordinary
// Term nodes — "is a type" is a semantic judgment, not a syntactic class.
object SurfaceAst {

  sealed trait Term {
    def span: Span
  }

  sealed trait ConstBody {
    def span: Span
  }

  sealed trait DecreaseSpec {
    def span: Span
  }

  object ConstBody {
    final case class TermBody(term: Term) extends ConstBody {
      override def span: Span = term.span
    }

    final case class Builtin(span: Span) extends ConstBody
  }

  object DecreaseSpec {
    final case class Structural(arg: String, span: Span) extends DecreaseSpec
    final case class Lexicographic(args: Vector[String], span: Span) extends DecreaseSpec
    final case class Measure(term: Term, span: Span) extends DecreaseSpec
  }

  object Term {
    // Identifier
    final case class Ident(name: String, span: Span) extends Term

    final case class NatLit(value: BigInt, span: Span) extends Term

    // Projection: base.field
    final case class Select(base: Term, field: String, span: Span) extends Term

    // Pi (x: A) -> B x
    final case class Pi(binder: Binder, body: Term, span: Span) extends Term

    // Application: f(a)
    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term

    // Lambda: fun (x : A)(y: B): B => body
    final case class Lam(header: FuncHeader, body: Term, span: Span) extends Term

    final case class Match(
        scrut: Term,
        motive: Option[Term],
        cases: Vector[Case],
        span: Span
    ) extends Term

    // Let: let x := foo
    final case class Let(name: String, ty: Option[Term], value: Term, span: Span)

    sealed trait BodyStmt {
      def span: Span
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

  case class Binder(
      name: String,
      ty: Term,
      span: Span,
      isImplicit: Boolean = false
  )

  case class FuncHeader(params: Vector[Binder], ty: Term, span: Span)

  case class Import(path: Vector[String], span: Span)

  sealed trait Command

  object Command {

    case class InductiveHeader(
        name: String,
        params: Vector[Binder],
        indices: Vector[Binder],
        resultTy: Term,
        span: Span
    ) {
      def binders: Vector[Binder] = params ++ indices
    }

    case class ConstructorDecl(
        name: String,
        binders: Vector[Binder],
        resultTy: Term,
        span: Span
    )

    // Global declarations and environment entries
    sealed trait Decl extends Command

    object Decl {
      // Constant: name : type [:= value]. Opaque definitions keep only their symbolic head in the environment.
      final case class ConstDecl(
          isOpaque: Boolean,
          header: DeclHeader,
          decreases: Option[DecreaseSpec],
          body: ConstBody,
          span: Span,
          lazyGlobal: Boolean = false
      ) extends Decl

      final case class AxiomDecl(
          header: DeclHeader,
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
