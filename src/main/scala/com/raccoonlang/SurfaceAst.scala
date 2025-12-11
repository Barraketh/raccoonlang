package com.raccoonlang
// Surface AST for RaccoonSurface (user language)
// Follows Parser-Spec.md: grammar, including inline modifier on defs, universe inference via `Type _`,
// explicit motives in matches, and optional (tooling-only) constructs.

object SurfaceAst {
  // Universe levels in surface syntax
  sealed trait SLevel

  object SLevel {
    final case class NatLit(n: Int) extends SLevel

    final case class Ident(name: String) extends SLevel

    final case class Succ(of: SLevel) extends SLevel

    final case class Max(a: SLevel, b: SLevel) extends SLevel
  }

  // Relevance of binders in surface syntax
  sealed trait SRelevance

  object SRelevance {
    case object Rel extends SRelevance

    case object Irr extends SRelevance
  }

  // Program
  final case class Program(decls: List[Decl])

  // Declarations
  sealed trait Decl

  object Decl {
    // data Name .{levels}? (params) : Type ... where { ctors }
    final case class Data(
        name: String,
        levelParams: List[String],
        params: List[Binder],
        resultType: TypeTerm,
        ctors: List[Ctor]
    ) extends Decl

    // inline? def Name .{levels}? (params) : T := body
    final case class Def(
        isInline: Boolean,
        name: String,
        levelParams: List[String],
        params: List[Binder],
        resultType: TypeTerm,
        body: Term
    ) extends Decl

    // theorem Name .{levels}? (params) : T := body
    final case class Theorem(
        name: String,
        levelParams: List[String],
        params: List[Binder],
        resultType: TypeTerm,
        body: Term
    ) extends Decl

    // axiom Name .{levels}? (params) : T
    final case class Axiom(
        name: String,
        levelParams: List[String],
        params: List[Binder],
        resultType: TypeTerm
    ) extends Decl
  }

  // Constructor inside a data declaration
  final case class Ctor(name: String, binders: List[Binder], ty: TypeTerm)

  // Binder
  final case class Binder(rel: SRelevance, name: String, ty: TypeTerm)

  // Patterns used in match cases (indices forced by refinement; no explicit index bindings)
  sealed trait Pattern

  object Pattern {
    final case class Ctor(name: String, binders: List[String]) extends Pattern
  }

  // Surface terms
  sealed trait Term
  sealed trait TypeTerm extends Term

  object Term {
    // Identifiers (variables, constants before resolution)
    final case class Ident(name: String) extends Term with TypeTerm

    // Type u (explicit level)
    final case class Type(level: SLevel) extends Term with TypeTerm

    // Type _ (fresh universe variable to be inferred)
    case object TypeHole extends Term with TypeTerm

    // Lambda: \(binder) => body
    final case class Lam(binder: Binder, body: Term) extends Term

    // Forall: forall (binder) -> body
    final case class Forall(binder: Binder, body: TypeTerm) extends Term with TypeTerm

    // Application: f a
    final case class App(fn: Term, arg: Term) extends Term with TypeTerm

    // Let: let x : T := v in body (always relevant in surface)
    final case class Let(name: String, ty: TypeTerm, value: Term, in: Term) extends Term

    // Ascription: (t : T)
    final case class Ascribe(term: Term, ty: TypeTerm) extends Term

    // Match: match scrut as w returning R with { cases }
    final case class Match(
        scrut: Term,
        asName: String,
        returning: TypeTerm,
        cases: List[Case]
    ) extends Term

    // Optional tooling-only constructs (not in kernel)
    // implicit[T]
    final case class ImplicitSite(goal: Term) extends Term

    // Named hole: ?h
    final case class Hole(name: String) extends Term
  }

  // Match case
  final case class Case(pattern: Pattern, body: Term)
}
