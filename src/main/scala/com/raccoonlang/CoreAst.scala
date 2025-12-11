package com.raccoonlang
// Core AST for RaccoonCore (trusted kernel language)
// Follows Kernel-Spec.md: levels, relevance, terms, cases, and global declarations.

object CoreAst {
  // Universe levels (non-cumulative)
  sealed trait Level

  object Level {
    final case class LNat(n: Int) extends Level

    final case class LSucc(l: Level) extends Level

    final case class LMax(a: Level, b: Level) extends Level
  }

  // Relevance of binders
  sealed trait Relevance

  object Relevance {
    case object Rel extends Relevance

    case object Irr extends Relevance
  }

  // Transparency for constants (delta-reduction policy)
  sealed trait Transparency

  object Transparency {
    case object Opaque extends Transparency

    case object Inline extends Transparency
  }

  // Kernel terms (de Bruijn indices for variables)
  sealed trait Term
  sealed trait TypeTerm extends Term

  object Term {
    // Variables by de Bruijn index
    final case class Var(index: Int) extends TypeTerm

    // Global constant reference (by name)
    final case class Const(name: String) extends TypeTerm

    // Universe: Type u
    final case class Type(level: Level) extends TypeTerm

    // Dependent function type: (x : A) -> B, with relevance
    final case class Pi(rel: Relevance, nameHint: String, ty: TypeTerm, body: TypeTerm) extends TypeTerm

    // Application: f a (term-level)
    final case class App(fn: Term, arg: Term) extends Term

    // Application in type position
    final case class TApp(fn: TypeTerm, arg: TypeTerm) extends TypeTerm

    // Lambda: \(x : A) => body, with relevance and stored binder type
    final case class Lam(rel: Relevance, nameHint: String, ty: TypeTerm, body: Term) extends Term

    // Let: let (rel x : A) := val in body
    final case class Let(rel: Relevance, nameHint: String, ty: TypeTerm, value: Term, body: Term) extends Term

    final case class Match(
        scrut: Term,
        scrutNameHint: String,
        motive: Motive,
        cases: List[Case]
    ) extends Term
  }

  // Structured motive for Match: lambda over scrutinee to a Type
  final case class Motive(rel: Relevance, nameHint: String, paramTy: TypeTerm, body: TypeTerm)

  // Case binder (used in Match cases)
  final case class Binder(rel: Relevance, name: String, ty: TypeTerm)

  // A Match case after index refinement: only remaining (non-forced) ctor args are bound
  final case class Case(ctorName: String, binders: List[Binder], body: Term)

  // Global declarations and environment entries
  sealed trait Decl

  object Decl {
    // Constant: name : type [:= value], with transparency (Opaque | Inline)
    final case class ConstDecl(
        name: String,
        ty: TypeTerm,
        value: Option[Term],
        transparency: Transparency
    ) extends Decl

    // Inductive type declaration
    final case class InductiveDecl(
        name: String,
        params: List[Binder],
        indices: List[Binder],
        universe: Level,
        ctors: List[CtorDecl]
    ) extends Decl
  }

  // Constructor declaration: its type must start with the inductive's parameter telescope
  final case class CtorDecl(name: String, ty: TypeTerm)

}
