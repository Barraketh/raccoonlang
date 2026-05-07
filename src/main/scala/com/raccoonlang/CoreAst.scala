package com.raccoonlang

import com.raccoonlang.Util.NEL
// Core AST for RaccoonCore (trusted kernel language)

object CoreAst {
  final case class LocalRef(id: Int, name: String)

  // Raw terms come from the surface elaborator. Checked terms are produced by the typechecker and have derived
  // arguments inserted, so the interpreter can evaluate them without performing elaboration or instance search.
  sealed trait Phase
  sealed trait Raw extends Phase
  sealed trait Checked extends Phase

  type RawTerm = Term[Raw]
  type RawTypePattern = TypePattern[Raw]
  type RawTypeTerm = TypeTerm[Raw]
  type RawRef = Term.Ref[Raw]
  type RawBinder = Binder[Raw]
  type RawLet = Let[Raw]
  type RawCase = Case[Raw]

  type CheckedTerm = Term[Checked]
  type CheckedTypePattern = TypePattern[Checked]
  type CheckedTypeTerm = TypeTerm[Checked]
  type CheckedRef = Term.Ref[Checked]
  type CheckedBinder = Binder[Checked]
  type CheckedLet = Let[Checked]
  type CheckedCase = Case[Checked]

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
  sealed trait Term[+P <: Phase] {
    def span: Span

    override def toString: String = PrettyPrinter.printTerm(this)
  }

  // Terms that can appear in args
  sealed trait TypePattern[+P <: Phase] {
    def span: Span
  }

  // Terms that can appear in type expressions
  sealed trait TypeTerm[+P <: Phase] extends Term[P]

  object TypePattern {
    final case class Type[P <: Phase](term: TypeTerm[P]) extends TypePattern[P] {
      override def span: Span = term.span
    }

    final case class App[P <: Phase](fn: Term.Ref[P], args: NEL[TypePattern[P]], span: Span)
      extends TypePattern[P]

    final case class Capture[P <: Phase](localRef: CoreAst.LocalRef, span: Span) extends TypePattern[P]
  }

  object Term {
    sealed trait Ref[+P <: Phase] extends Term[P] with TypeTerm[P]

    final case class GlobalRef[P <: Phase](name: String, span: Span) extends Ref[P]

    final case class LocalRef[P <: Phase](ref: CoreAst.LocalRef, span: Span) extends Ref[P]

    // Projection in type position: base[field]
    final case class TSelect[P <: Phase](base: TypeTerm[P], field: String, span: Span) extends TypeTerm[P]

    // Projection in term position. This also appears in checked type terms after typechecking type-position selects.
    final case class Select[P <: Phase](base: Term[P], field: String, span: Span) extends Term[P] with TypeTerm[P]

    // Application in type position
    final case class TApp[P <: Phase](fn: Ref[P], args: NEL[TypeTerm[P]], span: Span) extends TypeTerm[P]

    // Pi (x: A) -> B x
    final case class Pi[P <: Phase](binders: NEL[Binder[P]], out: TypeTerm[P], span: Span)
      extends Term[P]
      with TypeTerm[P]

    // Application. This also appears in checked type terms after derived arguments have been inserted.
    final case class App[P <: Phase](fn: Term[P], args: Vector[Term[P]], span: Span) extends Term[P] with TypeTerm[P]

    case class Body[P <: Phase](lets: Vector[Let[P]], res: Term[P], span: Span) extends Term[P]

    // Lambda: fun (x : A): B => body
    final case class Lam[P <: Phase](
        ty: Pi[P],
        uses: Vector[Use[P]],
        body: Term[P],
        span: Span,
        name: Option[String],
        isStable: Boolean
    ) extends Term[P]

    final case class Match[P <: Phase](
        scrut: Term[P],
        motive: Option[TypeTerm[P]],
        cases: Vector[Case[P]],
        span: Span
    ) extends Term[P]

  }

  // Let: let x := foo
  final case class Let[P <: Phase](
      localRef: LocalRef,
      ty: Option[TypeTerm[P]],
      value: Term[P],
      span: Span,
      isInstance: Boolean = false
  ) {
    def name: String = localRef.name
  }

  // Use directive (first-class normalizer application)
  final case class Use[P <: Phase](normalizer: Term[P], span: Span)

  case class Binder[P <: Phase](
      localRef: LocalRef,
      ty: TypePattern[P],
      span: Span,
      isDerived: Boolean = false,
      isInstance: Boolean = false
  ) {
    require(!isDerived || isInstance, "Derived binders must participate in local instance search")

    def name: String = localRef.name

    override def toString: String = PrettyPrinter.printBinder(this)
  }

  case class InductiveHeader(
      name: String,
      params: Vector[RawBinder],
      indices: Vector[RawBinder],
      resultTy: RawTypeTerm,
      span: Span
  ) {
    def arity: Int = params.length + indices.length
  }

  case class ConstructorDecl(
      name: String,
      fields: Vector[RawBinder],
      resultTy: RawTypeTerm,
      span: Span
  )

  case class Case[P <: Phase](ctorName: String, argRefs: Vector[Option[LocalRef]], body: Term[P], span: Span)

  // Global declarations and environment entries
  sealed trait Decl {
    def span: Span
  }

  object Decl {
    // Constant: name : type [:= value], with transparency (Opaque | Inline)
    final case class ConstDecl(
        unfoldStrategy: Option[UnfoldStrategy],
        name: String,
        ty: TypeTerm[Raw],
        body: Term[Raw],
        span: Span,
        isInstance: Boolean = false
    ) extends Decl

    // Inductive type declaration (structured)
    final case class InductiveDecl(
        header: InductiveHeader,
        ctors: Vector[ConstructorDecl],
        isStruct: Boolean,
        span: Span
    ) extends Decl
  }

  case class Program(decls: Vector[Decl], body: Option[RawTerm])
}
