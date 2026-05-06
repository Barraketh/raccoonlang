package com.raccoonlang

import com.raccoonlang.Util.NEL

// Checked AST. Applications in this tree are fully elaborated: derived arguments
// have already been inserted, and all local names are CoreAst.LocalRef slots.
object ElabAst {
  sealed trait Ast {
    def span: Span

    override def toString: String = PrettyPrinter.printElabTerm(this)
  }

  sealed trait Term extends Ast

  sealed trait TypePattern extends Ast

  sealed trait TypeTerm extends Term with TypePattern

  object Term {
    sealed trait Ref extends TypeTerm

    final case class GlobalRef(name: String, span: Span) extends Ref

    final case class LocalRef(ref: CoreAst.LocalRef, span: Span) extends Ref

    final case class Select(base: Term, field: String, span: Span) extends TypeTerm

    final case class App(fn: Term, args: Vector[Term], span: Span) extends TypeTerm

    final case class PatternApp(fn: Ref, args: NEL[TypePattern], span: Span) extends TypePattern

    final case class Pi(binders: NEL[Binder], out: TypeTerm, span: Span) extends TypeTerm

    final case class Capture(name: String, localRef: CoreAst.LocalRef, span: Span) extends TypePattern

    final case class Body(lets: Vector[Let], res: Term, span: Span) extends Term

    final case class Lam(ty: Pi, uses: Vector[Use], body: Term, span: Span, name: Option[String], isStable: Boolean)
      extends Term

    final case class Match(
        scrut: Term,
        motive: Option[TypeTerm],
        cases: Vector[Case],
        span: Span
    ) extends Term
  }

  final case class Binder(
      name: String,
      localRef: CoreAst.LocalRef,
      ty: TypePattern,
      expectedTy: TypeTerm,
      captures: Vector[Value.VCapture],
      span: Span,
      isDerived: Boolean = false,
      isInstance: Boolean = false
  )

  final case class Let(
      name: String,
      localRef: CoreAst.LocalRef,
      ty: Option[TypeTerm],
      value: Term,
      span: Span,
      isInstance: Boolean = false
  )

  final case class Use(normalizer: Term, span: Span)

  final case class Case(
      ctorName: String,
      argNames: Vector[String],
      argRefs: Vector[Option[CoreAst.LocalRef]],
      body: Term,
      span: Span
  )
}
