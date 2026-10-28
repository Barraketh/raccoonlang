package com.raccoonlang

import com.raccoonlang.Value.Universe

// Checked AST. Instance search expressions have already been resolved, and all local names are CoreAst.LocalRef slots.
object ElabAst {
  sealed trait Ast {
    def span: Span

    override def toString: String = PrettyPrinter.printElabTerm(this)
  }

  sealed trait Term extends Ast

  sealed trait TypePattern extends Ast

  sealed trait TopLevelTP extends TypePattern

  sealed trait TypeTerm extends Term

  object TypePattern {
    final case class Type(term: TypeTerm) extends TopLevelTP {
      override def span: Span = term.span
    }

    final case class App(fn: Term.Ref, args: Vector[TypePattern], span: Span) extends TopLevelTP {
      require(args.nonEmpty, "Type pattern application requires at least one argument")
    }

    final case class Capture(localRef: CoreAst.LocalRef, span: Span) extends TypePattern
  }

  sealed trait BinderType extends Ast

  object BinderType {
    final case class TypePattern(tp: TopLevelTP, span: Span) extends BinderType
    final case class ConstrainedCapture(localRef: CoreAst.LocalRef, constraint: TopLevelTP, span: Span)
      extends BinderType
  }

  object Term {
    sealed trait Ref extends Term with TypeTerm

    final case class GlobalRef(name: String, span: Span) extends Ref

    final case class LocalRef(ref: CoreAst.LocalRef, span: Span) extends Ref

    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term with TypeTerm

    final case class NatLit(value: BigInt, span: Span) extends Term with TypeTerm

    /**
     * String literal: its decoded text, which holds only Unicode scalar values. Its value is built on first evaluation
     * and shared by every later one; values never change, and no claim can extend its chunk, which is full.
     */
    final case class StrLit(text: String, span: Span) extends Term with TypeTerm {
      lazy val value: Value = packed.Strings.literal(text)
    }

    /**
     * A value of a list-shaped type, flat: `pieces` in order, ending in a splice. A layer piece holds the arguments of
     * one application of the cons constructor `consHead` before and after its recursive field, which is the rest of the
     * word; the erased arguments come first, as in any constructor application, and evaluation skips them. A splice is
     * a list term that the rest is appended to with the kernel `List` 's native `append`, and the last splice is the
     * end of the word, such as a terminator. Only the kernel `List` has splices before the end: runs of characters, as
     * `String.data` of a literal. Quotation emits it (`ValueQuote`), so that a long list is a node of linear size, and
     * evaluation, which conses the layers and appends the splices from the back in a loop, needs no stack per piece.
     * Like constructor applications, words are also type terms: they can be concrete arguments in type patterns.
     */
    final case class Word(consHead: GlobalRef, pieces: Vector[WordPiece], span: Span) extends TypeTerm {
      require(pieces.lastOption.exists(_.isInstanceOf[WordPiece.Splice]), "A word ends in a splice")
    }

    sealed trait WordPiece

    object WordPiece {
      final case class Layer(before: Vector[Term], after: Vector[Term]) extends WordPiece
      final case class Splice(list: Term) extends WordPiece
    }

    final case class Pi(binders: Vector[Binder], out: TypeTerm, classifier: Universe, span: Span, nodeId: NodeId)
      extends Term
      with TypeTerm {
      require(binders.nonEmpty, "Pi requires at least one binder")
    }

    final case class Body(lets: Vector[Let], res: Term, span: Span) extends Term

    final case class Lam(
        ty: Pi,
        body: Term,
        span: Span,
        name: Option[String],
        recursiveSelf: Option[CoreAst.LocalRef],
        nodeId: NodeId
    ) extends Term

    final case class Match(
        scrut: Term,
        motive: Option[TypeTerm],
        cases: Vector[Case],
        span: Span,
        nodeId: NodeId
    ) extends Term
  }

  final case class Binder(
      localRef: CoreAst.LocalRef,
      ty: BinderType,
      span: Span,
      isInstance: Boolean = false
  ) {
    def name: String = localRef.name

    override def toString: String = PrettyPrinter.printElabBinder(this)
  }

  final case class Let(
      localRef: CoreAst.LocalRef,
      ty: Option[TypeTerm],
      value: Term,
      span: Span,
      isInstance: Boolean = false
  ) {
    def name: String = localRef.name
  }

  final case class Case(ctorName: String, argRefs: Vector[Option[CoreAst.LocalRef]], body: Term, span: Span)
}
