package com.raccoonlang

// The one AST of RaccoonCore.  This data contract is shared by the untyped
// evaluator and the later checker; semantic restrictions are deliberately
// absent from this first executable milestone.
object CoreAst {
  final case class LocalRef(id: Int, name: String)

  sealed trait Ast {
    def span: Span
    override def toString: String = PrettyPrinter.printTerm(this)
  }

  sealed trait Term extends Ast
  sealed trait ConstBody { def span: Span }
  sealed trait DecreaseSpec extends Ast

  object ConstBody {
    final case class TermBody(term: Term) extends ConstBody { override def span: Span = term.span }
    final case class Builtin(span: Span) extends ConstBody
  }

  object DecreaseSpec {
    final case class Lexicographic(args: Vector[LocalRef], span: Span) extends DecreaseSpec
    final case class Measure(term: Term, span: Span) extends DecreaseSpec
  }

  final case class Recursion(selfRef: LocalRef, decreases: DecreaseSpec)

  final case class RecursiveDef(
      name: String,
      peerRef: LocalRef,
      ty: Term.Pi,
      body: Term,
      decreases: DecreaseSpec,
      span: Span
  )

  object Term {
    sealed trait Ref extends Term
    final case class GlobalRef(name: String, span: Span) extends Ref
    final case class LocalRef(ref: CoreAst.LocalRef, span: Span) extends Ref
    final case class NatLit(value: BigInt, span: Span) extends Term
    final case class StrLit(scalars: Vector[Int], span: Span) extends Term
    final case class Select(base: Term, field: String, span: Span) extends Term

    final case class Pi(
        binders: Vector[Binder],
        out: Term,
        span: Span,
        knownPropValued: Option[Boolean] = None
    ) extends Term {
      require(binders.nonEmpty, "Pi requires at least one binder")
      def nodeId: AstNodeId = span.nodeId
      lazy val refs: Set[CoreAst.LocalRef] = childRefs(this)
    }

    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term
    final case class Body(lets: Vector[Let], res: Term, span: Span) extends Term

    final case class Lam(
        ty: Pi,
        body: Term,
        span: Span,
        name: Option[String],
        recursion: Option[Recursion],
        recursivePeers: Vector[(CoreAst.LocalRef, String)] = Vector.empty
    ) extends Term {
      def nodeId: AstNodeId = span.nodeId
      lazy val refs: Set[CoreAst.LocalRef] = childRefs(this)
    }

    final case class Match(
        scrut: Term,
        motive: Option[Term],
        cases: Vector[Case],
        span: Span
    ) extends Term {
      def nodeId: AstNodeId = span.nodeId
      lazy val refs: Set[CoreAst.LocalRef] = childRefs(this)
    }
  }

  def children(term: Term): Vector[Term] = term match {
    case _: Term.GlobalRef | _: Term.LocalRef | _: Term.NatLit | _: Term.StrLit => Vector.empty
    case Term.Select(base, _, _)                                                => Vector(base)
    case Term.App(fn, args, _)                                                  => fn +: args
    case Term.Pi(binders, out, _, _)                                            => binders.map(_.ty) :+ out
    case Term.Body(lets, res, _)             => lets.flatMap(let => let.ty.toVector :+ let.value) :+ res
    case Term.Lam(ty, body, _, _, _, _)      => Vector(ty, body)
    case Term.Match(scrut, motive, cases, _) => (scrut +: motive.toVector) ++ cases.map(_.body)
  }

  private[raccoonlang] def mentionedRefs(term: Term): Set[CoreAst.LocalRef] = term match {
    case Term.LocalRef(ref, _) => Set(ref)
    case pi: Term.Pi           => pi.refs
    case lam: Term.Lam         => lam.refs
    case m: Term.Match         => m.refs
    case other                 => childRefs(other)
  }

  private def childRefs(term: Term): Set[CoreAst.LocalRef] =
    children(term).foldLeft(Set.empty[CoreAst.LocalRef])((acc, child) => acc | mentionedRefs(child))

  final case class Let(localRef: LocalRef, ty: Option[Term], value: Term, span: Span) {
    def name: String = localRef.name
  }

  final case class Binder(
      localRef: LocalRef,
      ty: Term,
      span: Span,
      isImplicit: Boolean = false,
      projection: Option[telescope.Projection.Spec] = None
  ) {
    def name: String = localRef.name
    override def toString: String = PrettyPrinter.printBinder(this)
  }

  case class InductiveHeader(
      name: String,
      params: Vector[Binder],
      indices: Vector[Binder],
      resultTy: Term,
      span: Span
  ) {
    def binders: Vector[Binder] = params ++ indices
    def arity: Int = params.length + indices.length
  }

  case class ConstructorDecl(
      canonicalName: String,
      shortName: String,
      binders: Vector[Binder],
      resultTy: Term,
      span: Span
  ) {
    def name: String = canonicalName
  }

  final case class Case(
      ctorName: String,
      isFullyQualified: Boolean,
      argRefs: Vector[Option[LocalRef]],
      body: Term,
      span: Span
  )

  sealed trait Decl { def span: Span }
  object Decl {
    final case class ConstDecl(isOpaque: Boolean, name: String, ty: Term, body: ConstBody, span: Span) extends Decl
    final case class AxiomDecl(name: String, ty: Term, span: Span) extends Decl
    final case class InductiveDecl(header: InductiveHeader, ctors: Vector[ConstructorDecl], span: Span) extends Decl
    final case class InductiveBlock(families: Vector[InductiveDecl], span: Span) extends Decl {
      def numParams: Int = families.headOption.fold(0)(_.header.params.length)
    }
    final case class RecursiveDefBlock(definitions: Vector[RecursiveDef], span: Span) extends Decl
  }

  case class Program(decls: Vector[Decl], body: Option[Term])
}
