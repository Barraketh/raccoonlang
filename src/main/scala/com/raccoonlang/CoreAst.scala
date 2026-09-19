package com.raccoonlang
// The one AST of RaccoonCore (trusted kernel language). The elaborator produces it from surface
// syntax, the type checker checks it, and the checker's residual is the same type again — annotated
// rather than translated (TypeChecker.CheckedTerm). All local names are CoreAst.LocalRefs.
//
// Types are terms: "is a type" is a semantic judgment (TypeChecker.assertType), not a syntactic
// class, so binder types, motives, and declared types are ordinary Terms.
//
// A few fields exist only after checking — `Binder.projection`, `Pi.knownPropValued`, and
// `Lam.recursivePeers`. Each defaults to the "not yet checked" value, so the parser and elaborator
// never mention them.

object CoreAst {
  final case class LocalRef(id: Int, name: String)

  sealed trait Ast {
    def span: Span

    override def toString: String = PrettyPrinter.printTerm(this)
  }

  sealed trait Term extends Ast

  sealed trait ConstBody {
    def span: Span
  }

  sealed trait DecreaseSpec extends Ast

  object ConstBody {
    final case class TermBody(term: Term) extends ConstBody {
      override def span: Span = term.span
    }

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

    // Projection: base[field]
    final case class Select(base: Term, field: String, span: Span) extends Term

    // Pi (x: A) -> B x
    //
    // No classifier field: a Pi's universe is env-dependent (level-polymorphic binder types), so it is derived at
    // evaluation time (Interpreter.piClassifier), never baked in. `knownPropValued` is only a checker-filled cache of
    // the classifications that cannot change under level instantiation.
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

    // Application: f(a)
    //
    // Checked applications carry only the explicit args: every implicit binder is re-derived by running its projection
    // spec against them (Interpreter.reconstructImplicits).
    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term

    final case class Body(lets: Vector[Let], res: Term, span: Span) extends Term

    // Lambda: fun (x : A): B => body
    //
    // `recursion` is what the source declared; `recursivePeers` is the runtime peer table the checker fills — a
    // singleton's own self reference, or the whole group's table for a RecursiveDefBlock member, which no single
    // lambda could derive on its own (Interpreter.runLam).
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
        // `None` means the match's result type is the scrutinee's own type (Interpreter.matchOutType).
        motive: Option[Term],
        cases: Vector[Case],
        span: Span
    ) extends Term {
      def nodeId: AstNodeId = span.nodeId

      lazy val refs: Set[CoreAst.LocalRef] = childRefs(this)
    }

  }

  /**
   * The immediate subterms of a term, in source order.
   *
   * Every structural walk over the AST (capture analysis, local-reference collection, global-reference scans) shares
   * this one enumeration, so a new node kind cannot be silently skipped by one traversal and handled by another: it is
   * added here once, and each traversal only states what it does at the nodes it actually cares about.
   */
  def children(term: Term): Vector[Term] =
    term match {
      case _: Term.GlobalRef | _: Term.LocalRef | _: Term.NatLit | _: Term.StrLit =>
        Vector.empty
      case Term.Select(base, _, _)     => Vector(base)
      case Term.App(fn, args, _)       => fn +: args
      case Term.Pi(binders, out, _, _) => binders.map(_.ty) :+ out
      case Term.Body(lets, res, _) =>
        lets.flatMap(let => let.ty.toVector :+ let.value) :+ res
      case Term.Lam(ty, body, _, _, _, _) => Vector(ty, body)
      case Term.Match(scrut, motive, cases, _) =>
        (scrut +: motive.toVector) ++ cases.map(_.body)
    }

  /**
   * Every `LocalRef` the term mentions, at any depth, with no regard for what the term itself binds.
   *
   * This is deliberately not lexical free-variable analysis, and matches what `CapturedRefs` needs: a closure captures
   * the refs that are already bound in the env at closure-creation time, and refs a term introduces itself are simply
   * not in that env. Intersecting this set with an env's locals therefore gives exactly the captures.
   *
   * The nodes that carry a cached `refs` reuse it rather than re-walking, so computing this for a deeply nested term is
   * linear in the nodes not already cached.
   */
  private[raccoonlang] def mentionedRefs(term: Term): Set[CoreAst.LocalRef] =
    term match {
      case Term.LocalRef(ref, _) => Set(ref)
      case pi: Term.Pi           => pi.refs
      case lam: Term.Lam         => lam.refs
      case m: Term.Match         => m.refs
      case other                 => childRefs(other)
    }

  /** The union over a node's immediate children. The cached nodes call this to fill their own `refs`. */
  private def childRefs(term: Term): Set[CoreAst.LocalRef] =
    children(term).foldLeft(Set.empty[CoreAst.LocalRef])((acc, child) => acc | mentionedRefs(child))

  // Let: let x := foo
  final case class Let(
      localRef: LocalRef,
      ty: Option[Term],
      value: Term,
      span: Span
  ) {
    def name: String = localRef.name
  }

  // An implicit binder never appears in checked App syntax: applications carry only the explicit
  // args, and evaluation reconstructs the implicits by running `projection` against them. The spec
  // is compiled at Pi formation and filled in by BinderOps.checkBinders.
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

  // `isFullyQualified` records how the source wrote the constructor name; match checking resolves
  // it to the canonical name, after which the flag is no longer consulted.
  final case class Case(
      ctorName: String,
      isFullyQualified: Boolean,
      argRefs: Vector[Option[LocalRef]],
      body: Term,
      span: Span
  )

  // Global declarations and environment entries
  sealed trait Decl {
    def span: Span
  }

  object Decl {
    // Constant: name : type [:= value]. Opaque definitions keep only their symbolic head in the environment.
    final case class ConstDecl(
        isOpaque: Boolean,
        name: String,
        ty: Term,
        body: ConstBody,
        span: Span
    ) extends Decl

    final case class AxiomDecl(
        name: String,
        ty: Term,
        span: Span
    ) extends Decl

    // Inductive type declaration. Record syntax has already been lowered to ordinary selector definitions.
    final case class InductiveDecl(
        header: InductiveHeader,
        ctors: Vector[ConstructorDecl],
        span: Span
    ) extends Decl

    /** A mutually checked group of families sharing one common parameter telescope. */
    final case class InductiveBlock(families: Vector[InductiveDecl], span: Span) extends Decl {
      def numParams: Int = families.headOption.fold(0)(_.header.params.length)
    }

    /** An atomic structural-recursion group. Its peer table is derived from `definitions`. */
    final case class RecursiveDefBlock(definitions: Vector[RecursiveDef], span: Span) extends Decl
  }

  case class Program(decls: Vector[Decl], body: Option[Term])
}
