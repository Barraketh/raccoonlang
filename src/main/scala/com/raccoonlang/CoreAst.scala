package com.raccoonlang
// Core AST for RaccoonCore (trusted kernel language)

object CoreAst {
  final case class LocalRef(id: Int, name: String)

  sealed trait Ast {
    def span: Span

    override def toString: String = PrettyPrinter.printTerm(this)
  }

  // Terms that can appear in function bodies
  sealed trait Term extends Ast

  // Terms that can appear in args
  sealed trait TypePattern extends Ast

  sealed trait TopLevelTP extends TypePattern

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

  // Terms that can appear in type expressions
  sealed trait TypeTerm extends Term

  object TypePattern {
    final case class Type(term: TypeTerm) extends TopLevelTP {
      override def span: Span = term.span
    }

    final case class App(fn: Term.Ref, args: Vector[TypePattern], span: Span) extends TopLevelTP {
      require(args.nonEmpty, "Type pattern application requires at least one argument")
    }

    final case class Capture(localRef: CoreAst.LocalRef, span: Span, constraint: Option[TopLevelTP] = None)
      extends TypePattern
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

    // Nat literal: a nonnegative numeral
    final case class NatLit(number: BigInt, span: Span) extends TypeTerm

    // String literal: its decoded text, which holds only Unicode scalar values
    final case class StrLit(text: String, span: Span) extends TypeTerm

    // Projection in either term or type position: base[field]
    final case class Select(base: Term, field: String, span: Span) extends Term with TypeTerm

    // Explicit instance search expression: derive[Goal]
    final case class Derive(goal: TypeTerm, span: Span) extends TypeTerm

    // Pi (x: A) -> B x
    final case class Pi(binders: Vector[Binder], out: TypeTerm, span: Span, nodeId: NodeId) extends Term with TypeTerm {
      require(binders.nonEmpty, "Pi requires at least one binder")
    }

    // Application in either term or type position.
    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term with TypeTerm

    final case class Body(lets: Vector[Let], res: Term, span: Span) extends Term

    // Lambda: fun (x : A): B => body
    final case class Lam(
        ty: Pi,
        uses: Vector[Use],
        body: Term,
        span: Span,
        name: Option[String],
        recursion: Option[Recursion],
        nodeId: NodeId
    ) extends Term

    sealed trait MatchTerm extends Term {
      def scrut: Term
      def motive: Option[TypeTerm]
      def span: Span
      def nodeId: NodeId
    }

    /**
     * A match's cases, then its wildcard case if it has one. Checking expands a wildcard into the cases it stands for,
     * so a checked match has none. `equation` is where the match names its equation, `match h : e`: then every case,
     * the wildcard included, binds `h` after its fields, as its `equation` local, and otherwise none does.
     */
    final case class Match(
        scrut: Term,
        motive: Option[TypeTerm],
        cases: Vector[Case],
        wildcard: Option[Wildcard],
        equation: Option[Span],
        span: Span,
        nodeId: NodeId
    ) extends MatchTerm

    final case class MatchOne(
        scrut: Term,
        motive: Option[TypeTerm],
        fieldRefs: Vector[CoreAst.LocalRef],
        body: Term,
        span: Span,
        nodeId: NodeId
    ) extends MatchTerm

  }

  // Let: let x := foo
  final case class Let(
      localRef: LocalRef,
      ty: Option[TypeTerm],
      value: Term,
      span: Span,
      isInstance: Boolean = false
  ) {
    def name: String = localRef.name
  }

  // Use directive (first-class normalizer application)
  final case class Use(normalizer: Term, span: Span)

  final case class Binder(
      localRef: LocalRef,
      ty: BinderType,
      span: Span,
      isInstance: Boolean = false
  ) {
    def name: String = localRef.name

    override def toString: String = PrettyPrinter.printBinder(this)
  }

  case class InductiveHeader(
      name: String,
      params: Vector[Binder],
      indices: Vector[Binder],
      resultTy: TypeTerm,
      span: Span
  ) {
    def binders: Vector[Binder] = params ++ indices
    def arity: Int = params.length + indices.length
  }

  case class ConstructorDecl(
      canonicalName: String,
      shortName: String,
      erasedBinders: Vector[Binder],
      fields: Vector[Binder],
      resultTy: TypeTerm,
      span: Span
  ) {
    def name: String = canonicalName
  }

  /** `equation` is the local of the equation its match names, bound after the fields (`Term.Match`). */
  final case class Case(
      ctorName: String,
      isFullyQualified: Boolean,
      argRefs: Vector[Option[LocalRef]],
      body: Term,
      span: Span,
      equation: Option[LocalRef] = None
  )

  /**
   * `| _ => body`, located at the whole case: one case for each reachable constructor that no other case of its match
   * names, binding its fields anonymously (docs/kernel.md, "Wildcard cases"). `MatchChecker` expands it. Its body is
   * elaborated in the match's scope, which is each expanded case's, since an anonymous field binds no local.
   */
  final case class Wildcard(body: Term, span: Span, equation: Option[LocalRef])

  /**
   * `term` written again: the same syntax with a fresh node identity for every node that carries one, so its function
   * types, lambdas and matches are its own, not shared with `term` (`NodeId`: an identity is shared only by
   * representations of the same code, and two checks of one term in different refinements may give different residual
   * code). Locals are slots in their scope, so the copy keeps them: it is checked where `term` would be. A wildcard's
   * expansion checks a copy of its body in each case it stands for.
   */
  private[raccoonlang] def freshCopy(term: Term): Term = {
    def tpe(t: TypeTerm): TypeTerm =
      t match {
        case _: Term.Ref | _: Term.NatLit | _: Term.StrLit => t
        case Term.Select(base, field, span)                => Term.Select(copy(base), field, span)
        case Term.Derive(goal, span)                       => Term.Derive(tpe(goal), span)
        case written: Term.Pi                              => pi(written)
        case Term.App(fn, args, span)                      => Term.App(copy(fn), args.map(copy), span)
      }
    def pi(written: Term.Pi): Term.Pi =
      Term.Pi(written.binders.map(binder), tpe(written.out), written.span, NodeId.fresh())
    def binder(b: Binder): Binder =
      b.copy(ty = b.ty match {
        case BinderType.TypePattern(tp, span) => BinderType.TypePattern(topLevel(tp), span)
        case BinderType.ConstrainedCapture(ref, constraint, span) =>
          BinderType.ConstrainedCapture(ref, topLevel(constraint), span)
      })
    def topLevel(tp: TopLevelTP): TopLevelTP =
      tp match {
        case TypePattern.Type(term)          => TypePattern.Type(tpe(term))
        case TypePattern.App(fn, args, span) => TypePattern.App(fn, args.map(pattern), span)
      }
    def pattern(tp: TypePattern): TypePattern =
      tp match {
        case top: TopLevelTP                            => topLevel(top)
        case TypePattern.Capture(ref, span, constraint) => TypePattern.Capture(ref, span, constraint.map(topLevel))
      }
    def copy(t: Term): Term =
      t match {
        case tt: TypeTerm => tpe(tt)
        case Term.Body(lets, res, span) =>
          Term.Body(lets.map(let => let.copy(ty = let.ty.map(tpe), value = copy(let.value))), copy(res), span)
        case Term.Lam(ty, uses, body, span, name, recursion, _) =>
          val copiedRecursion = recursion.map { r =>
            r.copy(decreases = r.decreases match {
              case DecreaseSpec.Measure(term, sp) => DecreaseSpec.Measure(copy(term), sp)
              case lexicographic                  => lexicographic
            })
          }
          Term.Lam(
            pi(ty),
            uses.map(use => use.copy(normalizer = copy(use.normalizer))),
            copy(body),
            span,
            name,
            copiedRecursion,
            NodeId.fresh()
          )
        case Term.Match(scrut, motive, cases, wildcard, equation, span, _) =>
          Term.Match(
            copy(scrut),
            motive.map(tpe),
            cases.map(c => c.copy(body = copy(c.body))),
            wildcard.map(w => w.copy(body = copy(w.body))),
            equation,
            span,
            NodeId.fresh()
          )
        case Term.MatchOne(scrut, motive, fieldRefs, body, span, _) =>
          Term.MatchOne(copy(scrut), motive.map(tpe), fieldRefs, copy(body), span, NodeId.fresh())
      }
    copy(term)
  }

  // Global declarations and environment entries
  sealed trait Decl {
    def span: Span
  }

  object Decl {
    // Constant: name : type [:= value]. None means explicitly opaque; term definitions otherwise default to Inline.
    final case class ConstDecl(
        name: String,
        ty: TypeTerm,
        body: ConstBody,
        span: Span,
        isInstance: Boolean = false,
        lazyGlobal: Boolean = false
    ) extends Decl

    final case class AxiomDecl(
        name: String,
        ty: TypeTerm,
        span: Span,
        isInstance: Boolean = false
    ) extends Decl

    // Inductive type declaration (structured)
    final case class InductiveDecl(
        header: InductiveHeader,
        ctors: Vector[ConstructorDecl],
        span: Span
    ) extends Decl

    /**
     * Inductive families that may name each other in their constructors, checked and published together
     * (docs/kernel.md, "Mutual blocks").
     */
    final case class MutualInductives(families: Vector[InductiveDecl], span: Span) extends Decl

    /** Recursive definitions that may call each other, checked and published together. */
    final case class MutualDefs(members: Vector[MutualDef], span: Span) extends Decl
  }

  /**
   * A member of a mutual block of definitions: its lambda, without a recursion of its own, and its metric. After its
   * parameters, its body binds `peers`, a slot for each member of the block, itself included, in the block's order,
   * through which it calls them.
   */
  final case class MutualDef(name: String, lam: Term.Lam, decreases: DecreaseSpec, peers: Vector[LocalRef], span: Span)

  case class Program(decls: Vector[Decl], body: Option[Term])
}
