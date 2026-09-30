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

    final case class StrLit(scalars: Vector[Int], span: Span) extends Term

    // Projection: base.field
    final case class Select(base: Term, field: String, span: Span) extends Term

    /**
     * Pi `{ kind = k, scope = S } (x: A) -> B x`. An unparenthesised arrow chain is ONE binder group: `(a: A) -> (b: B)
     * -> C` carries both binders here. Grouping is part of a function type's identity, so a parenthesised Pi in body
     * position — `(a: A) -> ((b: B) -> C)` — is a nested, separate 1-ary Pi and stays its own node. The closure
     * prefixes the whole group.
     */
    final case class Pi(closure: Closure, binders: Vector[Binder], body: Term, span: Span) extends Term

    // Application: f(a)
    final case class App(fn: Term, args: Vector[Term], span: Span) extends Term

    /**
     * A pair expression `(a, b)`: `Pair.mk(a, b)` of the active prelude, whatever is in scope (PAIRS_AND_PRELUDE §4).
     */
    final case class Pair(fst: Term, snd: Term, span: Span) extends Term

    /**
     * A sort former: `Sort { level = e, ... }`, or `Type` /`Prop`, which fix the level. `kind` and `scope` are the
     * fields written, if any.
     */
    final case class Sort(level: SortLevel, kind: Option[Term], scope: Option[Term], span: Span) extends Term

    sealed trait SortLevel
    object SortLevel {
      case object Zero extends SortLevel
      case object One extends SortLevel
      final case class Written(level: Term) extends SortLevel
    }

    // Lambda: fun { kind = k, scope = S } (x : A)(y: B): B => body
    final case class Lam(closure: Closure, header: FuncHeader, body: Term, span: Span) extends Term

    // Scope: scope l => body
    final case class Scope(name: String, body: Term, span: Span) extends Term

    final case class Match(
        scrut: Term,
        motive: Term,
        cases: Vector[Case],
        span: Span
    ) extends Term

    // Let: let x := foo, or a destructuring: let (a, (b, c)) := foo
    final case class Let(pattern: LetPattern, ty: Option[Term], value: Term, span: Span)

    /** What a `let` binds: a name or `_`, or a destructuring of two or more components (PAIRS_AND_PRELUDE §3.1). */
    sealed trait LetPattern {
      def span: Span

      /** Every name the pattern binds, `_` included, at any depth and in source order. */
      def names: Vector[LetPattern.Name] =
        this match {
          case name: LetPattern.Name                 => Vector(name)
          case LetPattern.Destructure(components, _) => components.flatMap(_.names)
        }
    }

    object LetPattern {
      final case class Name(name: String, span: Span) extends LetPattern
      final case class Destructure(components: Vector[LetPattern], span: Span) extends LetPattern
    }

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
        patternVars: Vector[PatternVar],
        body: Term,
        span: Span
    )

    /** A pattern's variable for one constructor field, `_` included, where it is written. */
    final case class PatternVar(name: String, span: Span)
  }

  /**
   * A function type's or lambda's closure, as written: its `kind` and `scope` fields, either of which may be omitted.
   */
  final case class Closure(kind: Option[Term], scope: Option[Term])

  object Closure {
    val omitted: Closure = Closure(None, None)
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
      // Constant: name : type [:= value]. Opaque definitions keep only their symbolic head in the environment. A
      // struct's generated selector names its family's declaration in `selectorOf`; a program cannot write one.
      final case class ConstDecl(
          isOpaque: Boolean,
          header: DeclHeader,
          decreases: Option[DecreaseSpec],
          body: ConstBody,
          selectorOf: Option[InductiveDecl],
          span: Span
      ) extends Decl

      final case class AxiomDecl(
          header: DeclHeader,
          span: Span
      ) extends Decl

      // Inductive type declaration
      final case class InductiveDecl(
          header: InductiveHeader,
          ctors: Vector[ConstructorDecl],
          generateSelectors: Boolean,
          isSealed: Boolean,
          span: Span
      ) extends Decl
    }

    case class Namespace(path: Vector[String], body: Vector[Command], span: Span) extends Command

    case class Open(namespace: Vector[String], root: Boolean, rules: Vector[AliasRule], span: Span) extends Command

    case class Block(body: Vector[Command], span: Span) extends Command

    /**
     * An atomic group of mutually recursive declarations. The elaborator lowers the group either to one recursive
     * definition block or one inductive block.
     */
    case class Mutual(body: Vector[Command], span: Span) extends Command

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
