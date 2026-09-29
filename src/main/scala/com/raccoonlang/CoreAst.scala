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
// never mention them. A lambda's derived closure field is likewise empty until the checker derives it.

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

    // Pi { kind = k, scope = S } (x: A) -> B x
    //
    // No classifier field: a Pi's universe is env-dependent (level-polymorphic binder types), so it is derived at
    // evaluation time (Interpreter.piClassifier), never baked in. `knownPropValued` is only a checker-filled cache of
    // the classifications that cannot change under level instantiation. The closure is evaluated where the Pi stands,
    // outside its own binders.
    final case class Pi(
        binders: Vector[Binder],
        out: Term,
        closure: Closure,
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

    /**
     * The sort at `level`, `kind` and `scope`. `Type` and `Prop` elaborate to it at `Level.one` and `Level.zero`, and
     * an omitted `kind` or `scope` to `Kind.unr` or `Lifetime.empty`.
     */
    final case class Sort(level: Term, kind: Term, scope: Term, span: Span) extends Term

    /** A sort parameter's form applied to all of its arguments, as `Level.succ(u)`; a nullary form has none. */
    final case class FormOp(form: Form, args: Vector[Term], span: Span) extends Term {
      require(args.length == form.arity, s"${form.qualifiedName} takes ${form.arity} arguments")
    }

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

      /** What the body mentions: a local bound outside the lambda among these is one of its captures (spec §4.3). */
      lazy val bodyRefs: Set[CoreAst.LocalRef] = mentionedRefs(body)

      lazy val refs: Set[CoreAst.LocalRef] = ty.refs | bodyRefs
    }

    /**
     * `scope l => body` (spec §4.1): `ref` denotes the atom this term opens, which its node identity names (Atoms), in
     * checking and evaluation alike. A residual keeps the term and its node identity, so re-evaluating it opens the
     * same atom.
     */
    final case class Scope(ref: CoreAst.LocalRef, body: Term, span: Span) extends Term {
      def nodeId: AstNodeId = span.nodeId
    }

    final case class Match(
        scrut: Term,
        motive: Term,
        cases: Vector[Case],
        span: Span
    ) extends Term {
      def nodeId: AstNodeId = span.nodeId

      lazy val refs: Set[CoreAst.LocalRef] = childRefs(this)
    }

  }

  /**
   * A function type's or lambda's closure (spec §1): its kind, how its values may be applied, and its scope, what they
   * hold. A function type captures nothing, so an omitted field of one is written as `Kind.unr` or `Lifetime.empty`.
   */
  final case class Closure(kind: ClosureField, scope: ClosureField) {
    def terms: Vector[Term] = Vector(kind, scope).flatMap(_.term)
  }

  object Closure {

    /** The closure of a function type that writes none, and of every declaration's own type (spec §3.3). */
    def unrestricted(span: Span): Closure =
      Closure(
        ClosureField.Written(Term.FormOp(Form.KindUnr, Vector.empty, span)),
        ClosureField.Written(Term.FormOp(Form.LifetimeEmpty, Vector.empty, span))
      )
  }

  sealed trait ClosureField {
    def term: Option[Term]
  }

  object ClosureField {
    final case class Written(written: Term) extends ClosureField {
      override def term: Option[Term] = Some(written)
    }

    /** A lambda's omitted field as elaborated, before checking derives it from the lambda's captures. */
    case object Omitted extends ClosureField {
      override def term: Option[Term] = None
    }

    /**
     * A lambda's omitted field as checked (spec §8): the captures it is derived from. Evaluation reads them where the
     * lambda stands and derives the field from their types' sorts (spec §4.3). A capture that contributes `Kind.unr` or
     * `Lifetime.empty` to the field as checking saw it is left out, since every instantiation keeps that. The captures
     * are among the lambda's body refs, so the lambda's own closure env binds them; they are not subterms of its type.
     */
    final case class Derived(captures: Vector[LocalRef]) extends ClosureField {
      override def term: Option[Term] = None
    }
  }

  /**
   * The sort parameters (spec §2.2). The kernel owns them and their forms; the prelude declares none of them. `name` is
   * the global that names the parameter and the namespace of its forms.
   */
  sealed abstract class Parameter(val name: String) {
    lazy val forms: Vector[Form] = Form.all.filter(_.parameter == this)
  }

  object Parameter {
    case object Level extends Parameter("Level")
    case object Kind extends Parameter("Kind")
    case object Lifetime extends Parameter("Lifetime")

    val all: Vector[Parameter] = Vector(Level, Kind, Lifetime)
  }

  /**
   * The forms of the sort parameters. They are forms of the language, not functions: the kernel owns them, no
   * declaration introduces them, and one is only ever written applied to all of its arguments. A form's arguments and
   * result are all of its own parameter.
   */
  sealed abstract class Form(val parameter: Parameter, val name: String, val arity: Int) {
    def qualifiedName: String = s"${parameter.name}.$name"
  }

  object Form {
    case object LevelZero extends Form(Parameter.Level, "zero", 0)
    case object LevelOne extends Form(Parameter.Level, "one", 0)
    case object LevelSucc extends Form(Parameter.Level, "succ", 1)
    case object LevelMax extends Form(Parameter.Level, "max", 2)
    case object LevelIMax extends Form(Parameter.Level, "imax", 2)
    case object KindUnr extends Form(Parameter.Kind, "unr", 0)
    case object KindLin extends Form(Parameter.Kind, "lin", 0)
    case object KindJoin extends Form(Parameter.Kind, "join", 2)
    case object LifetimeEmpty extends Form(Parameter.Lifetime, "empty", 0)
    case object LifetimeUnion extends Form(Parameter.Lifetime, "union", 2)

    val all: Vector[Form] =
      Vector(
        LevelZero,
        LevelOne,
        LevelSucc,
        LevelMax,
        LevelIMax,
        KindUnr,
        KindLin,
        KindJoin,
        LifetimeEmpty,
        LifetimeUnion
      )
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
      case Term.Select(base, _, _)              => Vector(base)
      case Term.Sort(level, kind, scope, _)     => Vector(level, kind, scope)
      case Term.FormOp(_, args, _)              => args
      case Term.App(fn, args, _)                => fn +: args
      case Term.Pi(binders, out, closure, _, _) => closure.terms ++ binders.map(_.ty) :+ out
      case Term.Body(lets, res, _) =>
        lets.flatMap(let => let.ty.toVector :+ let.value) :+ res
      case Term.Lam(ty, body, _, _, _, _) => Vector(ty, body)
      case Term.Scope(_, body, _)         => Vector(body)
      case Term.Match(scrut, motive, cases, _) =>
        Vector(scrut, motive) ++ cases.map(_.body)
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

  /** Whether the term mentions any of `names` as a global, at any depth. */
  private[raccoonlang] def mentionsGlobal(term: Term, names: Set[String]): Boolean =
    term match {
      case Term.GlobalRef(name, _) => names(name)
      case other                   => children(other).exists(mentionsGlobal(_, names))
    }

  // Let: let x := foo
  final case class Let(
      localRef: LocalRef,
      ty: Option[Term],
      value: Term,
      span: Span
  ) {
    def name: String = localRef.name
  }

  /**
   * Where a binder was written, which decides what it may bind (spec §2.2): a declaration's header or a family's
   * parameters may bind a level; a family index, a constructor field, and a function type's or lambda's binder may not.
   * A function type written after a declaration's `:` is not its header.
   */
  sealed trait BinderSite
  object BinderSite {
    case object Parameter extends BinderSite
    case object Field extends BinderSite
    case object Function extends BinderSite
  }

  // An implicit binder never appears in checked App syntax: applications carry only the explicit
  // args, and evaluation reconstructs the implicits by running `projection` against them. The spec
  // is compiled at Pi formation and filled in by BinderOps.checkBinders.
  final case class Binder(
      localRef: LocalRef,
      ty: Term,
      span: Span,
      site: BinderSite,
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
  // it to the canonical name, after which the flag is no longer consulted. A pattern binds a local for every field, a
  // `_` an anonymous one.
  final case class Case(
      ctorName: String,
      isFullyQualified: Boolean,
      patternVars: Vector[PatternVar],
      body: Term,
      span: Span
  ) {
    def argRefs: Vector[LocalRef] = patternVars.map(_.ref)
  }

  /** The local a pattern binds for one constructor field, and where its variable is written. */
  final case class PatternVar(ref: LocalRef, span: Span)

  // Global declarations and environment entries
  sealed trait Decl {
    def span: Span

    /** Every global name this declaration publishes, in source order. A block publishes all of its members. */
    def definedNames: Vector[String] =
      this match {
        case decl: Decl.ConstDecl          => Vector(decl.name)
        case decl: Decl.AxiomDecl          => Vector(decl.name)
        case decl: Decl.InductiveDecl      => inductiveNames(decl)
        case block: Decl.InductiveBlock    => block.families.flatMap(inductiveNames)
        case block: Decl.RecursiveDefBlock => block.definitions.map(_.name)
      }

    /** The name a report uses: top-level names only, without a family's constructors. */
    def label: String =
      (this match {
        case decl: Decl.InductiveDecl   => Vector(decl.header.name)
        case block: Decl.InductiveBlock => block.families.map(_.header.name)
        case other                      => other.definedNames
      }).mkString(", ")

    /** Whether this declaration's terms may name any of `names` as a global (`mayName`). */
    def references(names: Set[String]): Boolean =
      this match {
        case decl: Decl.ConstDecl =>
          mayName(decl.ty, names) || (decl.body match {
            case ConstBody.TermBody(term) => mayName(term, names)
            case _: ConstBody.Builtin     => false
          })
        case decl: Decl.AxiomDecl          => mayName(decl.ty, names)
        case decl: Decl.InductiveDecl      => inductiveReferences(decl, names)
        case block: Decl.InductiveBlock    => block.families.exists(inductiveReferences(_, names))
        case block: Decl.RecursiveDefBlock => block.definitions.exists(recursiveDefReferences(_, names))
      }
  }

  /** A family publishes its own name and each of its constructors'; all of them vanish together if it fails. */
  private def inductiveNames(decl: Decl.InductiveDecl): Vector[String] =
    decl.header.name +: decl.ctors.map(_.canonicalName)

  private def inductiveReferences(decl: Decl.InductiveDecl, names: Set[String]): Boolean = {
    val headerTerms = decl.header.binders.map(_.ty) :+ decl.header.resultTy
    val ctorTerms = decl.ctors.flatMap(ctor => ctor.binders.map(_.ty) :+ ctor.resultTy)
    (headerTerms ++ ctorTerms).exists(mayName(_, names))
  }

  private def recursiveDefReferences(definition: RecursiveDef, names: Set[String]): Boolean =
    mayName(definition.ty, names) || mayName(definition.body, names) || (definition.decreases match {
      case DecreaseSpec.Measure(term, _) => mayName(term, names)
      case _: DecreaseSpec.Lexicographic => false
    })

  /**
   * Whether checking the term may resolve a global among `names`, at any depth. `base.f` is checked as a call of its
   * family's selector `Family.f` (TypeChecker.checkSelect), and which family that is is known only once `base` is
   * checked, so a selection of `f` may name any of `names` whose last segment is `f`.
   */
  private def mayName(term: Term, names: Set[String]): Boolean =
    term match {
      case Term.GlobalRef(name, _) => names(name)
      case Term.Select(base, field, _) =>
        val selector = s".$field"
        names.exists(_.endsWith(selector)) || mayName(base, names)
      case other => children(other).exists(mayName(_, names))
    }

  object Decl {
    // Constant: name : type [:= value]. Opaque definitions keep only their symbolic head in the environment.
    // `sealedBy` is the seal of the family whose generated selector this is, when that family is sealed: the selector is
    // kept to the family's module, as its constructors are.
    final case class ConstDecl(
        isOpaque: Boolean,
        name: String,
        ty: Term,
        body: ConstBody,
        sealedBy: Option[Sealing.Seal],
        span: Span
    ) extends Decl

    final case class AxiomDecl(
        name: String,
        ty: Term,
        span: Span
    ) extends Decl

    // Inductive type declaration. Record syntax has already been lowered to ordinary selector definitions. A sealed
    // family's `seal` keeps its constructors and selectors to the module its declaration was read from (Sealing).
    final case class InductiveDecl(
        header: InductiveHeader,
        ctors: Vector[ConstructorDecl],
        seal: Option[Sealing.Seal],
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
