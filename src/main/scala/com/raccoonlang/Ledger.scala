package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps
import com.raccoonlang.{ElabAst => EA}

import scala.collection.immutable.BitSet

/**
 * Which values are linear (docs/kernel.md, "Linear types"). A type is linear when the kind of its universe is not
 * provably `copy`: `Lin(u)`, or a `Univ(k, u)` whose kind holds a variable. A value is linear when its type is; types,
 * universes, proofs and function values never are. A type determines its universe, so this is read off the type, never
 * off a family's fields.
 */
object Linearity {

  /** Whether `tpe`, a type, is linear. */
  def isLinear(tpe: Value): Boolean =
    tpe.tpe match {
      case VUniv(kind, _) => !kind.isCopy
      case _              => false
    }

  /**
   * What the ledger and the read rules (S1) ask of a checked node, decided by one universe test on its value's type.
   */
  sealed trait Role
  object Role {

    /** A type or a proof: a read extent, whose uses do not count. */
    case object TypeOrProof extends Role

    /** A value of linear type. */
    case object Linear extends Role

    /** Any other value: data of an unrestricted type, a level, or a function. */
    case object Ordinary extends Role
  }

  def role(value: Value): Role =
    value.tpe match {
      case _: Universe => Role.TypeOrProof
      case tpe =>
        tpe.tpe match {
          case PropTpe                        => Role.TypeOrProof
          case VUniv(kind, _) if !kind.isCopy => Role.Linear
          case _                              => Role.Ordinary
        }
    }

  /**
   * S3, a lint: whether a linear type occurs anywhere in `value`, an axiom's evaluated type or a part of it, so that
   * the axiom could produce or consume linear values. It occurs as a binder type or codomain of a function type at any
   * depth, or anywhere in an argument of an application, such as a family instance `Box(Nat -> Tok)`, a symbol
   * application `Gen(Tok)` or a constructor value, including a word's parts and a lambda's type and body opened on
   * fresh arguments. A linear type is a value whose universe is `Lin(u)`; `Lin(u)` itself is a universe, so `axiom T :
   * Lin(Level.zero)` passes, and so does every data axiom, such as `axiom magicNat : Nat`.
   *
   * Not seen: a stuck computation, such as a codomain `F(b)` that computes to `Nat -> Tok` at some `b`; a type variable
   * that a use instantiates, as in `axiom pick (A: Type) : A` at `A := Nat -> Tok`; and the field types of a family the
   * type names, as in `axiom m : Mint` for `inductive Mint : Type | mk (f: Nat -> Tok)`. Protocol soundness rests on
   * `--no-user-axioms`, not on this lint.
   */
  def axiomMentionsLinear(value: Value): Boolean =
    isLinear(value) || (value match {
      case pi: VPi =>
        val fresh = BinderOps.freshen(pi)
        pi.binders.exists(binder => axiomMentionsLinear(fresh(binder.localRef).tpe)) ||
        axiomMentionsLinear(pi.codomain(fresh))
      // A family instance, or a symbol, constructor or stuck application. Its head is a family, a symbol, a constructor
      // or a function in scope as a binder, whose type the telescope walk has seen.
      case app: VApp => app.args.exists(axiomMentionsLinear)
      case word: VWord =>
        !packed.Words.foreach(word)(
          layer = token => !(0 until token.payloadWidth).exists(index => axiomMentionsLinear(token.payload(index))),
          end = token => !axiomMentionsLinear(token.value)
        )
      case lam: VLam =>
        axiomMentionsLinear(lam.tpe) || (lam.body match {
          case _: LamBody.Core =>
            val fresh = BinderOps.freshen(lam.tpe)
            axiomMentionsLinear(Interpreter.runLam(lam, lam.tpe.binders.map(binder => fresh(binder.localRef))))
          // A native's type is walked above; its body is a builtin computation, which is not opened.
          case _: LamBody.Native => false
        })
      // The walk reads a value's form, so a suspended proof's forced value (docs/kernel.md, "Proof calls").
      case proof: VSuspendedProof => axiomMentionsLinear(Interpreter.force(proof))
      // A stuck match is not opened, and a variable is linear only by its own type, tested above.
      case _: NeutralThunk | _: Var | _: VConst | _: ConstructorHead | _: VNatPoly | _: Level | LevelTpe | _: Kind |
          KindTpe | _: VUniv | PropTpe | KernelObject =>
        false
    })
}

/**
 * The ledger (docs/kernel.md, "Linear types"). Two rules, decided bottom-up as each node is checked.
 *
 * **Terms use at most once.** A tracked local is used at most once on every path through its binder's extent, and may
 * be dropped. A path takes one branch at each `match`; an application evaluates its head and then its arguments, a
 * block its lets and then its result, and a match its scrutinee on every path through it. A use inside a read extent, a
 * node whose value is a type or a proof, is not a use: reading consumes nothing. So a binder whose extent is itself a
 * read extent, such as a parameter of a function returning a proposition, is only read, as often as its extent likes.
 *
 * **Reads keep inputs separate.** Inside a read extent, every linear-typed term has a provenance (`Provenance`): the
 * regions of root locals it is built from. Each call, an application or a constructor, must receive linear inputs of
 * pairwise disjoint provenance (`LinearReusedInType`), and the roots of their union must have been jointly live at some
 * point on the path (`LinearNotJointlyLive`). A call outside every read extent that breaks either rule also uses a
 * local twice, which the first rule reports, so each node passes its first violation up and the nearest read extent
 * reports it.
 *
 * A node's `LinearInfo` summarises both. Programs without tracked locals carry only `LinearInfo.empty`, and evaluation
 * makes none of these checks.
 */
object Ledger {

  /**
   * What the paths through a term do with one local: its first use on any path, and the first use that is a second use
   * on some path, each in source order.
   */
  final case class Uses(first: Option[Span], reuse: Option[Span]) {

    /** This term, then `next`, on one path: a use in `next` after a use here is a second use on that path. */
    def andThen(next: Uses): Uses =
      Uses(first.orElse(next.first), reuse.orElse(if (first.isDefined) next.first else None).orElse(next.reuse))

    /** The paths of two branches of one `match`. */
    def or(other: Uses): Uses = Uses(first.orElse(other.first), reuse.orElse(other.reuse))
  }

  private val none = Uses(None, None)

  /** The uses of every tracked local a term mentions outside its read extents, by slot id. */
  final class Summary private (val locals: Map[Int, Uses]) {
    def of(id: Int): Uses = locals.getOrElse(id, none)

    /** This term, then `next`, on one path. */
    def andThen(next: Summary): Summary = combine(next, _ andThen _)

    /** The paths of two branches of one `match`. */
    def or(other: Summary): Summary = combine(other, _ or _)

    private def combine(other: Summary, op: (Uses, Uses) => Uses): Summary =
      if (other.locals.isEmpty) this
      else if (locals.isEmpty) other
      else {
        val ids = locals.keySet ++ other.locals.keySet
        new Summary(ids.iterator.map(id => id -> op(of(id), other.of(id))).toMap)
      }

    /** The term with the local `id` out of scope. */
    def without(id: Int): Summary = if (locals.contains(id)) new Summary(locals - id) else this

    /** The tracked locals some path through the term uses. */
    def consumed: BitSet = BitSet.fromSpecific(locals.keysIterator)
  }

  object Summary {
    val empty: Summary = new Summary(Map.empty)
    def use(id: Int, span: Span): Summary = new Summary(Map(id -> Uses(Some(span), None)))
  }

  /**
   * A region of a root's value: the root, a tracked local bound with no defining value of its own, such as a parameter,
   * and the path of field indices that matches took into it. Two regions overlap when one path is a prefix of the
   * other.
   */
  final case class Origin(root: Int, path: Vector[Int]) {
    def overlaps(other: Origin): Boolean =
      root == other.root && (path.startsWith(other.path) || other.path.startsWith(path))
  }

  /**
   * The regions a linear value is built from. `exact` holds when the value is exactly its one region: a root, a field
   * of an exact value, or a `let` bound to one. Only then are a match's fields sub-regions of it; a field of any other
   * value, such as a constructor application, may be any part of its scrutinee's regions, so it gets them all. A `let`
   * aliases its value's provenance, and a value with none, a closed computation, may be recomputed in any read (R5).
   */
  final case class Provenance(origins: Set[Origin], exact: Boolean) {
    def isEmpty: Boolean = origins.isEmpty
    def overlaps(other: Provenance): Boolean = origins.exists(origin => other.origins.exists(origin.overlaps))
    def roots: BitSet = BitSet.fromSpecific(origins.iterator.map(_.root))

    /** Stored field `index` of a value of this provenance. */
    def field(index: Int): Provenance =
      if (exact) Provenance(origins.map(origin => origin.copy(path = origin.path :+ index)), exact = true) else this
  }

  object Provenance {
    val empty: Provenance = Provenance(Set.empty, exact = false)
    def root(id: Int): Provenance = Provenance(Set(Origin(id, Vector.empty)), exact = true)

    /** A value built from these, such as a call's result: it covers their regions, and need be none of them. */
    def union(provenances: Iterator[Provenance]): Provenance = Provenance(provenances.flatMap(_.origins).toSet, false)
  }

  /**
   * What a checked term does with tracked locals: its uses outside read extents; its provenance, for a linear value,
   * empty for any other; and the first violation of the read rules inside it that no read extent has reported yet.
   */
  final case class LinearInfo(uses: Summary, provenance: Provenance, pending: Option[TypeError]) {

    /** This node, whose value is `value`: a read extent reports `pending` and keeps nothing else. */
    def at(value: Value): LinearInfo =
      Linearity.role(value) match {
        case Linearity.Role.TypeOrProof =>
          pending.foreach(error => throw error)
          LinearInfo.empty
        case Linearity.Role.Linear   => this
        case Linearity.Role.Ordinary => if (provenance.isEmpty) this else copy(provenance = Provenance.empty)
      }
  }

  object LinearInfo {
    val empty: LinearInfo = LinearInfo(Summary.empty, Provenance.empty, None)

    /** A use of the tracked local `id`, whose binding gives its provenance. */
    def tracked(id: Int, span: Span, provenance: Provenance): LinearInfo =
      LinearInfo(Summary.use(id, span), provenance, None)
  }

  /** One input of a call: its info, and the span to report a shared local at, computed only for a report. */
  final class Input(val info: LinearInfo, spanOf: => Span) {
    lazy val span: Span = spanOf
  }

  object Input {
    def apply(info: LinearInfo, span: => Span): Input = new Input(info, span)
  }

  /**
   * A call, an application or a constructor, of `inputs` in evaluation order, the head first, whose value is `value`,
   * at `span` in `env`: its uses are its inputs' in sequence, its provenance their union, and it checks separation and
   * joint liveness over its linear inputs.
   */
  def call(value: Value, inputs: Seq[Input], span: => Span, env: Env): LinearInfo =
    if (inputs.forall(_.info eq LinearInfo.empty)) LinearInfo.empty.at(value)
    else {
      val uses = inputs.foldLeft(Summary.empty)((sum, input) => sum.andThen(input.info.uses))
      val pending = inputs.iterator.flatMap(_.info.pending).nextOption().orElse {
        separation(inputs.map(input => (input.info.provenance, input.span)), span, env)
      }
      LinearInfo(uses, Provenance.union(inputs.iterator.map(_.info.provenance)), pending).at(value)
    }

  /**
   * A projection of stored field `index` of a record whose info is `record`, whose value is `value`: the one-branch
   * match that returns that field (L4, L5). It uses its record, so a second projection of a linear record on one path
   * is a second use, and the other fields are dropped. Inside a read extent it is no call but an inspection, as a match
   * is, and it is field `index` of its record's provenance (S1): `(r, p ++ [index])` of a record that is exactly the
   * region `(r, p)`, the record's whole provenance otherwise. So two projections of one field overlap, and so do a
   * field and its record, while sibling fields are separate.
   */
  def project(record: LinearInfo, index: Int, value: Value): LinearInfo =
    if (record eq LinearInfo.empty) LinearInfo.empty
    else LinearInfo(record.uses, record.provenance.field(index), record.pending).at(value)

  /**
   * Separation at one call: the provenances of its linear inputs, each with the span to report a shared region at, are
   * pairwise disjoint, and the roots of their union were jointly live. Only linear values carry provenance, so the
   * unrestricted inputs need no test.
   */
  def separation(provenances: Seq[(Provenance, Span)], span: => Span, env: Env): Option[TypeError] = {
    var all = Vector.empty[Provenance]
    provenances.foreach { case (provenance, inputSpan) =>
      all.find(_.overlaps(provenance)).foreach { earlier =>
        val shared = earlier.origins.find(origin => provenance.origins.exists(origin.overlaps)).get
        return Some(LinearReusedInType(nameOf(shared.root, env), Some(inputSpan)))
      }
      if (!provenance.isEmpty) all = all :+ provenance
    }
    jointlyLive(BitSet.fromSpecific(all.iterator.flatMap(_.roots)), span, env)
  }

  /**
   * Joint liveness of the roots `ids`, all in scope in `env`: the latest bound, which has the greatest slot, was bound
   * when none of the others had been consumed on the path, so all were live together just after it was bound; a value
   * built from them since is recomputed from that point. A single root, consumed or not, is always fine: its
   * admissibility persists.
   */
  def jointlyLive(ids: BitSet, span: => Span, env: Env): Option[TypeError] =
    if (ids.size < 2) None
    else {
      val latest = ids.max
      val dead = env.localBinding(CoreAst.LocalRef(latest, "")).deadBefore
      (ids - latest)
        .find(dead.contains)
        .map(consumed => LinearNotJointlyLive(nameOf(consumed, env), nameOf(latest, env), Some(span)))
    }

  private def nameOf(id: Int, env: Env): String = env.localBinding(CoreAst.LocalRef(id, "")).name

  /**
   * The binder rule for the tracked local `ref` over its extent's uses: at most once on every path, unless the extent
   * is a read extent (`read`), which only reads the local; then the extent's summary without it.
   */
  def bind(ref: CoreAst.LocalRef, extent: Summary, read: Boolean): Summary = {
    if (!read) extent.of(ref.id).reuse.foreach(span => throw LinearReused(ref.name, Some(span)))
    extent.without(ref.id)
  }

  /** The first syntactic reference to local slot `id` in `term`, for reporting a capture. */
  def firstReference(id: Int, term: EA.Term): Option[Span] = {
    def terms(ts: Iterable[EA.Term]): Option[Span] = ts.iterator.map(firstReference(id, _)).collectFirst {
      case Some(span) => span
    }
    def pattern(tp: EA.TypePattern): Option[Span] =
      tp match {
        case EA.TypePattern.Type(t) => firstReference(id, t)
        case EA.TypePattern.App(fn, args, _) =>
          firstReference(id, fn).orElse(args.iterator.map(pattern).collectFirst { case Some(span) =>
            span
          })
        case EA.TypePattern.Capture(ref, span, constraint) =>
          if (ref.id == id) Some(span) else constraint.flatMap(pattern)
      }
    def binderType(bt: EA.BinderType): Option[Span] =
      bt match {
        case EA.BinderType.TypePattern(tp, _)                   => pattern(tp)
        case EA.BinderType.ConstrainedCapture(_, constraint, _) => pattern(constraint)
      }
    term match {
      case EA.Term.LocalRef(local, span)                                => if (local.id == id) Some(span) else None
      case _: EA.Term.GlobalRef | _: EA.Term.NatLit | _: EA.Term.StrLit => None
      case EA.Term.Word(_, pieces, _) =>
        terms(pieces.flatMap {
          case EA.Term.WordPiece.Layer(before, after) => before ++ after
          case EA.Term.WordPiece.Splice(list)         => Vector(list)
        })
      case EA.Term.App(fn, args, _)       => terms(fn +: args)
      case EA.Term.Proj(base, _, _, _, _) => firstReference(id, base)
      case EA.Term.Body(lets, res, _) =>
        terms(lets.flatMap(let => let.ty.toVector :+ let.value) :+ res)
      case EA.Term.Match(scrut, motive, cases, _, _, _) => terms((scrut +: motive.toVector) ++ cases.map(_.body))
      case EA.Term.Pi(binders, out, _, _, _) =>
        binders.iterator
          .map(b => binderType(b.ty))
          .collectFirst { case Some(span) => span }
          .orElse(firstReference(id, out))
      case EA.Term.Lam(ty, body, _, _, _, _, _) => firstReference(id, ty).orElse(firstReference(id, body))
    }
  }
}
