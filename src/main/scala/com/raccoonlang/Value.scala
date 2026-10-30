package com.raccoonlang

/**
 * Represents a typechecked value representation - the values that live in an Env. Values can contain Vars(), which
 * represent unknown values. Vars have a unique id, which means they can participate in equality. Thus values could be
 * thought of as a typed, maximally reduced representation of CoreAst / ElabAst. Invariants:
 *   - Every value is typed correctly. Types are themselves Values, and so are Sorts and Levels
 *   - synDeps is the set of all VarIds that this Value contains, including in its type. It is extremely important to
 * maintain this correctly
 *   - key - a structural hash key of this value. Lazily computed by ValueKey.orderKey(). Used by defEq and Normalizers
 *   - needsStructuralDefEq: tracks values whose key may differ even when structural equality can still succeed
 */
sealed trait Value {
  def tpe: Value
  def synDeps: DepSet

  final lazy val key: ValueKey.Key = ValueKey.orderKey(this)
  final lazy val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)

  override def toString: String = PrettyPrinter.print(this)
}

sealed trait TopLevelValue extends Value {
  override val synDeps: DepSet = DepSet.empty
}

object Value {

  private[raccoonlang] def needsStructuralDefEq(value: Value): Boolean = {
    // If this is a proof then we fall back to structural; a value at a structure eta type may convert with one of a
    // different key (`StructEta`). A proof call is a proof, decided without computing its proposition.
    value.isInstanceOf[VProofCall] || (value.tpe.tpe == PropTpe) || StructEta.eligible(value.tpe).isDefined ||
    (value match {
      case _: VPi | _: VLam | _: NeutralThunk => true
      case app: VApp =>
        app.head.needsStructuralDefEq || app.args.exists(_.needsStructuralDefEq) || app.tpe.needsStructuralDefEq
      case poly: VNatPoly => poly.form.needsStructuralDefEq
      case word: VWord    => word.repr.needsStructuralDefEq
      case _              => false
    })
  }

  type VarId = Int

  // Identifier for lambdas to shortcut equality when possible.
  sealed trait ValueId

  object ValueId {
    final case class Const(name: String) extends ValueId {
      override def toString: String = name
    }

    final case class LocalId(nodeId: NodeId, captures: Vector[Value]) extends ValueId
  }

  /** An interned canonical match code (`MatchIdentity`): one object, and one serial, per code in the process. */
  final class MatchCode private[raccoonlang] (val serial: Long) {
    override def toString: String = s"MatchCode($serial)"
  }

  /**
   * A stuck match's identity (docs/kernel.md, "Stuck matches"): its code, and the values of its free locals in the
   * order the code first mentions them (`MatchIdentity.Layout`). Two identities with one code and convertible captures
   * evaluate the same code on convertible values, so their matches convert.
   */
  final case class MatchId(code: MatchCode, captures: Vector[Value])

  /**
   * The ids among `among` that `value` depends on as eager evaluation built it: its dependencies, read from the sources
   * each form's `synDeps` reads, with every proof call's (`VProofCall`) replaced by its forced value's. A proof call's
   * own dependencies over-approximate its forced value's, so a decision that a dependency makes more conservative, an
   * occurs check, a positivity or eta check, or instance search's test of a solved argument, confirms the dependency
   * here before it acts on it (docs/kernel.md, "Proof calls"). This forces the proof calls whose dependencies meet
   * `among`, and visits a shared part once; a part whose `synDeps` misses `among` is skipped, since those include the
   * forced values'.
   */
  private[raccoonlang] def forcedDeps(value: Value, among: DepSet): DepSet = {
    val found = DepSet.newBuilder
    val visited = new java.util.IdentityHashMap[AnyRef, java.lang.Boolean]()
    def first(part: AnyRef): Boolean = visited.put(part, java.lang.Boolean.TRUE) == null
    def ids(deps: DepSet): Unit = found.unionInPlace(deps & among)
    def env(e: Env): Unit = if (first(e)) e.locals.foreach(_.valueOption.foreach(walk))
    def captures(id: ValueId): Unit =
      id match {
        case ValueId.LocalId(_, values) => values.foreach(walk)
        case ValueId.Const(_)           =>
      }
    def walk(v: Value): Unit =
      if (v.synDeps.intersects(among) && first(v))
        v match {
          case call: VProofCall    => walk(Interpreter.force(call))
          case variable: Var       => ids(variable.reductionBlockers); walk(variable.tpe)
          case _: Level | _: Kind  => ids(v.synDeps)
          case VUniv(kind, level)  => walk(kind); walk(level)
          case VConst(_, _, tpe)   => walk(tpe)
          case app: VApp           => walk(app.head); app.args.foreach(walk); walk(app.tpe)
          case thunk: NeutralThunk => env(thunk.env); walk(thunk.tpe); thunk.id.captures.foreach(walk)
          case lam: VLam           => walk(lam.tpe); lamEnv(lam.body); captures(lam.id)
          case pi: VPi             => captures(pi.id)
          case poly: VNatPoly      => poly.form.operands.foreach(walk)
          case word: VWord =>
            packed.Words.foreach(word)(
              layer = token => {
                (0 until token.payloadWidth).foreach(index => walk(token.payload(index)))
                walk(token.tpe)
                true
              },
              end = token => {
                walk(token.value)
                true
              }
            )
          case _: TopLevelValue => // no dependencies
        }
    def lamEnv(body: LamBody): Unit =
      body match {
        case LamBody.Core(_, e)      => env(e)
        case LamBody.Native(_, e, _) => env(e)
      }
    walk(value)
    found.result()
  }

  private[raccoonlang] def envDeps(env: Env): DepSet = {
    val res = DepSet.newBuilder
    env.locals.foreach(_.valueOption.foreach(value => res.unionInPlace(value.synDeps)))
    res.result()
  }

  sealed trait LamBody {
    def synDeps: DepSet
  }
  object LamBody {
    final case class Core(term: ElabAst.Term.Lam, env: Env) extends LamBody {
      override lazy val synDeps: DepSet = envDeps(env)
    }
    final case class Native(run: (Vector[Value], Env) => Value, env: Env, isRawRecursive: Boolean) extends LamBody {
      override lazy val synDeps: DepSet = envDeps(env)
    }
  }

  case object LevelTpe extends TopLevelValue {
    override def tpe: Value = TypeTpe
  }

  /** The type of kinds (docs/kernel.md, "Kinds"), a kernel sort like `Level`. */
  case object KindTpe extends TopLevelValue {
    override def tpe: Value = TypeTpe
  }

  case object KernelObject extends TopLevelValue {
    override def tpe: Value = KernelObject
  }

  // Represents max(var1 + k1, var2 + k2... , c)
  // Invariant: all offsets are non-negative, c is non-negative, and c is either 0 or c > k1...kn.
  final class Level private (val atoms: Map[VarId, Int], val c: Int) extends Value {
    override val tpe: Value = LevelTpe

    override lazy val synDeps: DepSet = DepSet.from(atoms.keys)

    override def equals(obj: Any): Boolean =
      obj match {
        case other: Level => atoms == other.atoms && c == other.c
        case _            => false
      }

    override def hashCode(): Int = 31 * atoms.hashCode() + c
  }
  object Level {
    def of(atoms: Map[VarId, Int], c: Int): Level = {
      require(c >= 0, s"Level constant must be non-negative: $c")
      require(atoms.values.forall(_ >= 0), s"Level atom offsets must be non-negative: $atoms")

      val nextC =
        if (atoms.nonEmpty && c <= atoms.values.max) 0
        else c
      new Level(atoms, nextC)
    }

    def const(c: Int): Level = of(Map.empty, c)

    def addOffset(l: Level, offset: Int): Level = {
      if (offset == 0) l
      else {
        val newAtoms = l.atoms.map { case (varId, k) => (varId, k + offset) }
        val newC = if (l.c > 0 || l.atoms.isEmpty) l.c + offset else 0
        of(newAtoms, newC)
      }
    }

    /**
     * Check if Level covers offset - that is, is it safe to subtract offset from level.
     */
    def geq(l: Level, offset: Int): Boolean =
      l.atoms.values.forall(k => k >= offset) && (l.c >= offset || (l.c == 0 && l.atoms.nonEmpty))

    def succ(l: Level): Level = addOffset(l, 1)

    def max(xs: Vector[Level]): Level = {
      require(xs.nonEmpty, "Level.max requires at least one level")

      val flatAtoms = xs.flatMap(_.atoms)
      val nextAtoms = flatAtoms.foldLeft(Map.empty[VarId, Int]) { case (curMap, (varId, k)) =>
        val curK = curMap.getOrElse(varId, 0)
        curMap + (varId -> math.max(curK, k))
      }
      val cMax = xs.map(_.c).max
      val kMax = if (nextAtoms.nonEmpty) nextAtoms.values.max else 0
      val nextC = if (cMax > kMax) cMax else 0
      of(nextAtoms, nextC)
    }

    def leq(l1: Level, l2: Level): Boolean = {
      (l1.c <= l2.c || l2.atoms.values.exists(_ >= l1.c)) &&
      l1.atoms.forall { case (varId, k) => k <= l2.atoms.getOrElse(varId, -1) }
    }

    def mk(varId: VarId): Level = of(Map(varId -> 0), 0)

    val zero = const(0)
    val one = const(1)

  }

  /**
   * A kind (docs/kernel.md, "Kinds"): `Kind.lin`, or a finite set of kind variables, where the empty set is
   * `Kind.copy`. This is the normal form of `Kind.join`: joins with `copy` vanish, and a join with `lin` is `lin`, so
   * `copy < lin` with the variables between them, ordered by inclusion.
   */
  final class Kind private (val vars: Set[VarId], val lin: Boolean) extends Value {
    override val tpe: Value = KindTpe

    override lazy val synDeps: DepSet = DepSet.from(vars)

    /** Provably `copy`: no variable can make it linear. */
    def isCopy: Boolean = !lin && vars.isEmpty

    override def equals(obj: Any): Boolean =
      obj match {
        case other: Kind => lin == other.lin && vars == other.vars
        case _           => false
      }

    override def hashCode(): Int = 31 * vars.hashCode() + lin.hashCode()
  }

  object Kind {
    val copy: Kind = new Kind(Set.empty, lin = false)
    val lin: Kind = new Kind(Set.empty, lin = true)

    def mk(varId: VarId): Kind = new Kind(Set(varId), lin = false)

    def join(a: Kind, b: Kind): Kind =
      if (a.lin || b.lin) lin
      else if (a.vars.isEmpty) b
      else if (b.vars.isEmpty) a
      else new Kind(a.vars ++ b.vars, lin = false)

    /** `a ≤ b` in the kind lattice: `b` is `lin`, or `a` is not and its variables are among `b`'s. */
    def leq(a: Kind, b: Kind): Boolean = b.lin || (!a.lin && a.vars.subsetOf(b.vars))
  }

  sealed trait Universe extends Value

  /**
   * The universe `Univ(kind, level)` (docs/kernel.md, "Kinds"): its types are of kind `kind`, and they are linear when
   * the kind is not provably `copy`. `Sort(l)` and `Lin(l)` name `Univ(Kind.copy, l)` and `Univ(Kind.lin, l)`.
   * Universes are not cumulative: a type is used at exactly its universe.
   */
  final case class VUniv(kind: Kind, level: Level) extends Universe {
    override def tpe: Value = VUniv(Kind.copy, Level.succ(level))

    override lazy val synDeps: DepSet = kind.synDeps ++ level.synDeps
  }

  /** `Sort(level)`, the universe of copyable types: `Univ(Kind.copy, level)`. */
  object VSort {
    def apply(level: Level): VUniv = VUniv(Kind.copy, level)

    def unapply(value: Value): Option[Level] =
      value match {
        case VUniv(kind, level) if kind.isCopy => Some(level)
        case _                                 => None
      }
  }

  final val TypeTpe: VUniv = VSort(Level.zero)

  /** `Lin(level)`, the universe of linear types: `Univ(Kind.lin, level)`. */
  object VLin {
    def apply(level: Level): VUniv = VUniv(Kind.lin, level)

    def unapply(value: Value): Option[Level] =
      value match {
        case VUniv(kind, level) if kind.lin => Some(level)
        case _                              => None
      }
  }

  case object PropTpe extends Universe with TopLevelValue {
    override def tpe: Value = TypeTpe
  }

  sealed trait CaptureType
  case object StructuralCapture extends CaptureType

  /**
   * The level of a universe, less `subtract`. It opens on a universe of any kind; the binder's type, checked by
   * conversion after the captures open, then fixes the kind.
   */
  case class LevelCapture(subtract: Int) extends CaptureType

  /** The kind of a universe, `$k` in `Univ($k, $u)`. */
  case object KindCapture extends CaptureType

  sealed trait CaptureRoot
  case object ActualType extends CaptureRoot
  case object ActualTypeClassifier extends CaptureRoot

  case class VCapture(
      localRef: CoreAst.LocalRef,
      path: List[Int],
      captureType: CaptureType,
      root: CaptureRoot = ActualType
  )

  case class VBinder(
      localRef: CoreAst.LocalRef,
      ty: ElabAst.BinderType,
      captures: Vector[Value.VCapture],
      isInstance: Boolean = false
  ) {
    def name: String = localRef.name
  }

  case class VPi(
      env: Env,
      binders: Vector[VBinder],
      codomain: Env => Value,
      synDeps: DepSet,
      id: ValueId,
      tpe: Universe
  ) extends Value {
    require(binders.nonEmpty, "VPi requires at least one binder")
  }

  case class VConst(name: String, constType: ConstType, tpe: Value) extends Value {
    override lazy val synDeps: DepSet = tpe.synDeps
  }

  /**
   * A published Nat normal form that is neither zero nor a lone unit atom, constructed only by `Form.toValue`, which
   * caches it. Every positive Nat constant and every successor is one of these, so equal forms have equal keys unless
   * an atom needs structural conversion. A primitive sum used as a factor base is also one of these, with its own key,
   * dependencies, and quotation. Dependencies come from the form's shared terms.
   */
  final class VNatPoly private[raccoonlang] (val form: NatNormalForm.Form) extends Value {
    override def tpe: Value = Kernel.natType

    override def synDeps: DepSet = form.synDeps
  }

  case class VApp(head: Value, args: Vector[Value], tpe: Value, blockerIds: DepSet = DepSet.empty) extends Value {
    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(head.synDeps)
      args.foreach(v => res.unionInPlace(v.synDeps))
      res.unionInPlace(tpe.synDeps)
      res.result()
    }

    require(args.nonEmpty || blockerIds.isEmpty, "Blocked application requires at least one argument")
    head match {
      case h: ConstructorHead =>
        require(blockerIds.isEmpty, s"Constructor ${h.name} cannot be blocked")
        require(
          args.length != 1 || h.name != Kernel.SuccName,
          "Nat successors are compact; construct them through ConstructorValue"
        )
        require(h.listShape.isEmpty, s"${h.name} applications are words; construct them through ConstructorValue")
        require(
          args.length == h.totalArity - h.numErased,
          s"Constructor ${h.name} stores ${args.length} fields, expected ${h.totalArity - h.numErased}"
        )
      case _ =>
    }
  }

  /**
   * A word of a list-shaped type (docs/packed_lists.md, "Words"): one or more cons layers, packed in shared storage,
   * followed by an end that is not a word. Every cons application of a list-shaped type is a word, never a `VApp`, so a
   * word is constructor data, never stuck, and is observed through `ConstructorValue` like any constructor value.
   * Storage is otherwise invisible: equal words may be divided and stored differently, and keys depend only on their
   * layers and end. The representation belongs to `packed.Words`, the only code that builds or reads words; this class
   * only delegates to it.
   */
  final class VWord private[raccoonlang] (val repr: packed.Word) extends Value {
    override def tpe: Value = repr.tpe

    override def synDeps: DepSet = repr.synDeps
  }

  /**
   * A suspended proof call (docs/kernel.md, "Proof calls"): the checked lambda `fn`, whose function type is a
   * proposition, applied to `args`, not yet run. Only `Interpreter.evalApply` builds one, where eager evaluation would
   * run `fn`, and materialization rebuilds one; `args` fit `fn` 's binders, as a checked application's do. It stands
   * for the value that running `fn` on `args` gives, its forced value, which `Interpreter.force` computes once, on
   * demand, and memoizes in `forced`. Every reader of a proof's form forces it first, as docs/kernel.md lists: a match,
   * an application, the checker's known-constructor view, the key, quotation, printing and the walks over a value's
   * form.
   *
   *   - Its type is `fn` 's codomain at `args`, computed when first read, without running `fn`. Eager evaluation took
   *     the forced value's own type instead. The two are convertible, since `fn` 's body checked against its codomain,
   *     and are the same normal form outside proofs and functions inside them; every reader of a proof's type reads it
   *     by conversion or by its universe, or forces the proof first.
   *   - Its dependencies are `fn` 's and `args` ', computed without forcing. Evaluation introduces no free variable, so
   *     they include those of its type and of its forced value: an over-approximation of the forced value's, which may
   *     add only variables in no rigid position of either. A decision that a dependency makes more conservative
   *     confirms it through forced values (`forcedDeps`), and a link holds the calls that mention its variable forced
   *     (`EqStore.linkable`).
   *   - Its key is its forced value's (`ValueKey`), so equal keys still mean convertible values, and termination
   *     checking compares proofs as it compared the forced values.
   */
  final class VProofCall private[raccoonlang] (val fn: VLam, val args: Vector[Value]) extends Value {
    override lazy val tpe: Value = Interpreter.applicationType(fn.tpe, args)

    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(fn.synDeps)
      args.foreach(v => res.unionInPlace(v.synDeps))
      res.result()
    }

    /**
     * The forced value once `Interpreter.force` has computed it, or materialization has carried it over from the call
     * it rebuilt; never itself a proof call, and `null` before.
     */
    private[raccoonlang] var forced: Value = null
  }


  /**
   * A stuck match: `term` closed over `env`, a value of `tpe`, its motive, waiting on `blockerIds`. `env` keeps exactly
   * the locals whose values `id` captures (`Interpreter.stuckMatch`), and materialization maps both alike, so the
   * captures are everything the match reads.
   */
  case class NeutralThunk(term: ElabAst.Term.Match, env: Env, id: MatchId, tpe: Value, blockerIds: DepSet)
    extends Value {
    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(tpe.synDeps)
      id.captures.foreach(v => res.unionInPlace(v.synDeps))
      res.result()
    }
  }

  case class Var(name: String, id: VarId, tpe: Value) extends Value {
    override lazy val synDeps: DepSet = tpe.synDeps + id

    /** The variable alone, without its type's dependencies; it blocks applications of and matches on it. */
    lazy val reductionBlockers: DepSet = DepSet.single(id)
  }

  case class VLam(
      tpe: VPi,
      id: ValueId,
      body: LamBody
  ) extends Value {
    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(tpe.synDeps)
      res.unionInPlace(body.synDeps)
      id match {
        case ValueId.Const(_) => res.result()
        case ValueId.LocalId(_, params) =>
          if (params.isEmpty) res.result()
          else {
            params.foreach(v => res.unionInPlace(v.synDeps))
            res.result()
          }
      }
    }

  }

  /**
   * The shape of a list-shaped type's cons constructor (see `InductiveChecks.listShape`): the index of its one
   * recursive field among its stored fields, and the number of other stored fields, which form the payload of each
   * layer.
   */
  final case class ListShape(recursiveIndex: Int, payloadWidth: Int) {
    require(recursiveIndex >= 0 && recursiveIndex <= payloadWidth, "List recursive field index must be a stored field")
  }

  /** `listShape` is present exactly on the cons constructor of a list-shaped type, whose applications are words. */
  case class ConstructorHead(
      name: String,
      erasedFamilyArgIndexes: Vector[Int],
      totalArity: Int,
      tpe: Value,
      listShape: Option[ListShape]
  ) extends TopLevelValue {
    require(erasedFamilyArgIndexes.forall(_ >= 0), "Constructor erased family arg indexes must be non-negative")
    require(
      erasedFamilyArgIndexes.distinct.length == erasedFamilyArgIndexes.length,
      "Constructor erased family arg indexes must be distinct"
    )

    def numErased: Int = erasedFamilyArgIndexes.length
  }

  final case class ConstructorMeta(shortName: String, canonicalName: String)

  /**
   * A record (docs/kernel.md, "Structure eta and projections"): a family with exactly one constructor, `ctorName`,
   * whose stored fields are named `fieldNames`, an anonymous one `_`. Each stored field has one canonical projector
   * (`StructEta`), and `base.field` projects a named one. `template` is the constructor's telescope opened once on
   * fresh variables (`StructEta.Template`), from which `StructEta` states a field's type at a value.
   *
   * `eta` holds when the record is also eligible for structure eta: `etaShape`, no indices, no recursive field and not
   * in `Prop`, and every field's type determined by the arguments of the family, of type `familyType`, and the earlier
   * fields. A recursive field's type names the family itself, so the template is read from the published constructor,
   * which `constructor` gives; `InductiveChecks` forces the template and `eta` once the family's block is published.
   */
  final class RecordInfo(
      val ctorName: String,
      val fieldNames: Vector[String],
      etaShape: Boolean,
      familyType: Value,
      constructor: () => ConstructorHead
  ) {
    val projectors: Vector[ElabAst.Term.Match] = StructEta.projectors(ctorName, fieldNames)

    lazy val template: StructEta.Template = StructEta.template(constructor())

    // A record that is not eta-shaped has no eta whatever its template, which is then not read here: a recursive
    // field's type names the family, whose eta this would ask while the template is opened.
    lazy val eta: Boolean = etaShape && StructEta.determined(template, familyType)

    def fieldCount: Int = fieldNames.length

    /** The stored field named `name`. An anonymous field has no name to select it by. */
    def fieldIndex(name: String): Option[Int] =
      if (name == "_") None else Some(fieldNames.indexOf(name)).filter(_ >= 0)
  }

  /**
   * `record` is present exactly for a family with one constructor (`RecordInfo`). The family's arguments are its
   * `paramCount` parameters, then its indices.
   */
  final case class InductiveMeta(
      constructors: Vector[ConstructorMeta],
      familyArity: Int,
      paramCount: Int,
      positiveArgs: DepSet,
      record: Option[RecordInfo] = None
  ) {
    require(
      positiveArgs.isEmpty || positiveArgs.max < familyArity,
      "Inductive positive argument indexes must be in range"
    )
    require(paramCount >= 0 && paramCount <= familyArity, "Inductive parameters are a prefix of its arguments")

    lazy val constructorNames: Vector[String] = constructors.map(_.canonicalName)
  }

  sealed trait ConstType
  case class Inductive(meta: InductiveMeta) extends ConstType
  case object Symbol extends ConstType

  /**
   * The head of a protocol primitive's canonical value (`ProtocolPrimitives`): `supply#`, `inst#`, `tok#` or `valid#`.
   * Only `ProtocolPrimitives` builds ghosts: the primitives' natives, and the root supply that `Interpreter.run` gives
   * an entry. They are always applied, each application carrying its precise type and, in its arguments, everything
   * that type depends on, since keys ignore types. No environment binds a ghost and its name is no identifier, so no
   * source term names one; quotation refuses them (`ValueQuote`). They convert by congruence only.
   */
  case object Ghost extends ConstType

  /**
   * Views over values.
   */

  object VBlockedApp {
    def apply(head: Value, args: Vector[Value], tpe: Value, blockerIds: DepSet): VApp =
      VApp(head, args, tpe, blockerIds)

    def unapply(value: Value): Option[(Value, Vector[Value], Value, DepSet)] =
      value match {
        case VApp(head, args, tpe, blockers) if blockers.nonEmpty => Some((head, args, tpe, blockers))
        case _                                                    => None
      }
  }

  /**
   * Constructor applications stored as a `VApp`. This is a view of storage, not of data: a cons of a list-shaped type
   * is a `VWord`, and a Nat successor is compact. Readers of constructor values use `ConstructorValue`.
   */
  object VCtor {
    def apply(head: ConstructorHead, fields: Vector[Value], tpe: Value): VApp = VApp(head, fields, tpe)

    def unapply(value: Value): Option[(ConstructorHead, Vector[Value], Value)] =
      value match {
        case VApp(head: ConstructorHead, fields, tpe, blockers) if blockers.isEmpty => Some((head, fields, tpe))
        case _                                                                      => None
      }
  }

  /** Dependencies that can make reduction progress; these grant no permission to refine variables. */
  object ReductionBlockers {
    def of(value: Value): DepSet =
      value match {
        case variable: Var                             => variable.reductionBlockers
        case VBlockedApp(_, _, _, ids)                 => ids
        case NeutralThunk(_, _, _, _, ids)             => ids
        case poly: VNatPoly if poly.form.constant == 0 => poly.synDeps // no known successor
        case _                                         => DepSet.empty
      }

    def unapply(value: Value): Option[DepSet] = {
      val blockers = of(value)
      if (blockers.isEmpty) None else Some(blockers)
    }
  }

  object Blocked {
    def unapply(value: Value): Option[DepSet] =
      value match {
        case VBlockedApp(_, _, _, ids)                     => Some(ids)
        case NeutralThunk(_, _, _, _, ids) if ids.nonEmpty => Some(ids)
        case _                                             => None
      }
  }

  object ConstSpine {
    def unapply(value: Value): Option[(VConst, Vector[Value])] =
      value match {
        case c: VConst                                                 => Some((c, Vector.empty))
        case VApp(head: VConst, args, _, blockers) if blockers.isEmpty => Some((head, args))
        case _                                                         => None
      }
  }

  final case class InductiveFamilyInstance(head: VConst, meta: InductiveMeta, args: Vector[Value])

  object InductiveFamilyValue {
    def unapply(value: Value): Option[InductiveFamilyInstance] =
      value match {
        case ConstSpine(head @ VConst(_, Inductive(meta), _), args) if args.length == meta.familyArity =>
          Some(InductiveFamilyInstance(head, meta, args))
        case _ => None
      }
  }

}
