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
    // different key (`StructEta`).
    (value.tpe.tpe == PropTpe) || StructEta.eligible(value.tpe).isDefined ||
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

  case class NeutralThunk(term: ElabAst.Term.Match, env: Env, id: ValueId.LocalId, tpe: Value, blockerIds: DepSet)
    extends Value {
    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(envDeps(env))
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
   * Structure eta for an eligible family (`StructEta`): its one constructor's name; a template of its telescope, opened
   * once on fresh variables (`templateIds`), as the family arguments of its result (`resultArgs`) and its stored fields
   * (`fieldVars`), whose types state each field's type in terms of the arguments and the earlier fields; and one
   * canonical projector per field.
   */
  final case class EtaInfo(
      ctorName: String,
      resultArgs: Vector[Value],
      fieldVars: Vector[Value],
      templateIds: DepSet,
      projectors: Vector[ElabAst.Term.Match]
  ) {
    def fieldCount: Int = fieldVars.length
  }

  /**
   * `selectable` holds for a family with one constructor, which has a selector for each named field; `eta` for one that
   * also has no indices and no recursive field, and is not in `Prop`. The family's arguments are its `paramCount`
   * parameters, then its indices.
   */
  final case class InductiveMeta(
      constructors: Vector[ConstructorMeta],
      familyArity: Int,
      paramCount: Int,
      selectable: Boolean,
      positiveArgs: DepSet,
      eta: Option[EtaInfo] = None
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
