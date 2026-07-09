package com.raccoonlang

/**
 * Represents a typechecked value representation - the values that live in an Env[Value]. Values can contain Vars(),
 * which represent unknown values. Vars have a unique id, which means they can participate in equality. Thus values
 * could be thought of as a typed, maximally reduced representation of CoreAst / ElabAst. Invariants:
 *   - Every value is typed correctly. Types are themselves Values, and so are Sorts and Levels
 *   - synDeps is the set of all VarIds that this Value contains, including in its type. It is extremely important to
 * maintain this correctly
 *   - key - a structural hash key of this value. Lazily computed by ValueKey.orderKey(). Used by defEq
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
  /**
   * Replace a neutral's remembered type with a defEq (or sort-cumulative) representative the
   * context knows to be more informative — typically the declared/expected type winning over the
   * inferred one. Canonical values determine their own types and pass through; neutrals
   * (`UpdatableType`) only carry an annotation recorded at creation, and syntax-directed machinery
   * (`evalApply`'s Pi dispatch, universe classification, keys) reads that annotation structurally,
   * so the representative matters. Also the deferred proof-collapse point: the ascription is often
   * the moment a value's type becomes *known* propositional (proof-collapse.md §3-4).
   */
  def ascribe(value: Value, tpe: Value): Value =
    value match {
      case u: UpdatableType => collapseIfProof(u.withTpe(tpe))
      case _                => value
    }

  /**
   * The value's type is a proposition: it lives in `Prop`. The sort `Prop` itself never qualifies
   * (`Prop : Sort 1`) — predicates are data, not proofs (kernel-theory §2).
   */
  def isPropositionType(tpe: Value): Boolean =
    tpe match {
      case PropTpe => false
      case tpe     => tpe.tpe == PropTpe
    }

  private def isKnownProof(value: Value): Boolean = isPropositionType(value.tpe)

  /**
   * Collapse a value whose type is a known proposition into the structureless `VProof` form
   * (docs/proof-collapse.md). Callers must present an existing inhabitant — collapse is erasure,
   * never creation (witness invariant). Exemptions:
   *   - `Var`: metas and unification unknowns must stay refinable — collapsing a placeholder would
   *     silently discharge a proof obligation. Rigid hypotheses are collapsed at binder freshening
   *     instead, where the binder itself is the witness (`collapseBinderWitness` below).
   *   - `ConstructorHead`: heads must remain applicable and recognizable by match machinery;
   *     their saturated applications collapse in `Interpreter.evalApply`.
   *   - raw-recursive `VLam`: the native body enforces the decrease check on every application;
   *     hiding it inside a `VProof` would disable termination checking for recursive proofs.
   */
  def collapseIfProof(value: Value): Value =
    if (!isPropositionType(value.tpe)) value
    else
      value match {
        case _: VProof | _: Var | _: ConstructorHead => value
        case VLam(_, _, LamBody.Native(_, _, true))  => value
        case _                                       => VProof(value.tpe, value)
      }

  /**
   * Collapse a freshened *rigid* binder: the bound hypothesis is its own witness
   * (proof-collapse.md §4). Counterpart to collapseIfProof's `Var` exemption — a bare fresh Var
   * is a refinable meta there and must not collapse, but here the Var is a rigid hypothesis being
   * bound, so it does. InstanceSearch's witness-invariant guard relies on rigid proof binders
   * being observably `VProof`.
   */
  def collapseBinderWitness(tpe: Value, fresh: Value): Value =
    if (isPropositionType(tpe)) VProof(tpe, fresh) else fresh

  private[raccoonlang] def needsStructuralDefEq(value: Value): Boolean =
    isKnownProof(value) || (value match {
      case _: VPi | _: VLam | _: NeutralThunk => true
      case app: VApp =>
        app.head.needsStructuralDefEq || app.args.exists(_.needsStructuralDefEq) || app.tpe.needsStructuralDefEq
      case _ => false
    })

  sealed trait UpdatableType {
    def withTpe(tpe: Value): Value
  }

  type VarId = Int

  // Identifier for lambdas to shortcut equality when possible.
  sealed trait ValueId

  object ValueId {
    final case class Const(name: String) extends ValueId {
      override def toString: String = name
    }

    final case class LocalId(nodeId: AstNodeId, captures: Vector[Value]) extends ValueId
  }

  private[raccoonlang] def envDeps(env: Env[Value]): DepSet = {
    val res = DepSet.newBuilder
    env.locals.values.foreach(value => res.unionInPlace(value.synDeps))
    res.result()
  }

  sealed trait LamBody {
    def synDeps: DepSet
  }
  object LamBody {
    final case class Core(term: ElabAst.Term.Lam, env: Env[Value]) extends LamBody {
      override lazy val synDeps: DepSet = envDeps(env)
    }
    final case class Native(run: (Vector[Value], Env[Value]) => Value, env: Env[Value], isRawRecursive: Boolean)
      extends LamBody {
      override lazy val synDeps: DepSet = envDeps(env)
    }
  }

  case object LevelTpe extends TopLevelValue {
    override def tpe: Value = TypeTpe
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

  case class VSort(level: Level) extends Value {
    override def tpe: Value = VSort(Level.succ(level))

    override lazy val synDeps: DepSet = level.synDeps
  }

  final val PropTpe: VSort = VSort(Level.zero)
  final val TypeTpe: VSort = VSort(Level.one)

  case class VBinder(
      localRef: CoreAst.LocalRef,
      ty: ElabAst.TypeTerm,
      isImplicit: Boolean = false,
      isInstance: Boolean = false
  ) {
    def name: String = localRef.name
  }

  // numLevelParams: the telescope is zoned [level implicits][other implicits][explicits];
  // the first numLevelParams binders are the implicit Level binders.
  case class VPi(
      env: Env[Value],
      binders: Vector[VBinder],
      codomain: Env[Value] => Value,
      synDeps: DepSet,
      id: ValueId,
      tpe: VSort,
      numLevelParams: Int
  ) extends Value
    with UpdatableType {
    require(binders.nonEmpty, "VPi requires at least one binder")
    require(
      numLevelParams >= 0 && numLevelParams <= binders.length,
      "VPi level parameter count must be within the telescope"
    )

    override def toString: String = "VPi"

    override def withTpe(tpe: Value): Value = tpe match {
      case u: VSort => this.copy(tpe = u)
      case _        => throw WTF(s"Cannot update Pi type to $tpe")
    }
  }

  case class VConst(name: String, constType: ConstType, tpe: Value) extends Value with UpdatableType {
    override lazy val synDeps: DepSet = tpe.synDeps

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  case class VApp(head: Value, args: Vector[Value], tpe: Value, blockerId: Option[VarId] = None)
    extends Value
    with UpdatableType {
    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(head.synDeps)
      args.foreach(v => res.unionInPlace(v.synDeps))
      res.unionInPlace(tpe.synDeps)
      res.result()
    }

    require(args.nonEmpty || blockerId.isEmpty, "Blocked application requires at least one argument")
    head match {
      case h: ConstructorHead =>
        require(blockerId.isEmpty, s"Constructor ${h.name} cannot be blocked")
        val expectedArgs = h.totalArity - h.numErasedFamilyArgs
        require(
          args.length == expectedArgs,
          s"Constructor ${h.name} stores ${args.length} args, expected $expectedArgs"
        )
      case _ =>
    }

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  case class NeutralThunk(
      term: ElabAst.Term.Match,
      env: Env[Value],
      id: ValueId.LocalId,
      tpe: Value,
      blockerId: Option[VarId]
  ) extends Value
    with UpdatableType {
    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(envDeps(env))
      res.unionInPlace(tpe.synDeps)
      id.captures.foreach(v => res.unionInPlace(v.synDeps))
      res.result()
    }

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  case class Var(name: String, id: VarId, tpe: Value) extends Value with UpdatableType {
    override lazy val synDeps: DepSet = tpe.synDeps + id

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  case class VLam(
      tpe: VPi,
      id: ValueId,
      body: LamBody
  ) extends Value
    with UpdatableType {
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

    override def withTpe(nextTpe: Value): Value = nextTpe match {
      case pi: VPi if pi.binders.map(_.localRef) == tpe.binders.map(_.localRef) => this.copy(tpe = pi)
      case _: VPi                                                               => this
      case _ => throw WTF(s"Cannot update lambda type to $nextTpe")
    }

  }

  /**
   * The single value form for proofs: every value whose type is *known* to be a proposition is a
   * `VProof` (collapse invariant, docs/proof-collapse.md §3). Proofs have no structure to read, so
   * proof-irrelevance violations are unrepresentable rather than guarded against; defEq of two
   * proofs is defEq of their propositions.
   *
   * `witness0` is the erased inhabitant this proof was collapsed from. It is excluded from
   * equality, keys and synDeps, and is consulted only for quoting and diagnostics — never for
   * evaluation or comparison (reading it there would reintroduce irrelevance violations).
   *
   * A `VProof` is never a `Blocker`: matches on proofs do not block-and-resume.
   */
  final class VProof private (val tpe: Value, witness0: () => Value) extends Value with UpdatableType {
    require(isPropositionType(tpe), s"VProof requires a proposition, got a value of $tpe")

    override lazy val synDeps: DepSet = tpe.synDeps

    lazy val witness: Value = witness0()

    // Ascription may retype at a defEq type that is not *known* to be a proposition (e.g. a
    // generic-universe binder type mid-elaboration); the proof keeps its proposition then,
    // mirroring VLam.withTpe's leniency on mismatched binders.
    override def withTpe(tpe: Value): Value =
      if (isPropositionType(tpe)) new VProof(tpe, witness0) else this

    override def equals(obj: Any): Boolean =
      obj match {
        case other: VProof => tpe == other.tpe
        case _             => false
      }

    override def hashCode(): Int = 31 * tpe.hashCode() + 13
  }

  object VProof {
    def apply(tpe: Value, witness: => Value): VProof = new VProof(tpe, () => witness)

    def unapply(p: VProof): Some[Value] = Some(p.tpe)
  }

  /**
   * `noConfusion`: whether unification may assume injectivity and disjointness for this head. True for constructors of
   * genuine inductive types. False for quotient constructors: Quot.sound identifies distinct Quot.mk applications, so
   * `Quot.mk a = Quot.mk b` neither implies `a = b` nor is refutable when `a` and `b` differ.
   */
  case class ConstructorHead(
      name: String,
      numErasedFamilyArgs: Int,
      totalArity: Int,
      tpe: Value,
      noConfusion: Boolean = true
  ) extends TopLevelValue
    with UpdatableType {
    require(numErasedFamilyArgs >= 0, "Constructor erased family argument count must be non-negative")
    require(numErasedFamilyArgs <= totalArity, "Constructor erased family argument count cannot exceed total arity")

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
  }

  private[raccoonlang] def constructorStoredArgs(head: ConstructorHead, args: Vector[Value]): Vector[Value] = {
    if (args.length != head.totalArity)
      throw WTF(s"Constructor ${head.name} was given ${args.length} args, expected ${head.totalArity}")
    args.drop(head.numErasedFamilyArgs)
  }

  private[raccoonlang] def constructorPatternArgs(head: ConstructorHead, args: Vector[Value]): Vector[Value] =
    head.tpe match {
      case pi: VPi =>
        val storedBinders = pi.binders.drop(head.numErasedFamilyArgs)
        if (args.length != storedBinders.length)
          throw WTF(s"Constructor ${head.name} stores ${args.length} args, expected ${storedBinders.length}")
        args

      case _ =>
        val expectedArgs = head.totalArity - head.numErasedFamilyArgs
        if (args.length != expectedArgs)
          throw WTF(s"Constructor ${head.name} stores ${args.length} args, expected $expectedArgs")
        args
    }

  final case class ConstructorMeta(shortName: String, canonicalName: String)

  final case class InductiveMeta(
      constructors: Vector[ConstructorMeta],
      familyArity: Int,
      isStruct: Boolean,
      positiveArgs: DepSet
  ) {
    require(
      positiveArgs.isEmpty || positiveArgs.max < familyArity,
      "Inductive positive argument indexes must be in range"
    )

    lazy val constructorNames: Vector[String] = constructors.map(_.canonicalName)
  }

  sealed trait ConstType
  case class Inductive(meta: InductiveMeta) extends ConstType
  case object Symbol extends ConstType

  /**
   * Views over values.
   */

  object VBlockedApp {
    def apply(head: Value, args: Vector[Value], tpe: Value, blockerId: VarId): VApp =
      VApp(head, args, tpe, Some(blockerId))

    def unapply(value: Value): Option[(Value, Vector[Value], Value, VarId)] =
      value match {
        case VApp(head, args, tpe, Some(blockerId)) => Some((head, args, tpe, blockerId))
        case _                                      => None
      }
  }

  object VCtor {
    def apply(head: ConstructorHead, fields: Vector[Value], tpe: Value): VApp = VApp(head, fields, tpe)

    def unapply(value: Value): Option[(ConstructorHead, Vector[Value], Value)] =
      value match {
        case VApp(head: ConstructorHead, fields, tpe, None) => Some((head, fields, tpe))
        case _                                              => None
      }
  }

  object Blocker {
    def unapply(value: Value): Option[VarId] =
      value match {
        case Var(_, id, _)                      => Some(id)
        case VBlockedApp(_, _, _, id)           => Some(id)
        case NeutralThunk(_, _, _, _, Some(id)) => Some(id)
        case _                                  => None
      }
  }

  object Blocked {
    def unapply(value: Value): Option[VarId] =
      value match {
        case VBlockedApp(_, _, _, id)           => Some(id)
        case NeutralThunk(_, _, _, _, Some(id)) => Some(id)
        case _                                  => None
      }
  }

  object ConstSpine {
    def unapply(value: Value): Option[(VConst, Vector[Value])] =
      value match {
        case c: VConst                         => Some((c, Vector.empty))
        case VApp(head: VConst, args, _, None) => Some((head, args))
        case _                                 => None
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
