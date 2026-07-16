package com.raccoonlang

/**
 * Represents a typechecked value representation - the values that live in an Env. Values can contain Vars(), which
 * represent unknown values. Vars have a unique id, which means they can participate in equality. Thus values could be
 * thought of as a typed, maximally reduced representation of CoreAst / ElabAst. Invariants:
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
   * Replace a neutral's remembered type with a defEq (or sort-cumulative) representative the context knows to be more
   * informative — typically the declared/expected type winning over the inferred one. Canonical values determine their
   * own types and pass through; neutrals (`UpdatableType`) only carry an annotation recorded at creation, and
   * syntax-directed machinery (`evalApply`'s Pi dispatch, universe classification, keys) reads that annotation
   * structurally, so the representative matters. Also the deferred proof-collapse point: the ascription is often the
   * moment a value's type becomes *known* propositional (proof-collapse.md §§2-3). Struct expansion (StructEta)
   * deliberately does NOT run here: ascription retypes values that already circulate, and wrapping one copy while the
   * bare original lives on in envs would leave two representations that never compare equal. Proof representation
   * tolerates that (`ProofEquation` relates every proof form); expansion has no mixed rule by design, so struct values
   * are canonicalized at creation only.
   */
  def ascribe(value: Value, tpe: Value): Value =
    value match {
      case u: UpdatableType => canonicalizeProof(u.withTpe(tpe))
      case _                => value
    }

  /**
   * The value's type is a proposition: it lives in `Prop`. The sort `Prop` itself never qualifies (`Prop : Sort 1`) —
   * predicates are data, not proofs (kernel-theory §2).
   */
  def isPropositionType(tpe: Value): Boolean =
    tpe match {
      case PropTpe => false
      // Impredicativity: a Pi is a proposition exactly when its codomain is Prop-valued. Answered
      // via the dedicated lazy val so proof-collapse checks skip the full classifier computation.
      case pi: VPi => pi.isPropValued
      case tpe     => tpe.tpe == PropTpe
    }

  private def isKnownProof(value: Value): Boolean = isPropositionType(value.tpe)

  /**
   * Put a proof into the canonical representation determined solely by its exact proposition (docs/proof-collapse.md).
   * If the proposition's declaration-time recipe reconstructs a constructor at that exact type, every inhabitant uses
   * constructor form. Otherwise a Pi proposition reconstructs its eta-lambda and every other ordinary inhabitant erases
   * to `VProof`. Exemptions:
   *   - `Var`: metas and unification unknowns must stay refinable — collapsing a placeholder would silently discharge a
   *     proof obligation. Rigid hypotheses are erased at binder freshening only after the source binder has established
   *     that an inhabitant is in scope (`canonicalizeRigidBinder` below).
   *   - `ConstructorHead`: heads must remain applicable and recognizable by match machinery.
   *   - a raw-recursive `VLam`: this checker-only stub must execute its decrease guard. The checked published proof
   *     lambda is replaced by the canonical proof eta-lambda after its body has passed checking.
   */
  def canonicalizeProof(value: Value): Value =
    value match {
      // A Pi's own type is a sort, never a proposition — skip without forcing its lazy classifier.
      // Metas remain linkable, constructor heads remain applicable, and the raw recursive lambda
      // remains executable until checking has validated every recursive call.
      case _: VPi | _: Var | _: ConstructorHead   => value
      case VLam(_, _, LamBody.Native(_, _, true)) => value
      case _ if !isPropositionType(value.tpe)     => value
      // A trusted application of the declaration-certified constructor already carries the
      // result-forced data fields. Check this before running the recipe so repeated canonicalization
      // at environment boundaries is constant-time.
      case VCtor(actualHead, _, _) if ProofReconstruction.isCertifiedConstructor(value.tpe, actualHead) => value
      case _ =>
        ProofReconstruction.reconstruct(value.tpe) match {
          case Some(reconstructed) =>
            VCtor(reconstructed.head, reconstructed.fields, value.tpe)
          case None =>
            value.tpe match {
              case pi: VPi =>
                value match {
                  case VLam(_, _, LamBody.ProofEta) => value
                  case _                            => canonicalProofLambda(pi)
                }
              case _ =>
                value match {
                  case proof: VProof => proof
                  case _             => VProof(value.tpe)
                }
            }
        }
    }

  /** The unique operational shape reconstructed for every proof of a Pi proposition. */
  private def canonicalProofLambda(pi: VPi): VLam =
    VLam(pi, ValueId.LocalId(AstNodeId.synthetic(), Vector.empty), LamBody.ProofEta)

  /**
   * Canonicalize a freshened *rigid* binder (proof-collapse.md §5). Counterpart to canonicalizeProof's `Var` exemption
   * — a bare fresh Var is a refinable meta there and must not collapse, but here the Var is a rigid hypothesis being
   * bound, so its identity is checking metadata rather than runtime proof representation.
   */
  def canonicalizeRigidBinder(tpe: Value, fresh: Value): Value =
    if (isPropositionType(tpe)) canonicalizeProof(VProof(tpe)) else fresh

  private[raccoonlang] def needsStructuralDefEq(value: Value): Boolean =
    isKnownProof(value) || (value match {
      case _: VPi | _: VLam | _: NeutralThunk => true
      case app: VApp =>
        app.head.needsStructuralDefEq || app.args.exists(_.needsStructuralDefEq) || app.tpe.needsStructuralDefEq
      case p: VPacked => !p.codec.canonical
      case _          => false
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

  private[raccoonlang] def envDeps(env: Env): DepSet = {
    val res = DepSet.newBuilder
    env.locals.values.foreach(value => res.unionInPlace(value.synDeps))
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

    /** Type-directed eta expansion of a proof of Pi; its result is reconstructed from the instantiated codomain. */
    case object ProofEta extends LamBody {
      override val synDeps: DepSet = DepSet.empty
    }
  }

  case object LevelTpe extends TopLevelValue {
    override def tpe: Value = TypeTpe
  }

  // Represents max(atom1 + k1, atom2 + k2... , c), where an atom is either a level variable or an unresolved imax.
  // Invariant: all offsets are non-negative, c is non-negative, and c is either 0 or c > k1...kn. IMax atoms are
  // created only by the smart constructor below, so every level is normalized at birth.
  final class Level private (val terms: Map[Level.Atom, Int], val c: Int) extends Value {
    override val tpe: Value = LevelTpe

    // Levels are immutable and IMax atoms recursively contain Levels. Cache the Scala collection
    // hash eagerly so using a nested atom as a Map key is O(1) in the nesting depth and does not
    // recursively re-hash the entire level tree.
    private val cachedHashCode: Int = 31 * terms.hashCode() + c

    private lazy val neverZero: Boolean =
      c > 0 || terms.exists {
        case (_, offset) if offset > 0   => true
        case (Level.IMaxAtom(_, rhs), _) => rhs.neverZero
        case (_: Level.ParamAtom, _)     => false
      }

    private lazy val hasIMax: Boolean =
      terms.keysIterator.exists {
        case _: Level.IMaxAtom => true
        case _                 => false
      }

    override lazy val synDeps: DepSet = {
      val deps = DepSet.newBuilder
      terms.keys.foreach {
        case Level.ParamAtom(id) => deps.add(id)
        case Level.IMaxAtom(lhs, rhs) =>
          deps.unionInPlace(lhs.synDeps)
          deps.unionInPlace(rhs.synDeps)
      }
      deps.result()
    }

    override def equals(obj: Any): Boolean =
      obj match {
        case other: Level => cachedHashCode == other.cachedHashCode && c == other.c && terms == other.terms
        case _            => false
      }

    override def hashCode(): Int = cachedHashCode
  }
  object Level {
    sealed trait Atom
    final case class ParamAtom(id: VarId) extends Atom
    final case class IMaxAtom(lhs: Level, rhs: Level) extends Atom

    private def ofTerms(terms: Map[Atom, Int], c: Int): Level = {
      require(c >= 0, s"Level constant must be non-negative: $c")
      require(terms.values.forall(_ >= 0), s"Level atom offsets must be non-negative: $terms")

      val nextC =
        if (terms.nonEmpty && c <= terms.values.max) 0
        else c
      new Level(terms, nextC)
    }

    def of(atoms: Map[VarId, Int], c: Int): Level = {
      ofTerms(atoms.map { case (id, offset) => ParamAtom(id) -> offset }, c)
    }

    def const(c: Int): Level = ofTerms(Map.empty, c)

    def addOffset(l: Level, offset: Int): Level = {
      if (offset == 0) l
      else {
        val newTerms = l.terms.map { case (atom, k) => (atom, k + offset) }
        val newC = if (l.c > 0 || l.terms.isEmpty) l.c + offset else 0
        ofTerms(newTerms, newC)
      }
    }

    /**
     * Check if Level covers offset - that is, is it safe to subtract offset from level.
     */
    def geq(l: Level, offset: Int): Boolean =
      l.terms.values.forall(k => k >= offset) && (l.c >= offset || (l.c == 0 && l.terms.nonEmpty))

    def succ(l: Level): Level = addOffset(l, 1)

    def max(xs: Vector[Level]): Level = {
      require(xs.nonEmpty, "Level.max requires at least one level")

      val nextTerms = scala.collection.mutable.HashMap.empty[Atom, Int]
      var cMax = 0
      xs.foreach { level =>
        cMax = math.max(cMax, level.c)
        level.terms.foreach { case (atom, offset) =>
          nextTerms.get(atom) match {
            case Some(current) if offset > current => nextTerms.update(atom, offset)
            case None                              => nextTerms.update(atom, offset)
            case _                                 =>
          }
        }
      }
      ofTerms(nextTerms.toMap, cMax)
    }

    /** True when the level is positive under every assignment of its variables. */
    def isNeverZero(l: Level): Boolean = l.neverZero

    /** Lean's impredicative maximum: zero when rhs is zero, max(lhs, rhs) otherwise. */
    def imax(lhs: Level, rhs: Level): Level = {
      if (rhs == zero) zero
      else if (isNeverZero(rhs)) max(Vector(lhs, rhs))
      else if (lhs == zero || lhs == one || lhs == rhs) rhs
      else ofTerms(Map(IMaxAtom(lhs, rhs) -> 0), 0)
    }

    def containsIMax(l: Level): Boolean = l.hasIMax

    /** The exact invertible shape accepted by level unification and forced-implicit projection. */
    def singleVariableOffset(l: Level): Option[(VarId, Int)] =
      if (l.c != 0 || l.terms.size != 1) None
      else
        l.terms.head match {
          case (ParamAtom(id), offset) => Some((id, offset))
          case _                       => None
        }

    private def regularLeq(l1: Level, l2: Level): Boolean =
      (l1.c <= l2.c || l2.terms.values.exists(_ >= l1.c)) &&
        l1.terms.forall { case (atom, k) => k <= l2.terms.getOrElse(atom, -1) }

    /**
     * A sound, intentionally incomplete pointwise level bound. Pure max-levels retain the old exact fast path; imax
     * follows Lean's conservative rules: rhs <= imax(lhs, rhs), while proving imax(lhs, rhs) <= out may require both
     * operands to fit out. This is a size check for inductives, never universe subtyping.
     */
    def leq(l1: Level, l2: Level): Boolean = {
      if (!containsIMax(l1) && !containsIMax(l2)) return regularLeq(l1, l2)

      val memo = scala.collection.mutable.Map.empty[(Level, Level), Boolean]
      def constantCovered(c: Int, out: Level): Boolean =
        c <= out.c || out.terms.values.exists(_ >= c)

      def termAsLevel(atom: Atom, offset: Int): Level = ofTerms(Map(atom -> offset), 0)

      def termLeq(atom: Atom, offset: Int, out: Level): Boolean = {
        val exactOrRhs = out.terms.exists {
          case (`atom`, outOffset) => offset <= outOffset
          case (IMaxAtom(_, rhs), outOffset) =>
            loop(termAsLevel(atom, offset), addOffset(rhs, outOffset))
          case _ => false
        }
        exactOrRhs || (atom match {
          case IMaxAtom(lhs, rhs) =>
            constantCovered(offset, out) &&
            loop(addOffset(lhs, offset), out) &&
            loop(addOffset(rhs, offset), out)
          case _: ParamAtom => false
        })
      }

      def loop(lhs: Level, rhs: Level): Boolean =
        if (lhs == rhs) true
        else
          memo.getOrElseUpdate(
            (lhs, rhs),
            if (!containsIMax(lhs) && !containsIMax(rhs)) regularLeq(lhs, rhs)
            else
              constantCovered(lhs.c, rhs) && lhs.terms.forall { case (atom, offset) =>
                termLeq(atom, offset, rhs)
              }
          )

      loop(l1, l2)
    }

    def mk(varId: VarId): Level = ofTerms(Map(ParamAtom(varId) -> 0), 0)

    /** The level a value denotes: a Level directly, or a Level-typed variable as its atom. */
    def fromValue(v: Value): Option[Level] =
      v match {
        case l: Level             => Some(l)
        case Var(_, id, LevelTpe) => Some(mk(id))
        case _                    => None
      }

    val zero = const(0)
    val one = const(1)

  }

  case class VSort(level: Level) extends Value {
    override def tpe: Value = VSort(Level.succ(level))

    override lazy val synDeps: DepSet = level.synDeps
  }

  final val PropTpe: VSort = VSort(Level.zero)
  final val TypeTpe: VSort = VSort(Level.one)

  // The classifier is a thunk, not a stored sort: a Pi's universe depends on the env it is
  // evaluated in (level-polymorphic binder types), so residuals carry no classifier and each VPi
  // instance derives its own from its binders and codomain (Interpreter.piClassifier).
  // Binders are the residual's own ElabAst.Binder nodes: a VPi is its syntax plus a closure.
  case class VPi(
      env: Env,
      binders: Vector[ElabAst.Binder],
      codomain: Env => Value,
      synDeps: DepSet,
      id: ValueId,
      classifier0: () => VSort
  ) extends Value
    with UpdatableType {
    require(binders.nonEmpty, "VPi requires at least one binder")

    override lazy val tpe: VSort = classifier0()

    /**
     * Whether this Pi is itself a proposition — by impredicativity, exactly when its codomain is Prop-valued, which is
     * also exactly when the classifier is Prop. Kept separate from `tpe` so the proof-collapse checks that run on every
     * lambda creation and env binding need only a codomain evaluation, not the per-binder universe walk of the full
     * classifier.
     */
    lazy val isPropValued: Boolean = {
      val freshEnv = telescope.BinderOps.freshen(binders, env)
      Value.isPropositionType(codomain(freshEnv))
    }

    override def toString: String = "VPi"

    override def withTpe(tpe: Value): Value = tpe match {
      case u: VSort => this.copy(classifier0 = () => u)
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
      env: Env,
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
        case ValueId.Const(_)           =>
        case ValueId.LocalId(_, params) => params.foreach(v => res.unionInPlace(v.synDeps))
      }
      res.result()
    }

    override def withTpe(nextTpe: Value): Value = nextTpe match {
      case pi: VPi if pi.binders.map(_.localRef) == tpe.binders.map(_.localRef) => this.copy(tpe = pi)
      case _: VPi                                                               => this
      case _ => throw WTF(s"Cannot update lambda type to $nextTpe")
    }

  }

  /**
   * The erased value form for proofs whose exact proposition reconstructs neither a constructor nor a Pi eta-lambda.
   * DefEq still compares every pair of proof values solely through their propositions. There is deliberately no stored
   * witness: quotation is canonical as the residual-only `proof(tpe)` intrinsic.
   *
   * A `VProof` is never a `Blocker`: matches on proofs do not block-and-resume. Proofs of Pi propositions instead use
   * the canonical `VLam(_, _, ProofEta)` representation.
   */
  final case class VProof(tpe: Value) extends Value with UpdatableType {
    require(isPropositionType(tpe), s"VProof requires a proposition, got a value of $tpe")

    override lazy val synDeps: DepSet = tpe.synDeps

    // Ascription may retype at a defEq type that is not *known* to be a proposition (e.g. a
    // generic-universe binder type mid-elaboration); the proof keeps its proposition then,
    // mirroring VLam.withTpe's leniency on mismatched binders.
    override def withTpe(tpe: Value): Value =
      if (isPropositionType(tpe)) copy(tpe = tpe) else this
  }

  /**
   * A packed representation codec (K3, docs/native-literals.md §3): one type's compact host-side representation for
   * ground data. The set is closed and kernel-curated by design — each codec is trusted code inside defeq. Laws L1–L9
   * of the spec govern every instance.
   */
  sealed abstract class PackedCodec {

    /** L5: every ground value of the type is packed; no ground constructor-headed value exists. */
    def canonical: Boolean

    /** One constructor layer of the payload: canonical constructor name plus stored arguments. */
    def decodeHead(v: VPacked): (String, Vector[Value])

    /** Strict order realized by constructor-field steps on decodings; well-founded (L6). */
    def strictlyLess(candidate: VPacked, root: VPacked): Boolean

    /** L9: unequal payloads decode to a derivable constructor clash at finite depth. */
    def refutesUnequalPayloads: Boolean
  }

  /** Nat as arbitrary-precision integers (docs/native-literals.md §4). */
  case object NatCodec extends PackedCodec {
    val familyName = "Nat"
    val zeroName = "Nat.zero"
    val succName = "Nat.succ"

    override def canonical: Boolean = true

    override def decodeHead(v: VPacked): (String, Vector[Value]) =
      if (v.payload == 0) (zeroName, Vector.empty)
      else (succName, Vector(VPacked(NatCodec, v.payload - 1, v.tpe)))

    override def strictlyLess(candidate: VPacked, root: VPacked): Boolean =
      candidate.payload < root.payload

    override def refutesUnequalPayloads: Boolean = true
  }

  /**
   * A packed literal: ground, closed data whose host payload contains no `Value` s. Constructor form is derived on
   * demand, one layer at a time, through the codec.
   *
   * The payload is `BigInt` while Nat is the only codec; it generalizes with the staged CharList codec.
   */
  final case class VPacked(codec: PackedCodec, payload: BigInt, tpe: Value) extends Value with UpdatableType {
    require(payload >= 0, s"Packed payload must be non-negative: $payload")
    require(!isPropositionType(tpe), s"VPacked requires a non-propositional type, got $tpe")

    override lazy val synDeps: DepSet = tpe.synDeps

    override def withTpe(tpe: Value): Value = this.copy(tpe = tpe)
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

  // Pattern binders bind exactly the stored fields: erased family args have no pattern slots,
  // so a VCtor's stored args ARE its pattern args.
  private[raccoonlang] def constructorStoredArgs(head: ConstructorHead, args: Vector[Value]): Vector[Value] = {
    if (args.length != head.totalArity)
      throw WTF(s"Constructor ${head.name} was given ${args.length} args, expected ${head.totalArity}")
    args.drop(head.numErasedFamilyArgs)
  }

  final case class ConstructorMeta(shortName: String, canonicalName: String)

  /**
   * A stored constructor field's declaration-time reconstruction recipe. Data fields name the direct family-result
   * argument that fixes them. Proposition fields are reconstructed shallowly as erased proofs of their instantiated
   * binder types.
   */
  sealed trait ProofFieldRecipe
  object ProofFieldRecipe {
    final case class ResultArgument(index: Int) extends ProofFieldRecipe
    case object ErasedProof extends ProofFieldRecipe
  }

  /**
   * Constructor reconstruction capability carried by an inductive family. The head is a promise resolved only after the
   * checked family and its constructor have been installed in the environment.
   */
  final class ProofConstructorInfo(
      val fields: Vector[ProofFieldRecipe],
      ctorHead0: () => Option[ConstructorHead]
  ) {
    // Family metadata exists while its constructor heads are still being checked. During that
    // interval reconstruction is unavailable; it becomes available once the declaration's final
    // environment has been installed.
    def ctorHead: Option[ConstructorHead] = ctorHead0()
  }

  /** Declaration-time proof representation policy. */
  sealed trait ProofStorage
  object ProofStorage {
    case object Erase extends ProofStorage
    final case class Reconstruct(info: ProofConstructorInfo) extends ProofStorage
  }

  /**
   * Expansion capability of an eta-eligible struct (StructEta): the field names in constructor order plus the
   * constructor head. Carried on the meta — inside the type value itself — so expansion needs no environment (Builtins
   * natives run under empty envs; `Value.ascribe` has none at all). The head is a promise: its type is checked against
   * the installed family head, so it cannot exist yet when the meta is built (InductiveChecks wires it right after
   * install).
   */
  final class StructEtaInfo(val fieldNames: Vector[String], ctorHead0: () => ConstructorHead) {
    lazy val ctorHead: ConstructorHead = ctorHead0()
  }

  final case class InductiveMeta(
      constructors: Vector[ConstructorMeta],
      familyArity: Int,
      isStruct: Boolean,
      positiveArgs: DepSet,
      etaInfo: Option[StructEtaInfo],
      proofStorage: ProofStorage
  ) {
    require(
      positiveArgs.isEmpty || positiveArgs.max < familyArity,
      "Inductive positive argument indexes must be in range"
    )
    require(etaInfo.isEmpty || isStruct, "Only structs can be eta-eligible")
    require(
      !proofStorage.isInstanceOf[ProofStorage.Reconstruct] || constructors.length == 1,
      "Constructor-reconstructing proof families must have exactly one constructor"
    )

    lazy val constructorNames: Vector[String] = constructors.map(_.canonicalName)
  }

  sealed trait ConstType
  case class Inductive(meta: InductiveMeta) extends ConstType
  case object Symbol extends ConstType

  /**
   * Head of a stuck struct projection: `VConst(\"S.field\", StructField(i), _)` applied to its base. Created only by
   * StructEta on neutral bases; `Interpreter.evalApply` reduces it structurally (constructor-headed base → stored
   * field), bypassing Pi dispatch. defEq and keys treat it like any VConst — by name — which is exactly projection
   * congruence.
   */
  case class StructField(index: Int) extends ConstType

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
