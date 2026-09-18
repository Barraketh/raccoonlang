package com.raccoonlang

import com.raccoonlang.telescope.BinderOps

import scala.collection.immutable.BitSet

/**
 * Represents a typechecked value representation - the values that live in an Env. Values can contain Vars(), which
 * represent unknown values. Vars have a unique id, which means they can participate in equality. Thus values could be
 * thought of as a typed, maximally reduced representation of CoreAst. Invariants:
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
   * The value's type is a proposition: it lives in `Prop`. The sort `Prop` itself never qualifies (`Prop : Sort 1`) —
   * predicates are data, not proofs (docs/kernel.md#universes-and-function-types).
   */
  def isPropositionType(tpe: Value): Boolean =
    tpe match {
      case PropTpe => false
      // Impredicativity: a Pi is a proposition exactly when its codomain is Prop-valued. Answered
      // via the dedicated lazy val so proof canonicalization checks skip the full classifier computation.
      case pi: VPi => pi.isPropValued
      case tpe     => tpe.tpe == PropTpe
    }

  private def isKnownProof(value: Value): Boolean = isPropositionType(value.tpe)

  /**
   * Put a proof into the canonical representation determined solely by its exact proposition
   * (docs/kernel.md#proofs-and-elimination). If the proposition's recovery plan reconstructs a constructor at that
   * exact type, every inhabitant uses constructor form. Otherwise a Pi proposition reconstructs its eta-lambda and
   * every other ordinary inhabitant erases to `VProof`. Exemptions:
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
      // result-forced data fields. Check this before running recovery so repeated canonicalization
      // at environment boundaries is constant-time.
      case VCtor(actualHead, _, _) if ProofReconstruction.isDefinitelyCertifiedConstructor(value.tpe, actualHead) =>
        value
      // A universe-polymorphic field may become a proof only at this exact instance, so it cannot
      // use the declaration-wide fast path. Validate recovery once and preserve the already-
      // constructor-headed value when it is the canonical head.
      case VCtor(actualHead, _, _) =>
        ProofReconstruction.reconstruct(value.tpe) match {
          case Some(reconstructed) if reconstructed.head.name == actualHead.name => value
          case Some(reconstructed) => VCtor(reconstructed.head, reconstructed.fields, value.tpe)
          case None                => VProof(value.tpe)
        }
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
   * Recover an erased proof without recursively reconstructing an inductive constructor. Pi proofs still need their
   * canonical operational eta-lambda because later dependent types may apply them.
   */
  private[raccoonlang] def shallowProof(tpe: Value): Value =
    tpe match {
      case pi: VPi => canonicalProofLambda(pi)
      case _       => VProof(tpe)
    }

  /**
   * Canonicalize a freshened *rigid* binder (docs/kernel.md#proofs-and-elimination). Counterpart to canonicalizeProof's
   * `Var` exemption — a bare fresh Var is a refinable meta there and must not collapse, but here the Var is a rigid
   * hypothesis being bound, so its identity is checking metadata rather than runtime proof representation.
   */
  def canonicalizeRigidBinder(tpe: Value, fresh: Value): Value =
    if (isPropositionType(tpe)) canonicalizeProof(VProof(tpe)) else fresh

  /**
   * Whether structure eta may decompose an equation with this value on one side: the value is a constructor at an
   * eta-eligible type, or any value at a *fieldless* eligible type (unit eta). Two neutrals at a struct type with
   * fields are deliberately NOT decomposable: each virtual field is a projection thunk that captures its base, so
   * comparing the fields would compare the bases again — a fieldwise rule for that case adds nothing and diverges.
   */
  private[raccoonlang] def etaDecomposable(value: Value): Boolean =
    value match {
      case _: VProof => false
      case v =>
        StructEta.eligibleInstance(v.tpe).exists { case (_, info) =>
          info.fieldCount == 0 || ConstructorForm.unapply(v).nonEmpty
        }
    }

  private[raccoonlang] def needsStructuralDefEq(value: Value): Boolean =
    isKnownProof(value) || (value match {
      case _: VPi | _: VLam | _: NeutralThunk => true
      // A value that structure eta can decompose compares fieldwise, which no key can decide
      // (StructEta, rule 2).
      case v if etaDecomposable(v) => true
      case app: VApp =>
        app.head.needsStructuralDefEq || app.args.exists(_.needsStructuralDefEq) || app.tpe.needsStructuralDefEq
      case p: VPacked => !p.codec.canonical
      case _          => false
    })

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

  /**
   * The `Var` objects occurring in `value` whose ids lie in `ids`. `synDeps` already answers *which* ids occur; this
   * recovers the variables themselves, which callers need when they have to look at a variable's type (the refinability
   * boundary in `EqStore.allowEta` asks whether each one stands at an eta-eligible struct type).
   *
   * The walk is pruned by `synDeps`: a subvalue that mentions none of `ids` is skipped whole. Each id is reported once
   * — a `Var` is determined by its id, so the first occurrence is as good as any.
   */
  private[raccoonlang] def varsIn(value: Value, ids: DepSet): Vector[Var] = {
    if (ids.isEmpty || !value.synDeps.intersects(ids)) return Vector.empty
    val found = Vector.newBuilder[Var]
    var seen = DepSet.empty

    def walkEnv(env: Env): Unit = env.locals.values.foreach(walk)

    def walk(v: Value): Unit = {
      if (!v.synDeps.intersects(ids)) return
      v match {
        case x: Var =>
          if (ids.contains(x.id) && !seen.contains(x.id)) {
            seen = seen + x.id
            found += x
          }
          walk(x.tpe)
        case VApp(head, args, tpe, _) =>
          walk(head)
          args.foreach(walk)
          walk(tpe)
        case NeutralThunk(_, env, id, tpe, _) =>
          walkEnv(env)
          id.captures.foreach(walk)
          walk(tpe)
        case pi: VPi =>
          walkEnv(pi.env)
        case lam: VLam =>
          walk(lam.tpe)
          lam.body match {
            case LamBody.Core(_, env)      => walkEnv(env)
            case LamBody.Native(_, env, _) => walkEnv(env)
            case LamBody.ProofEta          =>
          }
          lam.id match {
            case ValueId.Const(_)           =>
            case ValueId.LocalId(_, params) => params.foreach(walk)
          }
        // Everything else is either leaf-like or reaches vars only through its type. Sorts are
        // excluded explicitly: `VSort(u).tpe` is `VSort(u+1)`, an infinite ascent with the same deps.
        case _: VSort | LevelTpe | _: Level | _: ConstructorHead =>
        case other                                               => walk(other.tpe)
      }
    }

    walk(value)
    found.result()
  }

  sealed trait LamBody {
    def synDeps: DepSet
  }
  object LamBody {
    final case class Core(term: CoreAst.Term.Lam, env: Env) extends LamBody {
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
  // Binders are the checked CoreAst.Binder nodes themselves: a VPi is its syntax plus a closure.
  case class VPi(
      env: Env,
      binders: Vector[CoreAst.Binder],
      codomain: Env => Value,
      synDeps: DepSet,
      id: ValueId,
      classifier0: () => VSort,
      knownPropValued: Option[Boolean] = None
  ) extends Value {
    require(binders.nonEmpty, "VPi requires at least one binder")

    override lazy val tpe: VSort = classifier0()

    /**
     * Whether this Pi is itself a proposition — by impredicativity, exactly when its codomain is Prop-valued, which is
     * also exactly when the classifier is Prop. Kept separate from `tpe` so the proof canonicalization checks that run
     * on every lambda creation and env binding need only a codomain evaluation, not the per-binder universe walk of the
     * full classifier.
     */
    lazy val isPropValued: Boolean = {
      knownPropValued.getOrElse {
        val freshEnv = telescope.BinderOps.freshen(binders, env)
        Value.isPropositionType(codomain(freshEnv))
      }
    }

    /** How many explicit arguments this Pi's own binder group takes. */
    lazy val numExplicit: Int = binders.count(!_.isImplicit)

    /**
     * Implicit telescope indices grouped by the *explicit* argument position their projection spec roots at. Specs
     * always root at a non-implicit binder, so walking the explicit args in order lands every implicit exactly once.
     *
     * Derived from `binders` alone, so it survives `copy` of any other field.
     */
    lazy val implicitRoots: Map[Int, Vector[Int]] =
      binders.zipWithIndex
        .collect {
          case (binder, idx) if binder.isImplicit =>
            val spec = binder.projection.getOrElse(
              throw WTF(s"Implicit binder ${binder.name} has no projection spec")
            )
            spec.rootArgIdx -> idx
        }
        .groupMap(_._1)(_._2)

    override def toString: String = "VPi"
  }

  case class VConst(name: String, constType: ConstType, tpe: Value) extends Value {
    override lazy val synDeps: DepSet = tpe.synDeps
  }

  case class VApp(head: Value, args: Vector[Value], tpe: Value, blockedOn: DepSet = DepSet.empty) extends Value {
    override lazy val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(head.synDeps)
      args.foreach(v => res.unionInPlace(v.synDeps))
      res.unionInPlace(tpe.synDeps)
      res.result()
    }

    require(args.nonEmpty || blockedOn.isEmpty, "Blocked application requires at least one argument")
    head match {
      case h: ConstructorHead =>
        require(blockedOn.isEmpty, s"Constructor ${h.name} cannot be blocked")
        val expectedArgs = h.totalArity - h.numErasedFamilyArgs
        require(
          args.length == expectedArgs,
          s"Constructor ${h.name} stores ${args.length} args, expected $expectedArgs"
        )
      case _ =>
    }
  }

  case class NeutralThunk(
      term: CoreAst.Term.Match,
      env: Env,
      id: ValueId.LocalId,
      tpe: Value,
      blockedOn: DepSet
  ) extends Value {
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
        case ValueId.Const(_)           =>
        case ValueId.LocalId(_, params) => params.foreach(v => res.unionInPlace(v.synDeps))
      }
      res.result()
    }
  }

  /**
   * The erased value form for proofs whose exact proposition reconstructs neither a constructor nor a Pi eta-lambda.
   * DefEq still compares every pair of proof values solely through their propositions. There is deliberately no stored
   * witness.
   *
   * A `VProof` is never a head `Blocker`. A data-valued match on one can nevertheless be judgment-blocked on the
   * proposition's dependencies. Proofs of Pi propositions use the canonical `VLam(_, _, ProofEta)` representation.
   */
  final case class VProof(tpe: Value) extends Value {
    require(isPropositionType(tpe), s"VProof requires a proposition, got a value of $tpe")

    override lazy val synDeps: DepSet = tpe.synDeps
  }

  /**
   * A packed representation codec (docs/kernel.md#trusted-bootstrap-and-native-values): one type's compact host-side
   * representation for ground data. The set is closed and kernel-curated by design — each codec is trusted code inside
   * defeq.
   */
  sealed abstract class PackedCodec {

    /** Every ground value of the type is packed; no ground constructor-headed value exists. */
    def canonical: Boolean

    /** One constructor layer of the payload: canonical constructor name plus stored arguments. */
    def decodeHead(v: VPacked): (String, Vector[Value])

    /** Strict order realized by constructor-field steps on decodings; well-founded. */
    def strictlyLess(candidate: VPacked, root: VPacked): Boolean

    /** Unequal payloads decode to a derivable constructor clash at finite depth. */
    def refutesUnequalPayloads: Boolean

    /** Whether this codec owns this sealed payload variant. */
    private[raccoonlang] def acceptsPayload(payload: PackedPayload): Boolean

    /** Semantic payload equality. Codec compatibility is checked by the caller. */
    private[raccoonlang] def payloadEquals(left: PackedPayload, right: PackedPayload): Boolean

    /** Mix the complete payload into a trusted value key. */
    private[raccoonlang] def mixPayloadKey(key: ValueKey.Key, payload: PackedPayload): ValueKey.Key
  }

  sealed trait PackedPayload

  final class NatPayload private[Value] (val value: BigInt) extends PackedPayload

  final class CharListPayload private[Value] (private val scalars0: Vector[Int]) extends PackedPayload {
    private[raccoonlang] def scalars: Vector[Int] = scalars0
  }

  private[raccoonlang] object PackedPayload {
    def natValue(payload: PackedPayload): BigInt = payload match {
      case nat: NatPayload    => nat.value
      case _: CharListPayload => throw WTF("Nat codec received a CharList payload")
    }

    def charScalars(payload: PackedPayload): Vector[Int] = payload match {
      case _: NatPayload          => throw WTF("CharList codec received a Nat payload")
      case chars: CharListPayload => chars.scalars
    }
  }

  /** Nat as arbitrary-precision integers (docs/kernel.md#natural-numbers). */
  case object NatCodec extends PackedCodec {
    val familyName = "Nat"
    val zeroName = "Nat.zero"
    val succName = "Nat.succ"

    override def canonical: Boolean = true

    override def decodeHead(v: VPacked): (String, Vector[Value]) = {
      val value = PackedPayload.natValue(v.payload)
      if (value == 0) (zeroName, Vector.empty)
      else (succName, Vector(VPacked.nat(value - 1, v.tpe)))
    }

    override def strictlyLess(candidate: VPacked, root: VPacked): Boolean =
      PackedPayload.natValue(candidate.payload) < PackedPayload.natValue(root.payload)

    override def refutesUnequalPayloads: Boolean = true

    override private[raccoonlang] def acceptsPayload(payload: PackedPayload): Boolean =
      payload match {
        case _: NatPayload      => true
        case _: CharListPayload => false
      }

    override private[raccoonlang] def payloadEquals(left: PackedPayload, right: PackedPayload): Boolean =
      PackedPayload.natValue(left) == PackedPayload.natValue(right)

    override private[raccoonlang] def mixPayloadKey(key: ValueKey.Key, payload: PackedPayload): ValueKey.Key =
      ValueKey.mixBytes(key, PackedPayload.natValue(payload).toByteArray)
  }

  final class CharListCodec private[raccoonlang] (
      val natTpe: Value,
      val charTpe: Value,
      val listCharTpe: Value,
      val charOfNat: Value
  ) extends PackedCodec {
    require(Vector(natTpe, charTpe, listCharTpe, charOfNat).forall(_.synDeps.isEmpty), "String layout must be closed")

    override def canonical: Boolean = false

    override def decodeHead(v: VPacked): (String, Vector[Value]) =
      PackedPayload.charScalars(v.payload) match {
        case head +: _ =>
          val char = Interpreter.evalApply(charOfNat, Vector(VPacked.nat(BigInt(head), natTpe)))
          ("List.cons", Vector(char, VPacked.charListTail(v)))
        case _ => ("List.nil", Vector.empty)
      }

    override def strictlyLess(candidate: VPacked, root: VPacked): Boolean = {
      val left = PackedPayload.charScalars(candidate.payload)
      val right = PackedPayload.charScalars(root.payload)
      left.length < right.length && right.endsWith(left)
    }

    override def refutesUnequalPayloads: Boolean = false

    override private[raccoonlang] def acceptsPayload(payload: PackedPayload): Boolean =
      payload match {
        case _: NatPayload      => false
        case _: CharListPayload => true
      }

    override private[raccoonlang] def payloadEquals(left: PackedPayload, right: PackedPayload): Boolean =
      PackedPayload.charScalars(left) == PackedPayload.charScalars(right)

    override private[raccoonlang] def mixPayloadKey(key: ValueKey.Key, payload: PackedPayload): ValueKey.Key = {
      val scalars = PackedPayload.charScalars(payload)
      var cur = ValueKey.mixKey(key, listCharTpe.key)
      cur = ValueKey.mixLong(cur, scalars.length.toLong)
      scalars.foreach(scalar => cur = ValueKey.mixLong(cur, scalar.toLong & 0xffffffffL))
      cur
    }
  }

  sealed abstract class ValidatedStringLayout private[raccoonlang] {
    def stringTpe: Value
    def charListCodec: CharListCodec
    private[raccoonlang] def eval(scalars: Vector[Int]): Value
  }

  final class SourceStringLayout private[raccoonlang] (
      val stringTpe: Value,
      val stringMk: ConstructorHead,
      val charListCodec: CharListCodec
  ) extends ValidatedStringLayout {
    override private[raccoonlang] def eval(scalars: Vector[Int]): Value =
      Interpreter.evalApply(stringMk, Vector(VPacked.charList(charListCodec, scalars)))
  }

  /** A closed packed literal. Construction is restricted to the validated factories below. */
  final class VPacked private (
      val codec: PackedCodec,
      private[raccoonlang] val payload: PackedPayload,
      val tpe: Value
  ) extends Value {
    require(codec.acceptsPayload(payload), "Packed codec/payload mismatch")
    require(tpe.synDeps.isEmpty, s"VPacked requires a closed type, got dependencies ${tpe.synDeps}")
    require(!isPropositionType(tpe), s"VPacked requires a non-propositional type, got $tpe")

    override lazy val synDeps: DepSet = tpe.synDeps

    private[raccoonlang] def natValue: Option[BigInt] = codec match {
      case NatCodec         => Some(PackedPayload.natValue(payload))
      case _: CharListCodec => None
    }

    private[raccoonlang] def charScalars: Option[Vector[Int]] = codec match {
      case NatCodec         => None
      case _: CharListCodec => Some(PackedPayload.charScalars(payload))
    }
  }

  object VPacked {
    private[raccoonlang] def nat(value: BigInt, tpe: Value): VPacked = {
      require(value >= 0, s"Packed Nat payload must be non-negative: $value")
      require(tpe.synDeps.isEmpty, s"Packed Nat type must be closed, got dependencies ${tpe.synDeps}")
      new VPacked(NatCodec, new NatPayload(value), tpe)
    }

    private[raccoonlang] def charList(codec: CharListCodec, scalars: Vector[Int]): VPacked = {
      require(scalars.forall(UnicodeScalarString.isScalar), "Packed string contains a non-Unicode scalar")
      new VPacked(codec, new CharListPayload(scalars), codec.listCharTpe)
    }

    private[raccoonlang] def charListTail(parent: VPacked): VPacked =
      parent.codec match {
        case codec: CharListCodec =>
          val scalars = PackedPayload.charScalars(parent.payload)
          if (scalars.nonEmpty) new VPacked(codec, new CharListPayload(scalars.tail), codec.listCharTpe)
          else throw WTF("Cannot decode the tail of an empty packed CharList")
        case NatCodec => throw WTF("CharList tail requested from a packed Nat")
      }

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
  ) extends TopLevelValue {
    require(numErasedFamilyArgs >= 0, "Constructor erased family argument count must be non-negative")
    require(numErasedFamilyArgs <= totalArity, "Constructor erased family argument count cannot exceed total arity")

    /** The constructor's telescope, when it has one. A nullary constructor's type is its result type directly. */
    lazy val pi: Option[VPi] = tpe match {
      case pi: VPi => Some(pi)
      case _       => None
    }

    /**
     * The telescope split `numErasedFamilyArgs` induces: the leading binders instantiated from a family instance's
     * arguments, then the binders that become the constructor's stored fields. Both are empty when the type is not a
     * Pi, which is exactly the nullary case.
     */
    lazy val paramBinders: Vector[CoreAst.Binder] =
      pi.fold(Vector.empty[CoreAst.Binder])(_.binders.take(numErasedFamilyArgs))

    lazy val fieldBinders: Vector[CoreAst.Binder] =
      pi.fold(Vector.empty[CoreAst.Binder])(_.binders.drop(numErasedFamilyArgs))

    /**
     * The env in which this constructor's field binder types are evaluable: the Pi's own closure extended with the
     * parameter binders bound to `familyArgs`. Callers pass the family instance's arguments; only the leading
     * `paramBinders.length` of them are consumed, since trailing indices are not parameters.
     */
    def fieldEnv(familyArgs: Vector[Value]): Env = {
      val piEnv = pi.map(_.env).getOrElse(Env.empty)
      if (familyArgs.length < paramBinders.length)
        throw WTF(
          s"Constructor $name needs ${paramBinders.length} family parameters, got ${familyArgs.length}"
        )
      BinderOps.instantiateFull(paramBinders, piEnv, familyArgs.take(paramBinders.length))
    }
  }

  // Pattern binders bind exactly the stored fields: erased family args have no pattern slots,
  // so a VCtor's stored args ARE its pattern args.
  private[raccoonlang] def constructorStoredArgs(head: ConstructorHead, args: Vector[Value]): Vector[Value] = {
    if (args.length != head.totalArity)
      throw WTF(s"Constructor ${head.name} was given ${args.length} args, expected ${head.totalArity}")
    args.drop(head.numErasedFamilyArgs)
  }

  final case class ConstructorMeta(shortName: String, canonicalName: String)

  /** A stored data field's declaration-time source in the family result. */
  sealed trait ProofFieldSource
  object ProofFieldSource {
    final case class ResultArgument(index: Int) extends ProofFieldSource {
      require(index >= 0, "Proof field result-argument index must be non-negative")
    }
    case object Unavailable extends ProofFieldSource
  }

  /**
   * Checked field metadata of a one-constructor inductive family. `fieldDependencies(i)` is the precise transitive set
   * of preceding fields needed to instantiate the type of field `i`, and `etaEligible` records whether structure eta
   * applies. This is metadata read by the eta rules (StructEta); it is not itself an eliminator.
   *
   * Field spellings are deliberately absent: named selectors are ordinary frontend definitions that compile to matches.
   * The constructor head is a promise completed after declaration installation.
   */
  final class ProjectionInfo(
      val ctorName: String,
      val fieldDependencies: Vector[BitSet],
      val etaEligible: Boolean,
      ctorHead0: () => Option[ConstructorHead]
  ) {
    val fieldCount: Int = fieldDependencies.length
    fieldDependencies.zipWithIndex.foreach { case (dependencies, fieldIndex) =>
      require(dependencies.forall(_ < fieldIndex), "Projection fields may depend only on preceding fields")
    }

    /**
     * The canonical projection program for each field of this family, allocated once with the metadata. Each field
     * index gets its own synthetic span, so its `nodeId` is stable across every projection of that field and distinct
     * from every other field's — which is exactly what makes two projections of defEq bases compare equal by id.
     *
     * The terms depend only on the constructor's name and the field count, both fixed when the family is checked, so
     * they need neither the installed head nor a cache keyed on this object's identity.
     */
    lazy val projectors: Vector[StructEta.Projector] =
      Vector.tabulate(fieldCount)(idx => StructEta.buildProjector(ctorName, fieldCount, idx))
    def ctorHeadOption: Option[ConstructorHead] = ctorHead0()
    lazy val ctorHead: ConstructorHead = {
      val head = ctorHeadOption.getOrElse(throw WTF("Projection constructor requested before declaration installation"))
      if (head.name != ctorName)
        throw WTF(s"Projection metadata for $ctorName was completed with constructor ${head.name}")
      val actualFieldCount = head.totalArity - head.numErasedFamilyArgs
      if (actualFieldCount != fieldCount)
        throw WTF(s"Projection metadata for ${head.name} has $fieldCount fields, constructor has $actualFieldCount")
      head
    }
  }

  /**
   * Declaration-compiled plan for recovering fields from a Prop instance without consulting its proof value. Field
   * propness is deliberately classified at the actual instance; the stored sources describe only data recovery.
   */
  final class ProofRecoveryInfo(
      val fieldSources: Vector[ProofFieldSource],
      val projectionInfo: ProjectionInfo,
      val definitelyComplete: Boolean
  ) {
    require(fieldSources.length == projectionInfo.fieldCount, "Proof recovery and projection field counts must agree")
  }

  final case class InductiveBlockKey(members: Vector[String], numParams: Int) {
    require(members.nonEmpty, "An inductive block must contain at least one family")
    require(members.distinct.length == members.length, "Inductive block family names must be unique")
    require(numParams >= 0, "Inductive block parameter count must be non-negative")
  }

  sealed trait InductiveBlockDescriptor {
    def key: InductiveBlockKey
    def positiveParams: DepSet

    protected final def validatePositiveParams(): Unit =
      require(
        positiveParams.isEmpty || positiveParams.max < key.numParams,
        "Inductive positive source-parameter indexes must be in range"
      )

    final def isPositiveCoreArgument(index: Int): Boolean = positiveParams.contains(index)
  }

  final case class ProvisionalInductiveBlockInfo(
      key: InductiveBlockKey,
      positiveParams: DepSet
  ) extends InductiveBlockDescriptor {
    validatePositiveParams()
  }

  /**
   * The checked identity of an inductive block: its key and the source parameters the block-wide positivity fixed point
   * admitted. The native positivity walker nests through a previously declared family by reading these.
   */
  final case class CheckedInductiveBlockSchema(
      key: InductiveBlockKey,
      positiveParams: DepSet
  ) extends InductiveBlockDescriptor {
    validatePositiveParams()
  }

  final case class InductiveMeta(
      constructors: Vector[ConstructorMeta],
      familyArity: Int,
      block: InductiveBlockDescriptor,
      projectionInfo: Option[ProjectionInfo],
      proofRecovery: Option[ProofRecoveryInfo]
  ) {
    require(familyArity >= block.key.numParams, "Inductive family arity must contain the common parameter prefix")
    require(projectionInfo.isEmpty || constructors.length == 1, "Only one-constructor families can be projected")
    require(proofRecovery.isEmpty || constructors.length == 1, "Only one-constructor families can recover proof fields")
    require(
      proofRecovery.forall(info => projectionInfo.contains(info.projectionInfo)),
      "Proof recovery must share its family's projection metadata"
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
    def apply(head: Value, args: Vector[Value], tpe: Value, blockedOn: DepSet): VApp = {
      require(blockedOn.nonEmpty, "Blocked application requires at least one blocker")
      VApp(head, args, tpe, blockedOn)
    }

    def unapply(value: Value): Option[(Value, Vector[Value], Value, DepSet)] =
      value match {
        case VApp(head, args, tpe, blockedOn) if blockedOn.nonEmpty => Some((head, args, tpe, blockedOn))
        case _                                                      => None
      }
  }

  object VCtor {
    def apply(head: ConstructorHead, fields: Vector[Value], tpe: Value): VApp = VApp(head, fields, tpe)

    def unapply(value: Value): Option[(ConstructorHead, Vector[Value], Value)] =
      value match {
        case VApp(head: ConstructorHead, fields, tpe, blockedOn) if blockedOn.isEmpty =>
          Some((head, fields, tpe))
        case _ => None
      }
  }

  /**
   * One constructor layer of a value that is already in constructor form: the canonical constructor name and the
   * arguments it stores. A `VCtor` answers with its head name and stored fields; a `VPacked` answers with its codec's
   * decoding of one layer (`decodeHead`). Nothing else is in constructor form.
   *
   * The two representations are interchangeable exactly here — every consumer that dispatches on "which constructor is
   * this, and what did it store" (match evaluation and checking, positional projection, constructor-field projection
   * steps, structural-subterm descent) needs the name and the args and nothing more. Consumers that need the
   * `ConstructorHead` object itself (arity, no-confusion, its telescope) must keep matching `VCtor` directly.
   */
  object ConstructorForm {
    def unapply(value: Value): Option[(String, Vector[Value])] =
      value match {
        case VCtor(head, storedArgs, _) => Some((head.name, storedArgs))
        case p: VPacked                 => Some(p.codec.decodeHead(p))
        case _                          => None
      }
  }

  object Blocker {
    def unapply(value: Value): Option[DepSet] =
      value match {
        case Var(_, id, _)                                             => Some(DepSet(id))
        case VBlockedApp(_, _, _, blockedOn)                           => Some(blockedOn)
        case NeutralThunk(_, _, _, _, blockedOn) if blockedOn.nonEmpty => Some(blockedOn)
        case _                                                         => None
      }
  }

  object Blocked {
    def unapply(value: Value): Option[DepSet] =
      value match {
        case VBlockedApp(_, _, _, blockedOn)                           => Some(blockedOn)
        case NeutralThunk(_, _, _, _, blockedOn) if blockedOn.nonEmpty => Some(blockedOn)
        case _                                                         => None
      }
  }

  object ConstSpine {
    def unapply(value: Value): Option[(VConst, Vector[Value])] =
      value match {
        case c: VConst                                                   => Some((c, Vector.empty))
        case VApp(head: VConst, args, _, blockedOn) if blockedOn.isEmpty => Some((head, args))
        case _                                                           => None
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
