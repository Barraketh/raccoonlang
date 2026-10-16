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
 *   - key - a structural hash key of this value, computed from its already-built children. Used by defEq
 *   - needsStructuralDefEq: tracks values whose key may differ even when structural equality can still succeed
 */
sealed trait Value {
  def tpe: Value
  def synDeps: DepSet
  def key: ValueKey.Key
  def needsStructuralDefEq: Boolean

  override def toString: String = PrettyPrinter.print(this)
}

sealed trait TopLevelValue extends Value {
  override val synDeps: DepSet = DepSet.empty
}

object Value {

  private def isKnownProof(value: Value): Boolean = Sorts.isProposition(value.tpe)

  /**
   * Put a proof into the canonical representation determined by its exact proposition
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
      // A Pi's own type is a classifier, never a proposition — skip without forcing it.
      // Metas remain linkable, constructor heads remain applicable, and the raw recursive lambda
      // remains executable until checking has validated every recursive call.
      case _: VPi | _: Var | _: ConstructorHead   => value
      case VLam(_, _, LamBody.Native(_, _, true)) => value
      case _ if !Sorts.isProposition(value.tpe)   => value
      // A constructor application already in canonical form keeps it.
      case VCtor(head, _, _) if ProofReconstruction.isCanonicalConstructor(value.tpe, head) => value
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

  /**
   * The unique operational shape reconstructed for every proof of a Pi proposition. It is fabricated here, with no node
   * behind it, so it takes a fresh identity.
   */
  private def canonicalProofLambda(pi: VPi): VLam =
    VLam(pi, ValueId.LocalId(NodeId.fresh(), Vector.empty), LamBody.ProofEta)

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
    if (Sorts.isProposition(tpe)) canonicalizeProof(VProof(tpe)) else fresh

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
    value match {
      // Tested before proofhood, which would force a function type's classifier.
      case _: VPi | _: VLam | _: NeutralThunk => true
      // Sorts and level parameters sit at the top of an infinite classifier ascent. Their metadata is
      // known without following that ascent.
      case _: VSort | _: Level | LevelClassifier | Large | LevelTpe => false
      case _: VProof                                                => true
      case _ if isKnownProof(value)                                 => true
      // A value that structure eta can decompose compares fieldwise, which no key can decide
      // (StructEta, rule 2).
      case v if etaDecomposable(v) => true
      case app: VApp =>
        app.head.needsStructuralDefEq || app.args.exists(_.needsStructuralDefEq) || app.tpe.needsStructuralDefEq
      case _ => false
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
    env.locals.values.foreach(value => res.unionInPlace(value.synDeps))
    res.result()
  }

  /**
   * The `Var` objects occurring in `value` whose ids lie in `ids`. `synDeps` already answers *which* ids occur; this
   * recovers the variables themselves, which callers need when they have to look at a variable's type (the refinability
   * boundary in `EqStore.allowEta` asks whether each one stands at an eta-eligible struct type).
   *
   * The walk is pruned by `synDeps` and visits each value and environment identity once. It keeps the recursive walk's
   * first-match order without expanding shared closure graphs repeatedly. Each id is reported once — a `Var` is
   * determined by its id, so the first occurrence is as good as any.
   */
  private[raccoonlang] def varsIn(value: Value, ids: DepSet): Vector[Var] = {
    if (ids.isEmpty || !value.synDeps.intersects(ids)) return Vector.empty
    val found = Vector.newBuilder[Var]
    val walkedValues = new java.util.IdentityHashMap[Value, java.lang.Boolean]()
    val walkedEnvs = new java.util.IdentityHashMap[Env, java.lang.Boolean]()
    var seen = DepSet.empty
    val pending = scala.collection.mutable.ArrayDeque.empty[Either[Value, Env]]
    pending.append(Left(value))

    def pushValues(values: Iterable[Value]): Unit = {
      val buffer = values.iterator.toVector
      var idx = buffer.length - 1
      while (idx >= 0) {
        pending.append(Left(buffer(idx)))
        idx -= 1
      }
    }

    def pushEnv(env: Env): Unit = pending.append(Right(env))

    while (pending.nonEmpty) {
      pending.removeLast() match {
        case Right(env) =>
          if (walkedEnvs.put(env, java.lang.Boolean.TRUE) == null)
            pushValues(env.locals.values)
        case Left(v) if walkedValues.put(v, java.lang.Boolean.TRUE) == null && v.synDeps.intersects(ids) =>
          v match {
            case x: Var =>
              if (ids.contains(x.id) && !seen.contains(x.id)) {
                seen = seen + x.id
                found += x
              }
              pushValues(Vector(x.tpe))
            case VApp(head, args, tpe, _) =>
              pushValues(head +: (args :+ tpe))
            case NeutralThunk(_, env, id, tpe, _) =>
              pushValues(id.captures :+ tpe)
              pushEnv(env)
            case pi: VPi =>
              pushEnv(pi.env)
            case lam: VLam =>
              val captures = lam.id match {
                case ValueId.Const(_)           => Vector.empty
                case ValueId.LocalId(_, params) => params
              }
              pushValues(captures)
              lam.body match {
                case LamBody.Core(_, env)      => pushEnv(env)
                case LamBody.Native(_, env, _) => pushEnv(env)
                case LamBody.ProofEta          =>
              }
              pushValues(Vector(lam.tpe))
            // Everything else is either leaf-like or reaches vars only through its type. Sorts are
            // excluded explicitly: their types ascend forever with the same level dependencies.
            case _: VSort | Large | LevelClassifier | LevelTpe | _: Level | _: ConstructorHead =>
            case other =>
              pushValues(Vector(other.tpe))
          }
        case Left(_) =>
      }
    }
    found.result()
  }

  sealed trait LamBody {
    def synDeps: DepSet
  }
  object LamBody {
    final case class Core(term: CoreAst.Term.Lam, env: Env) extends LamBody {
      override val synDeps: DepSet = envDeps(env)
    }
    final case class Native(run: (Vector[Value], Env) => Value, env: Env, isRawRecursive: Boolean) extends LamBody {
      override val synDeps: DepSet = envDeps(env)
    }

    /** Type-directed eta expansion of a proof of Pi; its result is reconstructed from the instantiated codomain. */
    case object ProofEta extends LamBody {
      override val synDeps: DepSet = DepSet.empty
    }
  }

  case object LevelTpe extends TopLevelValue {
    override def tpe: Value = LevelClassifier
    override val key: ValueKey.Key = ValueKey.levelTpe
    override val needsStructuralDefEq: Boolean = false
  }

  /** The internal classifier of Level. It is not a sort and no program can write it. */
  case object LevelClassifier extends TopLevelValue {
    override def tpe: Value = LevelClassifier
    override val key: ValueKey.Key = ValueKey.levelClassifier
    override val needsStructuralDefEq: Boolean = false
  }

  /**
   * A type's classifier: a sort, or `Large`. Matches on a classifier are exhaustive and have no wildcard arm, so no
   * code reads a function type's classifier as a sort without deciding what a large one means there.
   */
  sealed trait Classifier extends Value

  /**
   * The classifier of a function type that binds a level. It is internal: no program writes it or binds a variable of
   * it, and it is not a sort, so a large type fits no position that requires a type. Only a declaration's own type is
   * large, so it is used only applied. `Large` classifies itself; nothing quantifies over it, so no hierarchy above it
   * is needed.
   */
  case object Large extends TopLevelValue with Classifier {
    override def tpe: Value = Large
    override val key: ValueKey.Key = ValueKey.large
    override val needsStructuralDefEq: Boolean = false
  }

  // Represents max(u1 + k1, u2 + k2... , c), where each ui is a level variable id.
  // Invariant: all offsets are non-negative, c is non-negative, and c is either 0 or c > k1...kn.
  final class Level private (val terms: Map[VarId, Int], val c: Int) extends Value {
    override val tpe: Value = LevelTpe
    override val key: ValueKey.Key = ValueKey.level(this)
    override val needsStructuralDefEq: Boolean = false

    private val cachedHashCode: Int = 31 * terms.hashCode() + c

    override val synDeps: DepSet = {
      val deps = DepSet.newBuilder
      terms.keysIterator.foreach(deps.add)
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
    def of(terms: Map[VarId, Int], c: Int): Level = {
      require(c >= 0, s"Level constant must be non-negative: $c")
      require(terms.values.forall(_ >= 0), s"Level variable offsets must be non-negative: $terms")

      val nextC =
        if (terms.nonEmpty && c <= terms.values.max) 0
        else c
      new Level(terms, nextC)
    }

    def const(c: Int): Level = of(Map.empty, c)

    def addOffset(l: Level, offset: Int): Level = {
      if (offset == 0) l
      else {
        val newTerms = l.terms.map { case (id, k) => id -> (k + offset) }
        val newC = if (l.c > 0 || l.terms.isEmpty) l.c + offset else 0
        of(newTerms, newC)
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

      val nextTerms = scala.collection.mutable.HashMap.empty[VarId, Int]
      var cMax = 0
      xs.foreach { level =>
        cMax = math.max(cMax, level.c)
        level.terms.foreach { case (id, offset) =>
          nextTerms.get(id) match {
            case Some(current) if offset > current => nextTerms.update(id, offset)
            case None                              => nextTerms.update(id, offset)
            case _                                 =>
          }
        }
      }
      of(nextTerms.toMap, cMax)
    }

    /** The exact invertible shape accepted by level unification and forced-implicit projection. */
    def singleVariableOffset(l: Level): Option[(VarId, Int)] =
      if (l.c != 0 || l.terms.size != 1) None
      else
        l.terms.headOption

    /** A sound, intentionally incomplete pointwise level bound used for inductive size checks. */
    def leq(l1: Level, l2: Level): Boolean =
      (l1.c <= l2.c || l2.terms.values.exists(_ >= l1.c)) &&
        l1.terms.forall { case (id, k) => k <= l2.terms.getOrElse(id, -1) }

    def mk(varId: VarId): Level = of(Map(varId -> 0), 0)

    val zero = const(0)
    val one = const(1)

  }

  /**
   * A sort, built only by `Sorts`, with an explicit proposition tag. There is no extractor and no structural equality:
   * two sorts are compared only by conversion, so `==` on a sort is a kernel bug and throws rather than silently
   * answering false.
   */
  final class VSort private[raccoonlang] (val isProp: Boolean, val level: Level) extends Classifier {
    require(!isProp || level == Level.zero, s"Prop sort must have level zero, got $level")

    override val key: ValueKey.Key = ValueKey.sort(isProp, level)
    override val needsStructuralDefEq: Boolean = false

    override lazy val tpe: Value =
      if (isProp) Sorts.Type else Sorts.sort(Level.succ(level))

    override val synDeps: DepSet = level.synDeps

    override def equals(obj: Any): Boolean = wtf(s"Sort $this compared structurally; compare sorts by conversion")
    override def hashCode(): Int = wtf(s"Sort $this hashed structurally; sorts are never collection keys")
  }

  // The classifier is a thunk rather than a stored sort: a Pi's universe depends on the env it is
  // evaluated in (level-polymorphic binder types), so residuals carry no classifier and each VPi
  // instance derives its own from its binders and codomain (Interpreter.piClassifier). A Pi that
  // binds a level is `Large`.
  // Binders are the checked CoreAst.Binder nodes themselves: a VPi is its syntax plus a closure.

  case class VPi(
      env: Env,
      binders: Vector[CoreAst.Binder],
      codomain: Env => Value,
      override val synDeps: DepSet,
      id: ValueId,
      classifier0: () => Classifier,
      isPropValued: Boolean
  ) extends Value {
    require(binders.nonEmpty, "VPi requires at least one binder")

    override val key: ValueKey.Key = ValueKey.pi(id, binders.length)
    override val needsStructuralDefEq: Boolean = true

    override lazy val tpe: Classifier = classifier0()

    override def equals(obj: Any): Boolean = wtf(s"Function type $this compared structurally; compare by conversion")
    override def hashCode(): Int = wtf(s"Function type $this hashed structurally; it is never a collection key")

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
              wtf(s"Implicit binder ${binder.name} has no projection spec")
            )
            spec.rootArgIdx -> idx
        }
        .groupMap(_._1)(_._2)
  }

  case class VConst(name: String, constType: ConstType, tpe: Value) extends Value {
    override val synDeps: DepSet = tpe.synDeps
    override val key: ValueKey.Key = ValueKey.constant(name)
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)
  }

  case class VApp(head: Value, args: Vector[Value], tpe: Value, blockedOn: DepSet = DepSet.empty) extends Value {
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

    override val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(head.synDeps)
      args.foreach(v => res.unionInPlace(v.synDeps))
      res.unionInPlace(tpe.synDeps)
      res.result()
    }
    override val key: ValueKey.Key = ValueKey.application(head, args, tpe)
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)
  }

  case class NeutralThunk(
      term: CoreAst.Term.Match,
      env: Env,
      id: ValueId.LocalId,
      tpe: Value,
      blockedOn: DepSet
  ) extends Value {
    override val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(envDeps(env))
      res.unionInPlace(tpe.synDeps)
      id.captures.foreach(v => res.unionInPlace(v.synDeps))
      res.result()
    }
    override val key: ValueKey.Key = ValueKey.neutralThunk(id)
    override val needsStructuralDefEq: Boolean = true
  }

  case class Var(name: String, id: VarId, tpe: Value) extends Value {
    override val synDeps: DepSet = tpe.synDeps + id
    override val key: ValueKey.Key = ValueKey.variable(id)
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)
  }

  case class VLam(
      tpe: VPi,
      id: ValueId,
      body: LamBody
  ) extends Value {
    override val synDeps: DepSet = {
      val res = DepSet.newBuilder
      res.unionInPlace(tpe.synDeps)
      res.unionInPlace(body.synDeps)
      id match {
        case ValueId.Const(_)           =>
        case ValueId.LocalId(_, params) => params.foreach(v => res.unionInPlace(v.synDeps))
      }
      res.result()
    }
    override val key: ValueKey.Key = ValueKey.lambda(id)
    override val needsStructuralDefEq: Boolean = true
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
    require(Sorts.isProposition(tpe), s"VProof requires a proposition, got a value of $tpe")

    override val synDeps: DepSet = tpe.synDeps
    override val key: ValueKey.Key = ValueKey.proof(tpe)
    override val needsStructuralDefEq: Boolean = true
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
    override val key: ValueKey.Key = ValueKey.constructorHead(this)
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)
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
        wtf(s"Constructor $name needs ${paramBinders.length} family parameters, got ${familyArgs.length}")
      BinderOps.instantiateFull(paramBinders, piEnv, familyArgs.take(paramBinders.length))
    }
  }

  // Pattern binders bind exactly the stored fields: erased family args have no pattern slots,
  // so a VCtor's stored args ARE its pattern args.
  private[raccoonlang] def constructorStoredArgs(head: ConstructorHead, args: Vector[Value]): Vector[Value] = {
    if (args.length != head.totalArity)
      wtf(s"Constructor ${head.name} was given ${args.length} args, expected ${head.totalArity}")
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
     * index gets a match node of its own, so its identity is stable across every projection of that field and distinct
     * from every other field's — which is exactly what makes two projections of defEq bases compare equal by id.
     *
     * The terms depend only on the constructor's name and the field count, both fixed when the family is checked, so
     * they need neither the installed head nor a cache keyed on this object's identity.
     */
    lazy val projectors: Vector[StructEta.Projector] =
      Vector.tabulate(fieldCount)(idx => StructEta.buildProjector(ctorName, fieldCount, idx))
    def ctorHeadOption: Option[ConstructorHead] = ctorHead0()
    lazy val ctorHead: ConstructorHead = {
      val head = ctorHeadOption.getOrElse(wtf("Projection constructor requested before declaration installation"))
      if (head.name != ctorName)
        wtf(s"Projection metadata for $ctorName was completed with constructor ${head.name}")
      val actualFieldCount = head.totalArity - head.numErasedFamilyArgs
      if (actualFieldCount != fieldCount)
        wtf(s"Projection metadata for ${head.name} has $fieldCount fields, constructor has $actualFieldCount")
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
   * admitted. The positivity walker nests through a previously declared family by reading these.
   */
  final case class CheckedInductiveBlockSchema(
      key: InductiveBlockKey,
      positiveParams: DepSet
  ) extends InductiveBlockDescriptor {
    validatePositiveParams()
  }

  /** A family's checked constructors, positivity, projection and proof metadata. */
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

  /** The head name and stored fields of an ordinary constructor application. */
  object ConstructorForm {
    def unapply(value: Value): Option[(String, Vector[Value])] =
      value match {
        case VCtor(head, storedArgs, _) => Some((head.name, storedArgs))
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
