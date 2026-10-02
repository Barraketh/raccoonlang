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
 *   - key - a structural hash key of this value (ValueKey). Used by defEq
 *   - needsStructuralDefEq: tracks values whose key may differ even when structural equality can still succeed
 *
 * The three are computed when a value is built, from its own components and its children's, which were computed when
 * they were built (docs/kernel.md#value-identity), so none of them walks a value, however deep. An application's three
 * leave out its evidence arguments, which its head and other arguments determine (`VApp.determiningArgs`).
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

/** A kernel singleton: equal only to itself, it has no dependencies and needs no structural comparison. */
sealed trait KernelSingleton extends TopLevelValue {
  override val needsStructuralDefEq: Boolean = false
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
   *   - `DeferredEvidence`: it is the canonical proof of its proposition once forced, and binding it must not force it.
   */
  def canonicalizeProof(value: Value): Value =
    value match {
      case _: DeferredEvidence => value
      // A Pi's own type is a classifier, never a proposition — skip without forcing it.
      // Metas remain linkable, constructor heads remain applicable, and the raw recursive lambda
      // remains executable until checking has validated every recursive call.
      case _: VPi | _: Var | _: ConstructorHead      => value
      case VLam(_, _, LamBody.Native(_, _, true, _)) => value
      case _ if !Sorts.isProposition(value.tpe)      => value
      // A constructor application already in canonical form keeps it.
      case ConstructorApp(head) if ProofReconstruction.isCanonicalConstructor(value.tpe, head) => value
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
   * eta-eligible type, or any value at an eligible type whose fields are all evidence (unit eta: conversion compares no
   * evidence field, so every value there is its constructor applied to nothing it compares). Two neutrals at a struct
   * type with other fields are deliberately NOT decomposable: each virtual field is a projection thunk that captures
   * its base, so comparing the fields would compare the bases again — a fieldwise rule for that case adds nothing and
   * diverges.
   */
  private[raccoonlang] def etaDecomposable(value: Value): Boolean =
    value match {
      case _: VProof => false
      case v =>
        StructEta.eligibleInstance(v.tpe).exists { case (_, info) =>
          info.fieldCount == 0 || isConstructorForm(v) || info.ctorHead.fieldBinders.forall(
            _.mode == BinderMode.Evidence
          )
        }
    }

  /** Whether `ConstructorForm` answers for a value, decided without reading its fields or decoding a packed one. */
  private def isConstructorForm(value: Value): Boolean =
    value match {
      case ConstructorApp(_) | _: VPacked => true
      case _                              => false
    }

  /**
   * Whether a key mismatch leaves an equation with this value open. Each value computes it when it is built: from its
   * own form and type, and for an application from its head's, its determining arguments' and its type's flags, which
   * were computed when they were built.
   */
  private[raccoonlang] def needsStructuralDefEq(value: Value): Boolean =
    value match {
      // Tested before proofhood, which would force a function type's classifier.
      case _: VPi | _: VLam | _: NeutralThunk => true
      // Classified by a sort or a sort parameter, so neither a proof nor a structure: tested before proofhood, which
      // would build a sort's type, a sort that would build its own in turn.
      case _: VSort | _: Level | _: Kind | _: Lifetime | _: KernelSingleton => false
      case _ if isKnownProof(value)                                         => true
      // A value that structure eta can decompose compares fieldwise, which no key can decide
      // (StructEta, rule 2).
      case v if etaDecomposable(v) => true
      case app: VApp =>
        app.head.needsStructuralDefEq || app.determiningArgs.exists(_.needsStructuralDefEq) ||
        app.tpe.needsStructuralDefEq
      case p: VPacked => !p.codec.canonical
      case _          => false
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

  private[raccoonlang] def envDeps(env: Env): DepSet = DepSet.unionAll(env.localValuesIterator.map(_.synDeps))

  /**
   * The `Var` objects occurring in `value` whose ids lie in `ids`. `synDeps` already answers *which* ids occur; this
   * recovers the variables themselves, which callers need when they have to look at a variable's type (the refinability
   * boundary in `EqStore.allowEta` asks whether each one stands at an eta-eligible struct type).
   *
   * The walk is pruned by `synDeps`: a subvalue that mentions none of `ids` is skipped whole. Values and environments
   * are visited once per invocation by object identity, so shared closure/type/environment DAGs are traversed once
   * without relying on structural equality. Each id is reported once — a `Var` is determined by its id, so the first
   * occurrence is as good as any — and an application's evidence arguments are skipped as its `synDeps` skips them: any
   * variable one holds, its head or other arguments hold.
   */
  private[raccoonlang] def varsIn(value: Value, ids: DepSet): Vector[Var] = {
    if (ids.isEmpty || !value.synDeps.intersects(ids)) return Vector.empty
    val found = Vector.newBuilder[Var]
    val walkedValues = new java.util.IdentityHashMap[Value, java.lang.Boolean]()
    val walkedEnvs = new java.util.IdentityHashMap[Env, java.lang.Boolean]()
    var seen = DepSet.empty

    def walkEnv(env: Env): Unit =
      if (walkedEnvs.put(env, java.lang.Boolean.TRUE) == null)
        env.localValuesIterator.foreach(walk)

    def walk(v: Value): Unit = {
      if (walkedValues.put(v, java.lang.Boolean.TRUE) != null || !v.synDeps.intersects(ids)) return
      v match {
        case x: Var =>
          if (ids.contains(x.id) && !seen.contains(x.id)) {
            seen = seen + x.id
            found += x
          }
          walk(x.tpe)
        case app: VApp =>
          walk(app.head)
          app.determiningArgs.foreach(walk)
          walk(app.tpe)
        case NeutralThunk(_, env, id, tpe, _) =>
          walkEnv(env)
          id.captures.foreach(walk)
          walk(tpe)
        case pi: VPi =>
          walkEnv(pi.env)
        case lam: VLam =>
          walk(lam.tpe)
          lam.body match {
            case LamBody.Core(_, env)         => walkEnv(env)
            case LamBody.Native(_, env, _, _) => walkEnv(env)
            case LamBody.ProofEta             =>
          }
          lam.id match {
            case ValueId.Const(_)           =>
            case ValueId.LocalId(_, params) => params.foreach(walk)
          }
        // Everything else is either leaf-like or reaches vars only through its type. Sorts are
        // excluded explicitly: the type of a sort at `u` is the sort at `u+1`, an infinite ascent with the same deps.
        case _: VSort | Large | SortParameter | _: ParameterTpe | _: Level | _: Kind | _: Lifetime |
            _: ConstructorHead =>
        case other => walk(other.tpe)
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
      override val synDeps: DepSet = envDeps(env)
    }
    final case class Native(
        run: (Vector[Value], Env) => Value,
        env: Env,
        isRawRecursive: Boolean,
        scalarCapability: Option[Packed.ScalarNatCapability] = None
    ) extends LamBody {
      override val synDeps: DepSet = envDeps(env)
    }

    /** Type-directed eta expansion of a proof of Pi; its result is reconstructed from the instantiated codomain. */
    case object ProofEta extends LamBody {
      override val synDeps: DepSet = DepSet.empty
    }
  }

  /**
   * A sort parameter: `Level`, `Kind` or `Lifetime` (spec §2.2). None is a type: no sort contains it, so a variable of
   * one is bound only at the binder sites the checker admits, and an expression of one stands only where that parameter
   * is expected.
   */
  sealed trait ParameterTpe extends KernelSingleton {
    final override def tpe: Value = SortParameter
  }

  case object LevelTpe extends ParameterTpe {
    override val key: ValueKey.Key = ValueKey.levelTpe
  }
  case object KindTpe extends ParameterTpe {
    override val key: ValueKey.Key = ValueKey.kindTpe
  }
  case object LifetimeTpe extends ParameterTpe {
    override val key: ValueKey.Key = ValueKey.lifetimeTpe
  }

  /**
   * The classifier of the sort parameters. It is not a sort, so nothing it classifies is a type; it classifies itself,
   * and no program can write it.
   */
  case object SortParameter extends KernelSingleton {
    override def tpe: Value = SortParameter
    override val key: ValueKey.Key = ValueKey.sortParameter
  }

  /**
   * A type's classifier: a sort, or `Large`. Matches on a classifier are exhaustive and have no wildcard arm, so no
   * code reads a function type's classifier as a sort without deciding what a large one means there.
   */
  sealed trait Classifier extends Value

  /**
   * The classifier of a function type that binds a level (spec §2.4). It is internal: no program writes it or binds a
   * variable of it, and it is not a sort, so a large type fits no position that requires a type. Only a declaration's
   * own type is large, so it is used only applied. `Large` classifies itself; nothing quantifies over it, so no
   * hierarchy above it is needed.
   */
  case object Large extends KernelSingleton with Classifier {
    override def tpe: Value = Large
    override val key: ValueKey.Key = ValueKey.large
  }

  // Represents max(u1 + k1, u2 + k2... , c). All offsets and the constant are non-negative,
  // and c is either zero or greater than all offsets; levels are normalized at birth.
  final class Level private (val terms: Map[VarId, Int], val c: Int) extends Value {
    override val tpe: Value = LevelTpe

    // Cache the immutable normal form hash used by level maps.
    private val cachedHashCode: Int = 31 * terms.hashCode() + c

    override val synDeps: DepSet =
      if (terms.isEmpty) DepSet.empty
      else {
        val deps = DepSet.newBuilder
        terms.keys.foreach { id =>
          deps.add(id)
        }
        deps.result()
      }

    override val key: ValueKey.Key = ValueKey.level(terms, c)
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)

    override def equals(obj: Any): Boolean =
      obj match {
        case other: Level => cachedHashCode == other.cachedHashCode && c == other.c && terms == other.terms
        case _            => false
      }

    override def hashCode(): Int = cachedHashCode
  }
  object Level {
    private def ofTerms(terms: Map[VarId, Int], c: Int): Level = {
      require(c >= 0, s"Level constant must be non-negative: $c")
      require(terms.values.forall(_ >= 0), s"Level atom offsets must be non-negative: $terms")

      val nextC =
        if (terms.nonEmpty && c <= terms.values.max) 0
        else c
      new Level(terms, nextC)
    }

    def of(atoms: Map[VarId, Int], c: Int): Level = {
      ofTerms(atoms, c)
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

      val nextTerms = scala.collection.mutable.HashMap.empty[VarId, Int]
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

    /** The exact invertible shape accepted by level unification and forced-implicit projection. */
    def singleVariableOffset(l: Level): Option[(VarId, Int)] =
      if (l.c != 0 || l.terms.size != 1) None
      else
        Some(l.terms.head)

    /** Pointwise size bound on normalized max-levels, not universe subtyping. */
    def leq(l1: Level, l2: Level): Boolean =
      (l1.c <= l2.c || l2.terms.values.exists(_ >= l1.c)) &&
        l1.terms.forall { case (atom, k) => k <= l2.terms.getOrElse(atom, -1) }

    def mk(varId: VarId): Level = ofTerms(Map(varId -> 0), 0)

    val zero = const(0)
    val one = const(1)

  }

  /**
   * A kind in normal form (spec §2.3): `Kind.lin`, or a set of kind variables, the empty set being `Kind.unr`. Built
   * only by the constructors below, so structural equality is definitional equality and the set is canonical at birth.
   */
  final class Kind private (val isLin: Boolean, val vars: DepSet) extends Value {
    override def tpe: Value = KindTpe
    override def synDeps: DepSet = vars

    def isUnr: Boolean = !isLin && vars.isEmpty

    if (!isUnr) Kind.nonUnrBuilt = true

    private val cachedHashCode: Int = 31 * vars.hashCode() + isLin.hashCode()

    // Its variable set's key, hashed by a loop when first read, as a packed payload's is: a join builds a kind for each
    // set it adds, and hashing each as it is built would make a join of many quadratic.
    override lazy val key: ValueKey.Key = ValueKey.kind(isLin, vars)
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)

    override def equals(obj: Any): Boolean =
      obj match {
        case other: Kind => cachedHashCode == other.cachedHashCode && isLin == other.isLin && vars == other.vars
        case _           => false
      }

    override def hashCode(): Int = cachedHashCode
  }

  object Kind {
    private var nonUnrBuilt = false

    /**
     * Whether a kind other than `unr` has been built. Until one is, no type is linear, since a type's kind is a kind
     * that was built: the linearity fast path. Like FreshVar, it assumes a single checking thread.
     */
    def anyNonUnr: Boolean = nonUnrBuilt

    val unr: Kind = new Kind(isLin = false, DepSet.empty)
    // Lazy, so that no program that never names it builds it.
    lazy val lin: Kind = new Kind(isLin = true, DepSet.empty)

    def variable(id: VarId): Kind = new Kind(isLin = false, DepSet(id))

    /** `lin` absorbs, and otherwise the variable sets unite: `join(unr, k) = k`, `join(lin, k) = lin`. */
    def join(kinds: Iterable[Kind]): Kind =
      if (kinds.exists(_.isLin)) lin
      else
        kinds.foldLeft(unr) { (acc, k) =>
          if (k.vars.isEmpty) acc else if (acc.vars.isEmpty) k else new Kind(isLin = false, acc.vars ++ k.vars)
        }

    /** `outer` contains `inner` when `outer` is `lin`, or `inner` is a set of variables each of which is in `outer`. */
    def contains(outer: Kind, inner: Kind): Boolean =
      outer.isLin || (!inner.isLin && (inner.vars -- outer.vars).isEmpty)

    /** The kind variable this kind is exactly, as refinement and forcing recognize it. */
    def singleVariable(k: Kind): Option[VarId] =
      if (!k.isLin && k.vars.size == 1) Some(k.vars.max) else None
  }

  /**
   * A lifetime in normal form (spec §2.3): the set of its lifetime variables, the empty set being `Lifetime.empty`.
   * Built only by the constructors below, so structural equality is definitional equality and the set is canonical at
   * birth.
   */
  final class Lifetime private (val vars: DepSet) extends Value {
    override def tpe: Value = LifetimeTpe
    override def synDeps: DepSet = vars

    def isEmpty: Boolean = vars.isEmpty

    private val cachedHashCode: Int = vars.hashCode()

    // Hashed when first read, as a kind's is.
    override lazy val key: ValueKey.Key = ValueKey.lifetime(vars)
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)

    override def equals(obj: Any): Boolean =
      obj match {
        case other: Lifetime => cachedHashCode == other.cachedHashCode && vars == other.vars
        case _               => false
      }

    override def hashCode(): Int = cachedHashCode
  }

  object Lifetime {
    val empty: Lifetime = new Lifetime(DepSet.empty)

    def variable(id: VarId): Lifetime = new Lifetime(DepSet(id))

    /** Set union: associative, commutative, idempotent, with `union(empty, x) = x`. */
    def union(lifetimes: Iterable[Lifetime]): Lifetime =
      lifetimes.foldLeft(empty) { (acc, l) =>
        if (l.isEmpty) acc else if (acc.isEmpty) l else new Lifetime(acc.vars ++ l.vars)
      }

    /** `outer` contains `inner` when every element of `inner` is one of `outer`. */
    def contains(outer: Lifetime, inner: Lifetime): Boolean = (inner.vars -- outer.vars).isEmpty

    /** `l` less the variables `ids`: a function type's scope without the lifetimes its own group binds (spec §2.4). */
    def less(l: Lifetime, ids: DepSet): Lifetime =
      if (!l.vars.intersects(ids)) l else new Lifetime(l.vars -- ids)

    /** The lifetime variable this lifetime is exactly, as refinement and forcing recognize it. */
    def singleVariable(l: Lifetime): Option[VarId] =
      if (l.vars.size == 1) Some(l.vars.max) else None
  }

  /**
   * A sort, built only by `Sorts`, which also answers every question about which sort it is. There is no extractor and
   * no structural equality: two sorts are compared only by conversion, so `==` on a sort is a kernel bug and throws
   * rather than silently answering false.
   */
  final class VSort private[raccoonlang] (val isProp: Boolean, val level: Level, val kind: Kind, val scope: Lifetime)
    extends Classifier {
    override lazy val tpe: Value = Sorts.sort(if (isProp) Level.zero else Level.succ(level), Kind.unr, scope)

    override val synDeps: DepSet = DepSet.unionAll(Iterator(level.synDeps, kind.synDeps, scope.synDeps))
    override val key: ValueKey.Key = ValueKey.sort(isProp, level, kind, scope)
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)

    override def equals(obj: Any): Boolean = wtf(s"Sort $this compared structurally; compare sorts by conversion")
    override def hashCode(): Int = wtf(s"Sort $this hashed structurally; sorts are never collection keys")
  }

  // The classifier is a thunk, not a stored sort: a Pi's universe depends on the env it is
  // evaluated in (level-polymorphic binder types), so residuals carry no classifier and each VPi
  // instance derives its own from its binders and codomain (Interpreter.piClassifier). A Pi that
  // binds a level is `Large`.
  // Binders are the checked CoreAst.Binder nodes themselves: a VPi is its syntax plus a closure.
  // `closureKind` and `closureScope` are the function type's closure (spec §1) in normal form; they are part of its
  // identity, so its key mixes them in and conversion compares them exactly. `mentionedScope` is what its captures
  // hold, read as a lambda's derived closure reads them, which its sort counts; it is part of its identity too.
  // Structural `==` is meaningless on a value holding functions, so it throws, as on a sort.
  /** Evaluator-created codomain closure with syntax-checked binder-independence metadata. */
  private[raccoonlang] abstract class CheckedPiCodomain(
      val ownerBinders: Vector[CoreAst.Binder],
      val independent: Boolean,
      val dependencyIndices: Option[Vector[Int]] = None,
      val ownerEnv: Env = null
  ) extends (Env => Value)

  case class VPi(
      env: Env,
      binders: Vector[CoreAst.Binder],
      codomain: Env => Value,
      closureKind: Kind,
      closureScope: Lifetime,
      mentionedScope: Lifetime,
      synDeps: DepSet,
      id: ValueId,
      classifier0: () => Classifier,
      // Fixed at formation, including for a Large Pi into a proposition.
      isPropValued: Boolean
  ) extends Value {
    require(binders.nonEmpty, "VPi requires at least one binder")

    private[raccoonlang] lazy val runtimeSlotLayout: RuntimeSlotLayout =
      RuntimeSlotLayout(binders.map(_.localRef))

    private[raccoonlang] lazy val runtimeSlotPrefixLayouts: RuntimeSlotPrefixCache =
      new RuntimeSlotPrefixCache(runtimeSlotLayout)

    override lazy val tpe: Classifier = classifier0()
    override val key: ValueKey.Key = ValueKey.pi(id, binders, closureKind, closureScope, mentionedScope)
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)

    override def equals(obj: Any): Boolean = wtf(s"Function type $this compared structurally; compare by conversion")
    override def hashCode(): Int = wtf(s"Function type $this hashed structurally; it is never a collection key")

    /** How many explicit arguments this Pi's own binder group takes. */
    lazy val numExplicit: Int = binders.count(_.mode == BinderMode.Explicit)

    /** How many evidence binders this Pi's own binder group has, which a bracket group supplies all of. */
    lazy val numEvidence: Int = binders.count(_.mode == BinderMode.Evidence)

    /** Argument positions whose values determine the Pi application's identity and dependencies. */
    private[raccoonlang] lazy val determiningArgIndices: Vector[Int] =
      if (numEvidence == 0) Vector.empty
      else {
        val indices = Vector.newBuilder[Int]
        var index = 0
        while (index < binders.length) {
          if (binders(index).mode != BinderMode.Evidence) indices += index
          index += 1
        }
        indices.result()
      }

    /**
     * The independent result belongs to this immutable closure instance and is computed once, safely across threads.
     */
    private[this] lazy val independentCodomain: Value = codomain(env)

    /** Constructor-only eligibility is derived on first constructor application, without allocating a plan object. */
    private[this] lazy val hasIndependentConstructorCodomain: Boolean =
      codomain match {
        case checked: CheckedPiCodomain =>
          checked.independent && (checked.ownerBinders.asInstanceOf[AnyRef] eq binders.asInstanceOf[AnyRef])
        case _ => false
      }

    /** A checked syntax closure may evaluate its codomain with just the binders that its code mentions. */
    private[this] lazy val constructorDependencies: Option[Vector[Int]] =
      codomain match {
        case checked: CheckedPiCodomain
            if (checked.ownerBinders.asInstanceOf[AnyRef] eq binders.asInstanceOf[AnyRef]) &&
              (checked.ownerEnv.asInstanceOf[AnyRef] eq env.asInstanceOf[AnyRef]) =>
          checked.dependencyIndices.filter(indices =>
            indices.nonEmpty &&
              indices.forall(index =>
                index >= 0 && index < binders.length && binders(index).mode != BinderMode.Evidence
              )
          )
        case _ => None
      }

    private[this] lazy val constructorDependencyLayout: RuntimeSlotLayout =
      RuntimeSlotLayout(constructorDependencies.get.map(index => binders(index).localRef))

    private final class ConstructorResultEntry(val arguments: Vector[Value], val result: Value)
    @volatile private[this] var constructorResults = Vector.empty[ConstructorResultEntry]

    /** Reference identity preserves the exact argument values and all their type annotations in a cached result. */
    private def sameConstructorArguments(
        entry: ConstructorResultEntry,
        indices: Vector[Int],
        args: Vector[Value]
    ): Boolean = {
      var position = 0
      while (position < indices.length) {
        if (!(entry.arguments(position).asInstanceOf[AnyRef] eq args(indices(position)).asInstanceOf[AnyRef]))
          return false
        position += 1
      }
      true
    }

    private def checkedConstructorArguments(args: Vector[Value]): Unit = {
      var index = 0
      while (index < args.length) {
        Env.assertCanonicalProof(Value.canonicalizeProof(args(index)))
        index += 1
      }
    }

    private def dependentConstructorResult(indices: Vector[Int], args: Vector[Value]): Value = {
      checkedConstructorArguments(args)
      val cached = constructorResults
      var index = 0
      while (index < cached.length) {
        val entry = cached(index)
        if (sameConstructorArguments(entry, indices, args)) return entry.result
        index += 1
      }

      val relevantArgs = indices.map(args)
      val result = codomain(env.bindRuntimeLocals(constructorDependencyLayout, relevantArgs))
      if (
        result.synDeps.isEmpty && Blocker.unapply(result).isEmpty &&
        relevantArgs.forall(arg => arg.synDeps.isEmpty && Blocker.unapply(arg).isEmpty)
      ) synchronized {
        val current = constructorResults
        if (!current.exists(sameConstructorArguments(_, indices, args)))
          constructorResults = (new ConstructorResultEntry(relevantArgs, result) +: current).take(4)
      }
      result
    }

    /** Constructor applications cache a checked independent result on this Pi instance; all others instantiate args. */
    private[raccoonlang] def constructorResultType(instantiatedEnv: => Env): Value =
      if (hasIndependentConstructorCodomain) independentCodomain else codomain(instantiatedEnv)

    private[raccoonlang] def constructorResultType(args: Vector[Value], instantiatedEnv: => Env): Value =
      if (hasIndependentConstructorCodomain) independentCodomain
      else
        constructorDependencies match {
          case Some(indices) => dependentConstructorResult(indices, args)
          case None          => codomain(instantiatedEnv)
        }

    /**
     * Implicit telescope indices grouped by the *explicit* argument position their projection spec roots at. Specs
     * always root at an explicit binder, so walking the explicit args in order lands every implicit exactly once.
     *
     * Derived from `binders` alone, so it survives `copy` of any other field.
     */
    lazy val implicitRoots: Map[Int, Vector[Int]] =
      binders.zipWithIndex
        .collect {
          case (binder, idx) if binder.mode == BinderMode.Implicit =>
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

  /**
   * An application that does not reduce: a neutral or blocked head's, or a constructor's. It stores its arguments as it
   * is given them, deferred evidence included, and `args` forces them when first read (`DeferredEvidence`), so building
   * one evaluates no proposition.
   *
   * Its evidence arguments, those at its head's evidence binders or its constructor's evidence fields, are determined
   * by the rest: each is a proof of its binder's proposition, evaluated from the head's type and the arguments before
   * it, and proofs are irrelevant. So its dependencies, key and conversion read only `determiningArgs`, the others, and
   * only a use of the arguments themselves forces evidence (docs/kernel.md#evidence-arguments). Ordinary applications
   * compute their key when built. The sole delayed-key exception is an exact packed `String.mk` result created through
   * a validated native String.append layout; its one child is a closed packed payload, and the same application key is
   * memoized if a consumer requests it.
   */
  sealed abstract class VApp private (val head: Value, stored: Vector[Value], val tpe: Value, val blockedOn: DepSet)
    extends Value {
    require(stored.nonEmpty || blockedOn.isEmpty, "Blocked application requires at least one argument")
    head match {
      case h: ConstructorHead =>
        require(blockedOn.isEmpty, s"Constructor ${h.name} cannot be blocked")
        val expectedArgs = h.totalArity - h.numErasedFamilyArgs
        require(
          stored.length == expectedArgs,
          s"Constructor ${h.name} stores ${stored.length} args, expected $expectedArgs"
        )
      case _ =>
    }

    /** The stored arguments less the evidence ones, which they and the head determine. None of them is deferred. */
    private[raccoonlang] val determiningArgs: Vector[Value] = VApp.determiningArgs(head, stored)

    override val synDeps: DepSet =
      DepSet.unionAll(Iterator(head.synDeps) ++ determiningArgs.iterator.map(_.synDeps) ++ Iterator(tpe.synDeps))
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)

    // Memoized without a lock: computing it again yields the same arguments, since each deferred proof forces once.
    private[this] var forcedArgs: Vector[Value] = null

    def args: Vector[Value] = {
      if (forcedArgs == null)
        forcedArgs =
          if (stored.exists { case _: DeferredEvidence => true; case _ => false }) stored.map(forced) else stored
      forcedArgs
    }

    /**
     * The explicit arguments, as stored, when the application saturates `pi`, its head's type: none of them is
     * evidence, so reading them forces nothing. Printing reads them, since it shows only a call's explicit arguments.
     */
    private[raccoonlang] def explicitArgs(pi: VPi): Option[Vector[Value]] =
      Option.when(stored.length == pi.binders.length) {
        stored.zip(pi.binders).collect { case (arg, binder) if binder.mode == BinderMode.Explicit => arg }
      }

    /**
     * The arguments as stored, deferred evidence unforced. Only a reader that forces nothing itself reads these:
     * rebuilding the application, a match or destructuring that binds a constructor's fields to locals, which force
     * them where they are looked up, implicit projection, which forces the one it reads, and printing, which shows no
     * evidence.
     */
    private[raccoonlang] def storedArgs: Vector[Value] = stored

    // Structural equality compares the parts the key is built from, as conversion does, and so hashes by key.
    override def equals(other: Any): Boolean =
      other match {
        case that: VApp =>
          (this eq that) || (head == that.head && determiningArgs == that.determiningArgs && tpe == that.tpe &&
            blockedOn == that.blockedOn)
        case _ => false
      }

    override def hashCode(): Int = key.hashCode()
  }

  object VApp {
    private final class EagerVApp(head: Value, stored: Vector[Value], tpe: Value, blockedOn: DepSet)
      extends VApp(head, stored, tpe, blockedOn) {
      override val key: ValueKey.Key = ValueKey.application(head, this.determiningArgs, tpe)
    }

    /**
     * Native append creates a flat packed String.mk application whose key is often never needed before the next append
     * or printing. Cache the unchanged application key on first demand so those intermediate suffixes are not rehashed.
     */
    private final class DeferredStringAppendVApp(
        stored: Vector[Value],
        tpe: Value,
        layout: SourceStringLayout
    ) extends VApp(layout.stringMk, stored, tpe, DepSet.empty) {
      @volatile private[this] var cachedApplicationKey: ValueKey.Key = null

      override def key: ValueKey.Key = {
        var result = cachedApplicationKey
        if (result eq null)
          synchronized {
            result = cachedApplicationKey
            if (result eq null) {
              result = ValueKey.application(head, this.determiningArgs, tpe)
              cachedApplicationKey = result
            }
          }
        result
      }

      def keyIsMaterialized: Boolean = cachedApplicationKey ne null
    }

    def apply(head: Value, args: Vector[Value], tpe: Value, blockedOn: DepSet = DepSet.empty): VApp =
      new EagerVApp(head, args, tpe, blockedOn)

    /** Create only the packed sole field of a validated, closed String.mk result; there is no general delay switch. */
    private[raccoonlang] def deferredStringAppendResult(
        layout: SourceStringLayout,
        storedArgs: Vector[Value],
        tpe: Value
    ): VApp = {
      require(layout.charConstructor.nonEmpty, "Deferred String.append key requires a reversible Char.ofNat layout")
      require(layout.stringMk.totalArity == 1 && layout.stringMk.numErasedFamilyArgs == 0)
      require(
        storedArgs match {
          case Vector(packed: VPacked) =>
            (packed.codec eq layout.charListCodec) && ValueEquivalence
              .defEq(packed.tpe, layout.charListCodec.listCharTpe)
          case _ => false
        },
        "Deferred String.append key requires the validated packed CharList field"
      )
      require(tpe.synDeps.isEmpty && !Sorts.isProposition(tpe), "Deferred String.append result must be closed data")
      require(ValueEquivalence.defEq(tpe, layout.stringTpe), "Deferred String.append result has the wrong String type")
      Value.canonicalizeProof(new DeferredStringAppendVApp(storedArgs, tpe, layout)) match {
        case app: VApp => app
        case _         => wtf("A validated String.append result was canonicalized to a non-application")
      }
    }

    /** Internal test observability for proving that append does not force intermediate application keys. */
    private[raccoonlang] def deferredStringAppendKeyMaterialized(app: VApp): Option[Boolean] = app match {
      case delayed: DeferredStringAppendVApp => Some(delayed.keyIsMaterialized)
      case _                                 => None
    }

    private[Value] def determiningArgs(head: Value, stored: Vector[Value]): Vector[Value] =
      head match {
        case constructor: ConstructorHead if constructor.hasEvidenceFields =>
          if (constructor.fieldBinders.length != stored.length)
            wtf(s"An application stores ${stored.length} arguments for ${constructor.fieldBinders.length} binders")
          select(stored, constructor.determiningStoredArgIndices)
        case _: ConstructorHead => stored
        case other =>
          other.tpe match {
            case pi: VPi if pi.numEvidence > 0 =>
              if (pi.binders.length != stored.length)
                wtf(s"An application stores ${stored.length} arguments for ${pi.binders.length} binders")
              select(stored, pi.determiningArgIndices)
            case _ => stored
          }
      }

    private def select(stored: Vector[Value], indices: Vector[Int]): Vector[Value] =
      if (indices.length == stored.length) stored
      else {
        val selected = Vector.newBuilder[Value]
        selected.sizeHint(indices.length)
        var index = 0
        while (index < indices.length) {
          selected += stored(indices(index))
          index += 1
        }
        selected.result()
      }

    def unapply(app: VApp): Some[(Value, Vector[Value], Value, DepSet)] =
      Some((app.head, app.args, app.tpe, app.blockedOn))
  }

  case class NeutralThunk(
      term: CoreAst.Term.Match,
      env: Env,
      id: ValueId.LocalId,
      tpe: Value,
      blockedOn: DepSet
  ) extends Value {
    override val synDeps: DepSet =
      DepSet.unionAll(Iterator(envDeps(env), tpe.synDeps) ++ id.captures.iterator.map(_.synDeps))
    override val key: ValueKey.Key = ValueKey.neutralThunk(id)
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)
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
    override val synDeps: DepSet = id match {
      case ValueId.Const(_) => DepSet.unionAll(Iterator(tpe.synDeps, body.synDeps))
      case ValueId.LocalId(_, params) =>
        DepSet.unionAll(Iterator(tpe.synDeps, body.synDeps) ++ params.iterator.map(_.synDeps))
    }
    override val key: ValueKey.Key = ValueKey.lambda(id)
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)
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
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)
  }

  /**
   * An evidence argument where a checked application runs (PROOF_BY_EVALUATION §1.6): an erased proof of its binder's
   * proposition, which `proposition` evaluates only when the proof is first forced. Evaluation binds a callee's
   * evidence parameters to these, so a call evaluates no proposition, and a decision procedure in one runs when
   * checking discharges it and not when the program runs. Whatever does look at the proof forces it, and sees exactly
   * the canonical proof the proposition determines (docs/kernel.md#proofs-and-elimination), so erasure changes when a
   * proposition is evaluated and never what a program means.
   *
   * It stands only where a value is held without being read: in the arguments `Interpreter.residualArguments` builds,
   * in the environment of the body they run, which forces it where a local is looked up or captured (`Env`), and among
   * the arguments a `VApp` stores, which forces it where they are read. Nothing reads one unforced: anything that does
   * is a kernel bug, so it has no type of its own.
   */
  final class DeferredEvidence private[raccoonlang] (proposition: () => Value) extends Value {
    // Memoized without a lock, like an application's forced arguments; checking is single-threaded.
    private[this] var forcedProof: Value = null

    def proof: Value = {
      if (forcedProof == null) {
        DeferredEvidence.forcings.incrementAndGet()
        forcedProof = canonicalizeProof(VProof(proposition()))
      }
      forcedProof
    }

    /**
     * This evidence with `f` applied to what it holds, as a rebuilt application needs it: to its proof if that has been
     * forced, and otherwise to its proposition when it is, so that mapping forces nothing.
     */
    private[raccoonlang] def map(f: Value => Value): Value =
      if (forcedProof != null) f(forcedProof) else new DeferredEvidence(() => f(proposition()))

    /** What a walk over values that reaches one reports: it escaped the containers that force it. */
    def escaped: Nothing = wtf("Deferred evidence was inspected before it was forced")

    override def tpe: Value = escaped
    override def synDeps: DepSet = escaped
    override def key: ValueKey.Key = escaped
    override def needsStructuralDefEq: Boolean = escaped
  }

  object DeferredEvidence {

    /** How many deferred proofs have been forced, which is how many propositions evaluation has evaluated. */
    private[raccoonlang] val forcings = new java.util.concurrent.atomic.AtomicLong
  }

  /** A value as the kernel may inspect it: deferred evidence forced to its proof, anything else itself. */
  private[raccoonlang] def forced(value: Value): Value =
    value match {
      case deferred: DeferredEvidence => deferred.proof
      case other                      => other
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

    /** Whether this codec owns this sealed payload variant. */
    private[raccoonlang] def acceptsPayload(payload: PackedPayload): Boolean

    /** Semantic payload equality. Codec compatibility is checked by the caller. */
    private[raccoonlang] def payloadEquals(left: PackedPayload, right: PackedPayload): Boolean

    /** Mix the complete payload into a trusted value key. */
    private[raccoonlang] def mixPayloadKey(key: ValueKey.Key, payload: PackedPayload): ValueKey.Key
  }

  sealed trait PackedPayload

  final class NatPayload private[Value] (val value: BigInt) extends PackedPayload

  private[raccoonlang] final case class CharListAppendDisplay(
      prefixLength: Int,
      hasPackedSuffix: Boolean,
      charConstructorName: String
  ) {
    require(prefixLength >= 0, "Packed String display prefix must be non-negative")
    require(!hasPackedSuffix || prefixLength > 0, "Packed String suffix metadata needs a constructor prefix")
  }

  final class CharListPayload private[Value] (
      private val scalars0: Vector[Int],
      private[raccoonlang] val appendDisplay: Option[CharListAppendDisplay]
  ) extends PackedPayload {
    private[raccoonlang] def scalars: Vector[Int] = scalars0
  }

  private[raccoonlang] object PackedPayload {
    def natValue(payload: PackedPayload): BigInt = payload match {
      case nat: NatPayload    => nat.value
      case _: CharListPayload => wtf("Nat codec received a CharList payload")
    }

    def charScalars(payload: PackedPayload): Vector[Int] = payload match {
      case _: NatPayload          => wtf("CharList codec received a Nat payload")
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
        case head +: _ => ("List.cons", Vector(decodeChar(head), VPacked.charListTail(v)))
        case _         => ("List.nil", Vector.empty)
      }

    /** The character a scalar of the payload decodes to. */
    private[raccoonlang] def decodeChar(scalar: Int): Value =
      Interpreter.evalApply(charOfNat, Vector(VPacked.nat(BigInt(scalar), natTpe)))

    override def strictlyLess(candidate: VPacked, root: VPacked): Boolean = {
      val left = PackedPayload.charScalars(candidate.payload)
      val right = PackedPayload.charScalars(root.payload)
      left.length < right.length && right.endsWith(left)
    }

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
      cur = ValueKey.mixCharScalars(cur, scalars)
      cur
    }
  }

  sealed abstract class ValidatedStringLayout private[raccoonlang] {
    def stringTpe: Value
    def charListCodec: CharListCodec

    /**
     * The constructor `Char.ofNat` applies to its argument, when its result is exactly that constructor over it: then
     * `Char.ofNat(s)` is that constructor over `s`, so a character it makes names its scalar (PrettyPrinter).
     */
    def charConstructor: Option[String]
    private[raccoonlang] def eval(scalars: Vector[Int]): Value
  }

  final class SourceStringLayout private[raccoonlang] (
      val stringTpe: Value,
      val stringMk: ConstructorHead,
      val charListCodec: CharListCodec,
      val charConstructor: Option[String]
  ) extends ValidatedStringLayout {
    override private[raccoonlang] def eval(scalars: Vector[Int]): Value =
      Interpreter.evalApply(stringMk, Vector(VPacked.charList(charListCodec, scalars)))

    /** Create a native append result through the checked constructor application path, with its key left pending. */
    private[raccoonlang] def evalAppended(chars: VPacked): Value =
      Interpreter.evalValidatedStringAppend(this, chars)
  }

  /** A closed packed literal. Construction is restricted to the validated factories below. */
  final class VPacked private (
      val codec: PackedCodec,
      private[raccoonlang] val payload: PackedPayload,
      val tpe: Value
  ) extends Value {
    require(codec.acceptsPayload(payload), "Packed codec/payload mismatch")
    require(tpe.synDeps.isEmpty, s"VPacked requires a closed type, got dependencies ${tpe.synDeps}")
    require(!Sorts.isProposition(tpe), s"VPacked requires a non-propositional type, got $tpe")

    override val synDeps: DepSet = tpe.synDeps
    override val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)

    /**
     * Its payload's key, hashed by a loop when first read. A payload is host data, not values, and a packed list's tail
     * is built for each layer decoded, so hashing each one as it is built would make decoding a list quadratic.
     */
    override lazy val key: ValueKey.Key = ValueKey.packed(codec, payload, tpe)

    private[raccoonlang] def natValue: Option[BigInt] = codec match {
      case NatCodec         => Some(PackedPayload.natValue(payload))
      case _: CharListCodec => None
    }

    private[raccoonlang] def charScalars: Option[Vector[Int]] = codec match {
      case NatCodec         => None
      case _: CharListCodec => Some(PackedPayload.charScalars(payload))
    }

    /** Source-like printing metadata for a String.append result; excluded from semantic equality and its key. */
    private[raccoonlang] def charListAppendDisplay: Option[CharListAppendDisplay] =
      codec match {
        case NatCodec => None
        case _: CharListCodec =>
          payload match {
            case chars: CharListPayload => chars.appendDisplay
            case _: NatPayload          => wtf("CharList codec received a Nat payload")
          }
      }
  }

  object VPacked {
    private[raccoonlang] def nat(value: BigInt, tpe: Value): VPacked = {
      require(value >= 0, s"Packed Nat payload must be non-negative: $value")
      require(tpe.synDeps.isEmpty, s"Packed Nat type must be closed, got dependencies ${tpe.synDeps}")
      new VPacked(NatCodec, new NatPayload(value), tpe)
    }

    private[raccoonlang] def charList(
        codec: CharListCodec,
        scalars: Vector[Int],
        appendDisplay: Option[CharListAppendDisplay] = None
    ): VPacked = {
      require(scalars.forall(UnicodeScalarString.isScalar), "Packed string contains a non-Unicode scalar")
      charListKnown(codec, scalars, appendDisplay)
    }

    /** Used only with Packed's unforgeable capability, minted while every input scalar is checked or already packed. */
    private[raccoonlang] def charList(
        codec: CharListCodec,
        scalars: Packed.ValidatedCharScalars,
        appendDisplay: Option[CharListAppendDisplay]
    ): VPacked = {
      require(scalars.codec eq codec, "Validated CharList belongs to a different codec")
      charListKnown(codec, scalars.values, appendDisplay)
    }

    private def charListKnown(
        codec: CharListCodec,
        scalars: Vector[Int],
        appendDisplay: Option[CharListAppendDisplay]
    ): VPacked = {
      appendDisplay.foreach { display =>
        require(display.prefixLength <= scalars.length, "Packed String display prefix exceeds its payload")
        require(
          display.hasPackedSuffix || display.prefixLength == scalars.length,
          "Packed String without a packed suffix must be entirely constructor-prefixed"
        )
      }
      new VPacked(codec, new CharListPayload(scalars, appendDisplay), codec.listCharTpe)
    }

    private[raccoonlang] def charListTail(parent: VPacked): VPacked =
      parent.codec match {
        case codec: CharListCodec =>
          val scalars = PackedPayload.charScalars(parent.payload)
          if (scalars.nonEmpty) {
            val nextDisplay = parent.charListAppendDisplay.flatMap { display =>
              require(display.prefixLength > 0, "Packed String display metadata outlived its constructor prefix")
              val prefixLength = display.prefixLength - 1
              // Once the constructor prefix is exhausted, a packed suffix is again an ordinary packed literal.
              if (prefixLength == 0 && display.hasPackedSuffix) None
              else Some(display.copy(prefixLength = prefixLength))
            }
            new VPacked(codec, new CharListPayload(scalars.tail, nextDisplay), codec.listCharTpe)
          } else wtf("Cannot decode the tail of an empty packed CharList")
        case NatCodec => wtf("CharList tail requested from a packed Nat")
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

    /** Its name's key, which its applications mix in. */
    private[raccoonlang] val nameKey: ValueKey.Key = ValueKey.constructorName(name)

    // A nullary constructor is already a value in constructor form: a global lookup hands back the bare head where
    // `evalRef` hands back `VCtor(h, [], tpe)`. Both spellings denote the same value, so the bare head keys exactly as
    // that application would, or defEq's key fast path would call one unequal to the other.
    override val key: ValueKey.Key =
      if (totalArity == 0) ValueKey.application(this, Vector.empty, tpe) else nameKey

    // Decided when first asked, which building its first application does, rather than when it is built: a constructor
    // is built while its family is checked, before its type need be evaluable. It has no children, so this walks
    // nothing.
    override lazy val needsStructuralDefEq: Boolean = Value.needsStructuralDefEq(this)

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

    /** Whether any field is an evidence field, which its applications' dependencies, keys and conversion skip. */
    lazy val hasEvidenceFields: Boolean = fieldBinders.exists(_.mode == BinderMode.Evidence)

    /** Stored argument positions that determine a constructor application's identity and dependencies. */
    private[raccoonlang] lazy val determiningStoredArgIndices: Vector[Int] =
      if (!hasEvidenceFields) Vector.empty
      else {
        val indices = Vector.newBuilder[Int]
        var index = 0
        while (index < fieldBinders.length) {
          if (fieldBinders(index).mode != BinderMode.Evidence) indices += index
          index += 1
        }
        indices.result()
      }

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

  /**
   * A constructor as its family's metadata records it. `fieldSources` is where each stored field occurs among the
   * arguments of the constructor's result type, compiled once its family is checked, for a family whose instances may
   * be propositions; it is absent otherwise, and while its family is being checked. ProofReconstruction reads it both
   * to reconstruct a proof and to discharge evidence (PROOF_BY_EVALUATION §1.2).
   */
  final case class ConstructorMeta(
      shortName: String,
      canonicalName: String,
      fieldSources: Option[Vector[ProofFieldSource]]
  )

  /** A stored field's declaration-time source in the family result. */
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
   * admitted. The native positivity walker nests through a previously declared family by reading these.
   */
  final case class CheckedInductiveBlockSchema(
      key: InductiveBlockKey,
      positiveParams: DepSet
  ) extends InductiveBlockDescriptor {
    validatePositiveParams()
  }

  /**
   * A family's checked metadata. `seal` is present when the family is sealed to its module (Sealing).
   * `evidenceEligible` says its instances are discharged through their evidence fields (Discharge, rule 2).
   */
  final case class InductiveMeta(
      constructors: Vector[ConstructorMeta],
      familyArity: Int,
      block: InductiveBlockDescriptor,
      projectionInfo: Option[ProjectionInfo],
      proofRecovery: Option[ProofRecoveryInfo],
      seal: Option[Sealing.Seal],
      evidenceEligible: Boolean
  ) {
    require(familyArity >= block.key.numParams, "Inductive family arity must contain the common parameter prefix")
    require(projectionInfo.isEmpty || constructors.length == 1, "Only one-constructor families can be projected")
    require(!evidenceEligible || projectionInfo.nonEmpty, "An evidence-eligible family has one constructor")
    require(proofRecovery.isEmpty || constructors.length == 1, "Only one-constructor families can recover proof fields")
    require(
      proofRecovery.forall(info => projectionInfo.contains(info.projectionInfo)),
      "Proof recovery must share its family's projection metadata"
    )

    lazy val constructorNames: Vector[String] = constructors.map(_.canonicalName)
  }

  sealed trait ConstType
  case class Inductive(meta: InductiveMeta) extends ConstType

  /**
   * A trusted axiom whose type ends in a sort, as `Quot` 's does: a type former, which names each of its lifetime
   * parameters in its declared scope as a family does (`Sorts.requireNamesLifetimeParameters`).
   */
  case object TypeFormer extends ConstType

  /**
   * Any other axiom's, a stuck builtin's or a checked recursive call's head: an application of it is blocked.
   */
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

    /** Reads the fields only of a constructor's application, so it forces no other application's arguments. */
    def unapply(value: Value): Option[(ConstructorHead, Vector[Value], Value)] =
      value match {
        case app: VApp => ConstructorApp.unapply(app).map(head => (head, app.args, app.tpe))
        case _         => None
      }
  }

  /** A constructor's application, by its head alone, so reading none of its fields and forcing no evidence field. */
  object ConstructorApp {
    def unapply(value: Value): Option[ConstructorHead] =
      value match {
        case app: VApp if app.blockedOn.isEmpty =>
          app.head match {
            case head: ConstructorHead => Some(head)
            case _                     => None
          }
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

    /**
     * The same layer with a constructor application's fields as stored, its evidence fields unforced
     * (`VApp.storedArgs`): for a match or destructuring, which binds them to locals that force them where looked up,
     * and for implicit projection, which forces the one field it reads.
     */
    object Stored {
      def unapply(value: Value): Option[(String, Vector[Value])] =
        value match {
          case app: VApp  => ConstructorApp.unapply(app).map(head => (head.name, app.storedArgs))
          case p: VPacked => Some(p.codec.decodeHead(p))
          case _          => None
        }
    }
  }

  // Blocker and Blocked read an application's blockers alone, never its arguments.
  object Blocker {
    def unapply(value: Value): Option[DepSet] =
      value match {
        case Var(_, id, _)                                             => Some(DepSet(id))
        case app: VApp if app.blockedOn.nonEmpty                       => Some(app.blockedOn)
        case NeutralThunk(_, _, _, _, blockedOn) if blockedOn.nonEmpty => Some(blockedOn)
        case _                                                         => None
      }
  }

  object Blocked {
    def unapply(value: Value): Option[DepSet] =
      value match {
        case app: VApp if app.blockedOn.nonEmpty                       => Some(app.blockedOn)
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

    /** Reads an application's arguments only once its head is a family's. */
    def unapply(value: Value): Option[InductiveFamilyInstance] =
      value match {
        case head @ VConst(_, Inductive(meta), _) if meta.familyArity == 0 =>
          Some(InductiveFamilyInstance(head, meta, Vector.empty))
        case app: VApp if app.blockedOn.isEmpty =>
          app.head match {
            case head @ VConst(_, Inductive(meta), _) if app.args.length == meta.familyArity =>
              Some(InductiveFamilyInstance(head, meta, app.args))
            case _ => None
          }
        case _ => None
      }
  }

}
