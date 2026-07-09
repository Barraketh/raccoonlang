package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

object ValueEquivalence {

  /**
   * A failed unification. `apart` means the two values are provably unequal: the failure is rooted in a data
   * constructor clash whose no-confusion principle is derivable (a Type-valued inductive), so callers may treat the
   * equation as refutable. When `apart` is false the equation is merely unsolvable by this algorithm and must NOT be
   * used as evidence of disequality: the sides may still be propositionally equal (e.g. via Quot.sound, proof
   * irrelevance, or — once added — propext/funext). See docs/kernel-theory.md §5.
   */
  final case class UnifyFailure(v1: Value, v2: Value, apart: Boolean) {
    def asStuck: UnifyFailure = if (apart) copy(apart = false) else this
  }

  /**
   * What a successful link is allowed to mean.
   *
   * `Solve`: links are choices — any store that makes the equation true is acceptable. Congruence makes linking sound
   * under arbitrary frames (`?m := b` justifies `f ?m ~ f b` even for non-injective `f`). This is what elaboration and
   * instance search need.
   *
   * `Invert`: links are consequences — the caller will treat every link as a fact forced by the equation (match
   * refinement checks branches under them). A link made beneath a non-invertible frame is not a consequence (`f x = f
   * y` does not force `x = y` for non-injective `f`), so Invert refuses it and reports the equation as stuck.
   */
  sealed trait UnifyMode
  object UnifyMode {
    case object Solve extends UnifyMode
    case object Invert extends UnifyMode
  }

  // The value's type is a proposition (not the sort Prop), i.e. the value is a proof.
  private def typeLivesInProp(tpe: Value): Boolean =
    tpe match {
      case PropTpe => false
      case tpe0 =>
        tpe0.tpe match {
          case PropTpe => true
          case _       => false
        }
    }

  def defEq(
      v1: Value,
      v2: Value,
      propIrrelevant: Boolean
  ): Boolean =
    DefEq.defEq(v1, v2)(propIrrelevant)

  // Throwing convenience wrapper; only used by tests.
  def unify(v1: Value, v2: Value, meta: EqStore, mode: UnifyMode = UnifyMode.Solve): EqStore =
    tryUnify(v1, v2, meta, mode) match {
      case Right(eqStore) => eqStore
      case Left(failed)   => throw UnificationFailed(failed.v1, failed.v2)
    }

  def tryUnify(
      v1: Value,
      v2: Value,
      meta: EqStore,
      mode: UnifyMode
  ): Either[UnifyFailure, EqStore] =
    Unify.tryUnify(v1, v2, meta, Unify.Ctx(mode))

  private object DefEq {
    case class RelatedPis(vars: Vector[Value], out1: Value, out2: Value)

    def relatePis(pi1: VPi, pi2: VPi): Option[RelatedPis] = {
      if (
        pi1.binders.zip(pi2.binders).exists { case (b1, b2) =>
          b1.isInstance != b2.isInstance || b1.isImplicit != b2.isImplicit
        }
      )
        return None

      val nextEnv1 = BinderOps.freshen(pi1)
      val sharedVars = pi1.binders.map(binder => nextEnv1(binder.localRef))
      val nextEnv2 =
        try BinderOps.checkAndInstantiate(pi2.binders, pi2.env, sharedVars)
        catch { case _: TypeMismatch => return None }

      val out1 = pi1.codomain(nextEnv1)
      val out2 = pi2.codomain(nextEnv2)

      Some(RelatedPis(sharedVars, out1, out2))
    }

    private def defEqPi(pi1: VPi, pi2: VPi)(implicit
        propIrrelevant: Boolean
    ): Option[Vector[Value]] =
      relatePis(pi1, pi2) match {
        case Some(related) if defEq(related.out1, related.out2) => Some(related.vars)
        case _                                                  => None
      }

    private def defEqLamId(id1: ValueId, id2: ValueId)(implicit
        propIrrelevant: Boolean
    ): Boolean = {
      (id1, id2) match {
        case (ValueId.Const(n1), ValueId.Const(n2)) if n1 == n2 => true
        case (l1: ValueId.LocalId, l2: ValueId.LocalId)
            if l1.nodeId == l2.nodeId && l1.captures.length == l2.captures.length =>
          l1.captures.zip(l2.captures).forall { case (v1, v2) => defEq(v1, v2) }
        case _ => false
      }
    }

    private def sameValueObject(v1: Value, v2: Value): Boolean =
      v1.asInstanceOf[AnyRef] eq v2.asInstanceOf[AnyRef]

    private def shouldTryStructuralDefEq(a: Value, b: Value): Boolean =
      a.needsStructuralDefEq || b.needsStructuralDefEq

    private def proofIrrelevant(a: Value, b: Value)(implicit
        propIrrelevant: Boolean
    ): Boolean =
      propIrrelevant && typeLivesInProp(a.tpe) && defEq(a.tpe, b.tpe)

    private def defEqStructural(a: Value, b: Value)(implicit
        propIrrelevant: Boolean
    ): Boolean =
      (a, b) match {
        case (PropTpe, PropTpe)                               => true
        case (LevelTpe, LevelTpe)                             => true
        case (l1: Level, l2: Level)                           => l1 == l2 || Level.leq(l1, l2) && Level.leq(l2, l1)
        case (s1: VSort, s2: VSort)                           => defEq(s1.level, s2.level)
        case (VConst(n1, _, _), VConst(n2, _, _)) if n1 == n2 => true
        case (p1: VPi, p2: VPi) if p1.binders.length == p2.binders.length => defEqPi(p1, p2).isDefined
        case (l1: VLam, l2: VLam) if l1.tpe.binders.length == l2.tpe.binders.length =>
          if (l1.eq(l2) || defEqLamId(l1.id, l2.id)) true
          else {
            defEqPi(l1.tpe, l2.tpe) match {
              case Some(vars) =>
                val res1 = Interpreter.runLam(l1, vars)
                val res2 = Interpreter.runLam(l2, vars)
                defEq(res1, res2)
              case None => false
            }
          }

        case (v1: VApp, v2: VApp) if v1.args.length == v2.args.length =>
          defEq(v1.head, v2.head) &&
          v1.args.zip(v2.args).forall { case (arg1, arg2) => defEq(arg1, arg2) } &&
          defEq(v1.tpe, v2.tpe) // Important for constructors

        case (c1: ConstructorHead, c2: ConstructorHead) if c1.name == c2.name => true

        case (s1: NeutralThunk, s2: NeutralThunk) => defEqLamId(s1.id, s2.id)

        case (Var(_, id1, _), Var(_, id2, _)) if id1 == id2 => true
        case _                                              => false
      }

    def defEq(v1: Value, v2: Value)(implicit
        propIrrelevant: Boolean
    ): Boolean = {
      if (sameValueObject(v1, v2)) true
      else if (proofIrrelevant(v1, v2)) true
      else {
        v1.key == v2.key || (shouldTryStructuralDefEq(v1, v2) && defEqStructural(v1, v2))
      }
    }
  }

  private object Unify {
    // EqStore is immutable, so a Left result implies the caller's store is untouched: failed
    // sub-unifications discard their partial links for free. Callers (MatchChecker refinement in
    // particular) rely on this — a mutable-store optimization would silently break it.
    private type Result = Either[UnifyFailure, EqStore]
    private final case class PiUnification(eqStore: EqStore, vars: Vector[Value], watermark: Value.VarId)

    /**
     * Unification context: the mode plus whether every frame descended through so far is invertible.
     *
     * In both modes a link records exactly the equation presented at the point of linking (or its unique forced
     * solution) — the store never invents values. The modes differ in whether *decomposed sub-equations* are
     * consequences of the original equation: descending through a non-invertible frame produces sub-equations that are
     * sufficient but not necessary, so Invert mode (whose links are read as facts) refuses to link beneath one, while
     * Solve mode (whose vars are the elaborator's to instantiate) may.
     */
    final case class Ctx(mode: UnifyMode, invertibleFrame: Boolean = true) {
      def canLinkForced: Boolean = mode == UnifyMode.Solve || invertibleFrame
      def enterNonInvertibleFrame: Ctx = if (invertibleFrame) copy(invertibleFrame = false) else this
    }

    // Unsolvable, but not refutable: safe for elaboration to give up on, unsound to prune a match case on.
    private def stuck(v1: Value, v2: Value): Result = Left(UnifyFailure(v1, v2, apart = false))
    // Provably unequal: rooted in no-confusion evidence, safe to prune a match case on.
    private def apart(v1: Value, v2: Value): Result = Left(UnifyFailure(v1, v2, apart = true))

    /**
     * Heads whose applications may be decomposed invertibly: the equation `H as ~ H bs` forces the argument equations
     * definitionally. True for constructors of genuine inductives (no-confusion) and for inductive family heads
     * (definitional injectivity of type formers). Everything else — opaque constants, axioms, quotient constructors,
     * blocked heads — is an arbitrary function: decomposition is only a solving heuristic, and its failures prove
     * nothing.
     *
     * Note this is about invertibility (links and failure pass-through), not apartness: head *clashes* are refutations
     * only for data constructors (see the VCtor case). Family-head clashes prove nothing propositionally — under
     * propositional extensionality distinct Prop-valued families can be equal (And T T = Or T T), and type-former
     * generativity is not derivable even for Type-valued families.
     *
     * TODO(propext): once propositional extensionality is added, invertible decomposition of Prop-sorted family
     * instances appearing in *index* positions (e.g. the sides of an `Eq Prop` scrutinee) is itself no longer a
     * consequence; the root instantiation probe in MatchChecker remains eliminator-justified. Distinguishing the two
     * needs a root-vs-index marker on Ctx.
     */
    private def definitionallyInjectiveHead(head: Value): Boolean =
      head match {
        case h: ConstructorHead         => h.noConfusion
        case VConst(_, Inductive(_), _) => true
        case _                          => false
      }

    // Proof irrelevance makes all proofs of a proposition equal, so constructor shape carries no
    // propositional evidence for proofs: inl/inr of the same Or are equal, and Exists.intro is not
    // injective in its witness. Proofs are therefore excluded from apartness and from invertible
    // decomposition.
    private def isProofValue(value: Value): Boolean = typeLivesInProp(value.tpe)

    // Rejects solutions that let scope-local fresh vars escape. This also catches transitive
    // escapes (?a := f(?b), ?b := freshVar): every escape chain contains at least one link made
    // since `start` whose immediate solution mentions a var above the watermark, because stores
    // returned by inner unifications never contain out-of-scope vars themselves.
    private def newSolutionDependsOnFreshVar(start: EqStore, store: EqStore, watermark: Value.VarId): Boolean =
      store.subst.exists { case (id, solution) =>
        !start.subst.contains(id) && solution.synDeps.nonEmpty && solution.synDeps.max > watermark
      }

    // Pi-former injectivity is not assumed, so all failures below are reported as stuck and links made
    // inside binder types or the codomain are not consequences of the Pi equation (non-invertible frame).
    private def tryUnifyPis(pi1: VPi, pi2: VPi, eqStore: EqStore, ctx: Ctx): Either[UnifyFailure, PiUnification] = {
      if (
        pi1.binders.length != pi2.binders.length ||
        pi1.binders.zip(pi2.binders).exists { case (b1, b2) =>
          b1.isInstance != b2.isInstance || b1.isImplicit != b2.isImplicit
        }
      )
        return Left(UnifyFailure(pi1, pi2, apart = false))

      val innerCtx = ctx.enterNonInvertibleFrame
      val watermark = FreshVar.currentId
      var curStore = eqStore
      var env1 = pi1.env
      var env2 = pi2.env
      val sharedVars = Vector.newBuilder[Value]

      pi1.binders.zip(pi2.binders).foreach { case (binder1, binder2) =>
        val ty1 = ValueOps.materialize(Interpreter.evalTypeTerm(binder1.ty, env1), curStore)
        val ty2 = ValueOps.materialize(Interpreter.evalTypeTerm(binder2.ty, env2), curStore)
        tryUnify(ty1, ty2, curStore, innerCtx) match {
          case Right(nextStore) => curStore = nextStore
          case Left(failed)     => return Left(failed.asStuck)
        }

        val (_, shared) = FreshVar.freshValue(binder1.name, ValueOps.materialize(ty1, curStore))
        env1 = BinderOps.bindValue(env1, binder1, shared)
        env2 = BinderOps.bindValue(env2, binder2, shared)
        sharedVars += shared
      }

      tryUnify(pi1.codomain(env1), pi2.codomain(env2), curStore, innerCtx) match {
        case Right(nextEqStore) =>
          if (newSolutionDependsOnFreshVar(eqStore, nextEqStore, watermark)) Left(UnifyFailure(pi1, pi2, apart = false))
          else Right(PiUnification(nextEqStore, sharedVars.result(), watermark))
        case Left(failed) => Left(failed.asStuck)
      }
    }

    // Thunk identity is a congruence heuristic (same code + same captures => same value); its failures prove
    // nothing, and capture equations are not consequences of the thunk equation (a match expression need not
    // be injective in its captures). The type equation is a consequence: equal values have equal types.
    private def tryUnifyNeutralThunks(v1: NeutralThunk, v2: NeutralThunk, meta: EqStore, ctx: Ctx): Result =
      tryUnify(v1.tpe, v2.tpe, meta, ctx) match {
        case Left(failed) => Left(failed.asStuck)
        case Right(m1) =>
          if (v1.id.captures.length != v2.id.captures.length) stuck(v1, v2)
          else {
            val captureCtx = ctx.enterNonInvertibleFrame
            var curMeta = m1
            val captures = v1.id.captures.zip(v2.id.captures)
            val iter = captures.iterator
            while (iter.hasNext) {
              val (p1, p2) = iter.next()
              tryUnify(p1, p2, curMeta, captureCtx) match {
                case Left(failed) => return Left(failed.asStuck)
                case Right(next)  => curMeta = next
              }
            }
            Right(curMeta)
          }
      }

    // `v + k = l2` has at most one solution (v := l2 - k), so this link is forced. Equations with
    // multiple level atoms (`max(u, v) = c`) have many solutions and are left stuck: a link must
    // record the equation in hand or its unique forced solution, never a chosen value.
    private def unifyLevels(l1: Level, l2: Level, meta: EqStore, ctx: Ctx): Option[EqStore] = {
      if (l1.atoms.size == 1 && l1.c == 0) {
        if (!ctx.canLinkForced) return None
        val (varId, k) = l1.atoms.head
        if (meta.isRefinable(varId) && !meta.occurs(varId, l2) && Level.geq(l2, k)) {
          val other = Level.addOffset(l2, -k)
          Some(meta.addLink(varId, other))
        } else None
      } else None
    }

    private def tryLinkVar(v: Var, other: Value, meta: EqStore, ctx: Ctx): Result = {
      val m1 =
        if (!v.tpe.synDeps.intersects(meta.refinable) && TypeChecker.sortLeq(other.tpe, v.tpe)) meta
        else
          // Eq is homogeneous, so provably-apart types refute the value equation: propagate as-is.
          tryUnify(v.tpe, other.tpe, meta, ctx) match {
            case Left(failed) => return Left(failed)
            case Right(next)  => next
          }
      // Occurs failures are merely stuck: `x ~ succ(x)` is refutable for well-founded data,
      // but we do not currently exploit acyclicity as apartness evidence.
      if (m1.occurs(v.id, other)) stuck(v, other)
      else Right(m1.addLink(v.id, other))
    }

    /**
     * This specifically handles wildcard vars during pattern matching. The problem is that wildcard vars never actually
     * get stored in Env[Value], so they can't be properly quoted. This forces us to prefer the other var as the
     * representative
     */
    private def tryLinkVarToPreferredRepresentative(v1: Var, v2: Var, meta: EqStore, ctx: Ctx): Result = {
      val v1Anonymous = v1.name == "_"
      val v2Anonymous = v2.name == "_"
      val (toLink, representative) =
        if (v1Anonymous && !v2Anonymous) (v1, v2)
        else if (v2Anonymous && !v1Anonymous) (v2, v1)
        else if (v1.id > v2.id) (v1, v2)
        else (v2, v1)

      tryLinkVar(toLink, representative, meta, ctx)
    }

    def tryUnify(v1: Value, v2: Value, meta: EqStore, ctx: Ctx): Result = {
      val a = ValueOps.materialize(v1, meta)
      val b = ValueOps.materialize(v2, meta)

      // Prefer solving refinable vars over the irrelevance shortcut: equating two proofs without
      // descending would leave metas inside them unsolved. Consequently, comparisons of proofs that
      // mention refinable vars DO reach the structural cases below, which is why those cases must
      // themselves respect irrelevance (no apartness or invertible decomposition for proofs).
      val canUseProofIrrelevance =
        !a.synDeps.intersects(meta.refinable) && !b.synDeps.intersects(meta.refinable)
      if (DefEq.defEq(a, b)(propIrrelevant = canUseProofIrrelevance)) return Right(meta)

      (a, b) match {
        case (p1: VPi, p2: VPi) if p1.binders.length == p2.binders.length =>
          tryUnifyPis(p1, p2, meta, ctx).map(_.eqStore)
        case (l1: VLam, l2: VLam) if l1.tpe.binders.length == l2.tpe.binders.length =>
          // We know that the id check failed - falling back to extensional unification. Body links at the
          // fresh shared vars are consequences (equal functions agree everywhere), so ctx is inherited.
          tryUnifyPis(l1.tpe, l2.tpe, meta, ctx) match {
            case Left(failed) => Left(failed)
            case Right(PiUnification(nextMeta, sharedVars, watermark)) =>
              val mappedVars = sharedVars.map(arg => ValueOps.materialize(arg, nextMeta))
              val res1 = Interpreter.runLam(ValueOps.materialize(l1, nextMeta).asInstanceOf[VLam], mappedVars)
              val res2 = Interpreter.runLam(ValueOps.materialize(l2, nextMeta).asInstanceOf[VLam], mappedVars)
              tryUnify(res1, res2, nextMeta, ctx) match {
                case Right(bodyMeta) if newSolutionDependsOnFreshVar(nextMeta, bodyMeta, watermark) => stuck(l1, l2)
                // Deliberate precision loss: body apartness at the fresh var would refute the lambda
                // equation (congrFun), but bodies may compare proofs or propositions where apartness
                // is not propositionally valid, so we downgrade rather than carve out the safe cases.
                case Left(failed) => Left(failed.asStuck)
                case solved       => solved
              }
          }

        // Different constructors of a genuine inductive are disjoint — for data. Proofs are excluded
        // (proof irrelevance equates inl/inr proofs of the same Or), as are heads without no-confusion
        // (e.g. Quot.mk): those can only be identified or separated by their propositional theory.
        case (VCtor(h1, _, _), VCtor(h2, _, _)) if h1.name != h2.name =>
          if (h1.noConfusion && h2.noConfusion && !isProofValue(a) && !isProofValue(b)) apart(a, b)
          else stuck(a, b)

        // Deliberately NOT a refutation: different inductive family heads (bare or applied) are only
        // definitionally distinct. Propositional generativity is not assumed — propext can equate
        // Prop-valued families (And T T = Or T T), so head clashes fall through to stuck.

        case (v1: VApp, v2: VApp) if v1.args.length == v2.args.length =>
          // Decomposition is invertible only for no-confusion heads applied to non-proofs. For any
          // other head it is a solving heuristic: `f a ~ f b` failing on `a ~ b` proves nothing about
          // the applications, and links made below are choices, not consequences (Invert mode refuses
          // them via argCtx).
          val invertible =
            definitionallyInjectiveHead(v1.head) && definitionallyInjectiveHead(v2.head) && !isProofValue(
              v1
            ) && !isProofValue(v2)
          val argCtx = if (invertible) ctx else ctx.enterNonInvertibleFrame
          def frame(failed: UnifyFailure): UnifyFailure = if (invertible) failed else failed.asStuck
          tryUnify(v1.head, v2.head, meta, argCtx) match {
            case Left(failed) => Left(frame(failed))
            case Right(m0) =>
              var curMeta = m0
              // Stuck component equations are postponed and retried after the rest of the spine:
              // an equation like `max(u, v) ~ 1` has no forced solution on its own, but becomes
              // ground once a later argument solves its atoms. Postponement reorders work without
              // ever inventing values. Apart failures are rigid and fail immediately.
              val deferred = Vector.newBuilder[(Value, Value, UnifyFailure)]
              val args = v1.args.zip(v2.args)
              val iter = args.iterator
              while (iter.hasNext) {
                val (arg1, arg2) = iter.next()
                tryUnify(arg1, arg2, curMeta, argCtx) match {
                  case Left(failed) if failed.apart => return Left(frame(failed))
                  case Left(failed)                 => deferred += ((arg1, arg2, failed))
                  case Right(next)                  => curMeta = next
                }
              }
              // Equal values have equal types, so the type equation is a consequence: ctx is inherited.
              tryUnify(v1.tpe, v2.tpe, curMeta, ctx) match { // Important for constructors
                case Left(failed) => return Left(frame(failed))
                case Right(next)  => curMeta = next
              }
              val retryIter = deferred.result().iterator
              while (retryIter.hasNext) {
                val (arg1, arg2, original) = retryIter.next()
                tryUnify(arg1, arg2, curMeta, argCtx) match {
                  case Left(_)     => return Left(frame(original))
                  case Right(next) => curMeta = next
                }
              }
              Right(curMeta)
          }

        case (v1: NeutralThunk, v2: NeutralThunk) if v1.id.nodeId == v2.id.nodeId =>
          tryUnifyNeutralThunks(v1, v2, meta, ctx)

        // Level arithmetic failures are never refutations: an unsolvable constraint may still be satisfiable.
        case (l1: Level, l2: Level) =>
          unifyLevels(l1, l2, meta, ctx)
            .orElse(unifyLevels(l2, l1, meta, ctx))
            .map(Right(_))
            .getOrElse(stuck(l1, l2))

        case (s1: VSort, s2: VSort) => tryUnify(s1.level, s2.level, meta, ctx)

        // Unify FreshVars through ctx. Basic idea: FreshVars can point at things through context
        // unify creates a ctx of pointers. We only create pointers from the top of the chain
        case (v1: Var, v2: Var) if meta.isRefinable(v1.id) && meta.isRefinable(v2.id) =>
          if (ctx.canLinkForced) tryLinkVarToPreferredRepresentative(v1, v2, meta, ctx) else stuck(v1, v2)

        // Link unlinked Var (left) to a non-Var value
        case (v: Var, other) if meta.isRefinable(v.id) =>
          if (ctx.canLinkForced) tryLinkVar(v, other, meta, ctx) else stuck(v, other)

        // Symmetric: link unlinked Var (right) to non-Var value
        case (other, v: Var) if meta.isRefinable(v.id) =>
          if (ctx.canLinkForced) tryLinkVar(v, other, meta, ctx) else stuck(v, other)

        // No no-confusion evidence: unsolvable, but not refutable.
        case _ => stuck(a, b)
      }
    }
  }
}
