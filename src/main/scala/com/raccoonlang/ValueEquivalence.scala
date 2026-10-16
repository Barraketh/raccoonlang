package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.util.control.NonFatal

object ValueEquivalence {

  /**
   * A failed unification. `apart` means the two values are provably unequal: the failure is rooted in a data
   * constructor clash whose no-confusion principle is derivable (a Type-valued inductive), so callers may treat the
   * equation as refutable. When `apart` is false the equation is merely unsolvable by this algorithm and must NOT be
   * used as evidence of disequality: the sides may still be propositionally equal (e.g. via Quot.sound, proof
   * irrelevance, or — once added — propext/funext). See docs/kernel.md#apartness.
   */
  final case class UnifyFailure(v1: Value, v2: Value, apart: Boolean) {
    def asStuck: UnifyFailure = if (apart) copy(apart = false) else this
  }

  /**
   * Definitional conversion is unification with no refinable variables: with an empty store nothing can link, so every
   * rule of the evidence model (docs/kernel.md#equality-and-evidence) reduces to the congruence it would use anyway,
   * and a `Right` is exactly a derivation of `a ≡ b`. There is no second walk over the value forms — see
   * `Unify.tryUnify`.
   */
  def defEq(v1: Value, v2: Value): Boolean =
    Unify.tryUnify(v1, v2, EqStore.empty, Unify.Ctx(invertibleFrame = true, scrutineeTypeRoot = false)).isRight

  /**
   * Proof irrelevance reduces every equation between proof values to the equation between their propositions
   * (docs/kernel.md#proofs-and-elimination). This includes reconstructed constructor proofs, canonical eta-lambdas,
   * erased `VProof` values, and proof-typed Vars. No proof representation may reach structural unification first.
   */
  private object ProofEquation {
    def unapply(pair: (Value, Value)): Option[(Value, Value)] =
      pair match {
        case (left, right) if Sorts.isProposition(left.tpe) && Sorts.isProposition(right.tpe) =>
          Some((left.tpe, right.tpe))
        case _ => None
      }
  }

  /**
   * Unification whose links are consequences: every caller treats a link as a fact forced by the root equation (match
   * refinement checks branches under them). A link made beneath a non-invertible frame is not a consequence (`f x = f
   * y` does not force `x = y` for non-injective `f`), so it is refused and the equation reports stuck. Choice-mode
   * solving (any store that makes the equation true) left with its last clients, unification-based elaboration and
   * instance search.
   */
  def tryUnify(
      v1: Value,
      v2: Value,
      meta: EqStore
  ): Either[UnifyFailure, EqStore] =
    Unify.tryUnify(v1, v2, meta, Unify.Ctx(invertibleFrame = true, scrutineeTypeRoot = false))

  /**
   * Unify a constructor result type with the type of its match scrutinee. The eliminator justifies inversion of a Prop
   * family at this root equation; all structural descent clears that permission.
   */
  def tryUnifyMatchTypes(v1: Value, v2: Value, meta: EqStore): Either[UnifyFailure, EqStore] =
    Unify.tryUnify(v1, v2, meta, Unify.Ctx(invertibleFrame = true, scrutineeTypeRoot = true))

  /**
   * Key-coherence assertions (docs/kernel.md#value-identity): wherever the fast path decides an equation by key alone,
   * the rules below must reach the same verdict. On by default so the whole test suite checks it; disable for
   * benchmarking with -Draccoon.keyAssertions=false.
   */
  private[raccoonlang] val keyAssertionsEnabled: Boolean =
    java.lang.Boolean.parseBoolean(System.getProperty("raccoon.keyAssertions", "true"))

  private object Unify {
    // EqStore is immutable, so a Left result implies the caller's store is untouched: failed
    // sub-unifications discard their partial links for free. Callers (MatchChecker refinement in
    // particular) rely on this — a mutable-store optimization would silently break it.
    private type Result = Either[UnifyFailure, EqStore]
    private final case class PiUnification(eqStore: EqStore, vars: Vector[Value], watermark: Value.VarId)

    /** A stuck equation and the original store needed to tell whether later links can make retry useful. */
    private final case class Postponed(v1: Value, v2: Value, store: EqStore, failure: UnifyFailure) {
      def reachesLinksOf(later: EqStore): Boolean = {
        val linkedSince = later.solvedIds -- store.solvedIds
        linkedSince.nonEmpty &&
        (store.reachable(v1).intersects(linkedSince) || store.reachable(v2).intersects(linkedSince))
      }
    }

    /**
     * Unification context: whether every frame descended through so far is invertible, and whether this is the match's
     * root type equation. Structural descent clears the root-only permission before calling any helper.
     *
     * A link records exactly the equation presented at the point of linking (or its unique forced solution) — the store
     * never invents values. Since links are consumed as consequences of the root equation, linking is legal only while
     * every enclosing frame is invertible: descending through a non-invertible frame produces sub-equations that are
     * sufficient but not necessary, so links beneath one are refused.
     */
    final case class Ctx(invertibleFrame: Boolean, scrutineeTypeRoot: Boolean) {
      def canLinkForced: Boolean = invertibleFrame
      def enterNonInvertibleFrame: Ctx =
        if (invertibleFrame || scrutineeTypeRoot) copy(invertibleFrame = false, scrutineeTypeRoot = false) else this
      def nested: Ctx = if (scrutineeTypeRoot) copy(scrutineeTypeRoot = false) else this
    }

    private def sameValueObject(v1: Value, v2: Value): Boolean =
      v1.asInstanceOf[AnyRef] eq v2.asInstanceOf[AnyRef]

    /**
     * The exemption list of the key-coherence assertion: the atoms whose key is their identity, so the key is the whole
     * of their equality and no rule below restates it. A variable is its id, a constant or constructor head its name,
     * and a level its normal form (the level rule below only links).
     */
    private def keyIsIdentity(a: Value, b: Value): Boolean =
      (a, b) match {
        case (_: Var, _: Var) | (_: VConst, _: VConst) | (_: ConstructorHead, _: ConstructorHead) |
            (_: Level, _: Level) =>
          true
        case _ => false
      }

    private def keysAreInconclusive(a: Value, b: Value): Boolean =
      a.needsStructuralDefEq || b.needsStructuralDefEq

    // Unsolvable, but not refutable: safe for elaboration to give up on, unsound to prune a match case on.
    private def stuck(v1: Value, v2: Value): Result = Left(UnifyFailure(v1, v2, apart = false))
    // Provably unequal: rooted in no-confusion evidence, safe to prune a match case on.
    private def apart(v1: Value, v2: Value): Result = Left(UnifyFailure(v1, v2, apart = true))

    private def constructorClashIsRefutable(a: Value, b: Value, meta: EqStore, noConfusion: Boolean): Boolean = {
      val sameCheckedFamilyAtCommonParameters = (a.tpe, b.tpe) match {
        case (InductiveFamilyValue(family1), InductiveFamilyValue(family2)) if family1.head.name == family2.head.name =>
          val parameterCount = family1.meta.block.key.numParams
          family1.args.length >= parameterCount && family2.args.length >= parameterCount &&
          family1.args.take(parameterCount).zip(family2.args.take(parameterCount)).forall { case (p1, p2) =>
            defEq(ValueOps.materialize(p1, meta), ValueOps.materialize(p2, meta))
          }
        case _ => false
      }
      noConfusion && sameCheckedFamilyAtCommonParameters
    }

    /** A key mismatch cannot refute an equation; it only sends a real no-confusion clash to its rule. */
    private def mismatchRefutableAtHead(a: Value, b: Value, meta: EqStore): Boolean =
      (a, b) match {
        case (VCtor(h1, _, _), VCtor(h2, _, _)) if h1.name != h2.name =>
          constructorClashIsRefutable(a, b, meta, h1.noConfusion && h2.noConfusion)
        case _ => false
      }

    /** Data-family N1 inversion holds at every depth; Prop-family inversion is justified only at the match root. */
    private def familyArgumentsInvertible(value: Value, ctx: Ctx): Boolean =
      !Sorts.isProposition(value) || ctx.scrutineeTypeRoot

    /** An unequal key may hide a refutable equation between arguments of the same invertible checked family. */
    private def familyEquationMayRefute(a: Value, b: Value, ctx: Ctx): Boolean =
      (a, b) match {
        case (InductiveFamilyValue(f1), InductiveFamilyValue(f2)) if f1.head.name == f2.head.name =>
          familyArgumentsInvertible(a, ctx) && familyArgumentsInvertible(b, ctx)
        case _ => false
      }

    /** Whether this application equation permits forced argument links and propagates apartness. */
    private def invertibleApplication(value: VApp, ctx: Ctx): Boolean =
      value match {
        case InductiveFamilyValue(_) => familyArgumentsInvertible(value, ctx)
        case _ =>
          value.head match {
            case h: ConstructorHead => h.noConfusion
            case _                  => false
          }
      }

    // Rejects solutions that let scope-local fresh vars escape. This also catches transitive
    // escapes (?a := f(?b), ?b := freshVar): every escape chain contains at least one link made
    // since `start` whose immediate solution mentions a var above the watermark, because stores
    // returned by inner unifications never contain out-of-scope vars themselves.
    private def newSolutionDependsOnFreshVar(start: EqStore, store: EqStore, watermark: Value.VarId): Boolean =
      store.subst.exists { case (id, solution) =>
        !start.subst.contains(id) && solution.synDeps.nonEmpty && solution.synDeps.max > watermark
      }

    // Pi-former injectivity is not assumed, so all failures below are reported as stuck and links made
    // inside the closure, binder types or the codomain are not consequences of the Pi equation
    // (non-invertible frame).
    //
    // Grouping is part of a function type's identity: two Pis are related binder-by-binder within their
    // single groups, and differing group counts are a failure to derive `≡` (stuck), never apartness.
    // `(a:A)(b:B) -> C` and `(a:A) -> (b:B) -> C` are different types and do not relate here. So is the

    private def tryUnifyPis(pi1: VPi, pi2: VPi, eqStore: EqStore, ctx: Ctx): Either[UnifyFailure, PiUnification] = {
      if (
        pi1.binders.length != pi2.binders.length ||
        pi1.binders.zip(pi2.binders).exists { case (b1, b2) => b1.isImplicit != b2.isImplicit }
      )
        return Left(UnifyFailure(pi1, pi2, apart = false))

      val innerCtx = ctx.enterNonInvertibleFrame
      val watermark = FreshVar.currentId
      var curStore = eqStore
      var env1 = pi1.env
      var env2 = pi2.env
      val sharedVars = Vector.newBuilder[Value]

      pi1.binders.zip(pi2.binders).foreach { case (binder1, binder2) =>
        val ty1 = ValueOps.materialize(Interpreter.evalTerm(binder1.ty, env1), curStore)
        val ty2 = ValueOps.materialize(Interpreter.evalTerm(binder2.ty, env2), curStore)
        tryUnify(ty1, ty2, curStore, innerCtx) match {
          case Right(nextStore) => curStore = nextStore
          case Left(failed)     => return Left(failed.asStuck)
        }

        // One shared binder stands for both sides. It is an ordinary rigid var; structure eta
        // reaches it through the rules.
        val sharedTy = ValueOps.materialize(ty1, curStore)
        val shared = FreshVar.freshValue(binder1.name, sharedTy)._2
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

    /**
     * Same code at the same node with convertible captures, so the two closures denote the same value. This is a
     * recognizer, not a decomposition: it answers only "yes, equal", never links, and its failures say nothing (the
     * extensional comparison follows). Captures are therefore compared by conversion, under a store that cannot link.
     */
    private def sameLamId(id1: ValueId, id2: ValueId): Boolean =
      (id1, id2) match {
        case (ValueId.Const(n1), ValueId.Const(n2)) if n1 == n2 => true
        case (l1: ValueId.LocalId, l2: ValueId.LocalId)
            if l1.nodeId == l2.nodeId && l1.captures.length == l2.captures.length =>
          l1.captures.zip(l2.captures).forall { case (c1, c2) => defEq(c1, c2) }
        case _ => false
      }

    private val neutralComparisonDepth = new ThreadLocal[Int] {
      override def initialValue(): Int = 0
    }

    /**
     * Distinct checked match programs can denote the same stuck computation even when their closure ids differ: one
     * closure may capture a structure while another captures the field reached by its scrutinee projection. Compare the
     * eliminators themselves, using the same fresh constructor fields on both sides.
     *
     * This is a congruence check, so its failures prove nothing and every one of them is stuck. Two distinct match
     * programs are not a clash of anything with a no-confusion principle, and the comparison gives up on any malformed
     * shape, on an exception, and beyond a fixed depth — none of which is evidence about the values. Links made inside
     * are likewise not consequences of the thunk equation (a match need not be injective in its scrutinee or its
     * branches), so the whole comparison runs under a non-invertible frame.
     */
    private def tryUnifyNeutralMatches(left: NeutralThunk, right: NeutralThunk, meta: EqStore, ctx: Ctx): Result = {
      val depth = neutralComparisonDepth.get()
      if (depth >= 16) return stuck(left, right)
      neutralComparisonDepth.set(depth + 1)
      val innerCtx = ctx.enterNonInvertibleFrame
      // The whole comparison either establishes the equation or proves nothing, so partial stores from
      // a run that later gives up are discarded with it: only a complete success returns a store.
      def run(): Result = {
        val leftScrutinee = Interpreter.evalTerm(left.term.scrut, left.env)
        val rightScrutinee = Interpreter.evalTerm(right.term.scrut, right.env)
        var curMeta = meta
        def step(a: Value, b: Value): Boolean =
          tryUnify(a, b, curMeta, innerCtx) match {
            case Right(next) => curMeta = next; true
            case Left(_)     => false
          }

        val shapeAgrees =
          left.term.cases.length == right.term.cases.length &&
            !left.term.cases.zip(right.term.cases).exists { case (l, r) =>
              l.ctorName != r.ctorName || l.argRefs.length != r.argRefs.length
            }

        if (!step(left.tpe, right.tpe) || !step(leftScrutinee, rightScrutinee) || !shapeAgrees) stuck(left, right)
        else
          leftScrutinee.tpe match {
            // Each constructor's fields are taken at the scrutinee type's parameters, so only the result's indices
            // remain to agree with both scrutinee types.
            case InductiveFamilyValue(family) =>
              val branchesAgree = left.term.cases.zip(right.term.cases).forall { case (leftCase, rightCase) =>
                left.env(leftCase.ctorName) match {
                  case head: ConstructorHead =>
                    val (fields, resultType) = BinderOps.freshCtorFields(head, family.args, leftCase.argRefs)
                    step(resultType, leftScrutinee.tpe) && step(resultType, rightScrutinee.tpe) &&
                    step(
                      Interpreter.evalBranch(leftCase, fields, left.env),
                      Interpreter.evalBranch(rightCase, fields, right.env)
                    )
                  case _ => false
                }
              }
              if (branchesAgree) Right(curMeta) else stuck(left, right)
            case _ => stuck(left, right)
          }
      }

      try run()
      catch {
        // A broken kernel invariant is not a comparison that did not work out; it must not be
        // absorbed into "these two are stuck".
        case internal: InternalError => throw internal
        case NonFatal(_)             => stuck(left, right)
      } finally {
        if (depth == 0) neutralComparisonDepth.remove()
        else neutralComparisonDepth.set(depth)
      }
    }

    // `v + k = l2` has at most one solution (v := l2 - k), so this link is forced. Equations with
    // multiple level atoms (`max(u, v) = c`) have many solutions and are left stuck: a link must
    // record the equation in hand or its unique forced solution, never a chosen value.
    private def unifyLevels(l1: Level, l2: Level, meta: EqStore, ctx: Ctx): Option[EqStore] = {
      Level.singleVariableOffset(l1) match {
        case Some((varId, k)) if ctx.canLinkForced =>
          if (meta.isRefinable(varId) && !meta.occurs(varId, l2) && Level.geq(l2, k)) {
            val other = Level.addOffset(l2, -k)
            Some(meta.addLink(varId, other))
          } else None
        case _ => None
      }
    }

    private def tryLinkVar(v: Var, other: Value, meta: EqStore, ctx: Ctx): Result = {
      val m1 =
        if (!v.tpe.synDeps.intersects(meta.refinable) && defEq(other.tpe, v.tpe)) meta
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
     * Link one of two vars to the other. The choice of representative only has to be *deterministic* — both vars denote
     * the same value once linked — so the lower id wins. (A name-based preference for non-wildcard vars used to matter
     * when quotation had to find a representative in the env; it no longer does.)
     */
    private def tryLinkVarToPreferredRepresentative(v1: Var, v2: Var, meta: EqStore, ctx: Ctx): Result = {
      val (toLink, representative) = if (v1.id > v2.id) (v1, v2) else (v2, v1)
      tryLinkVar(toLink, representative, meta, ctx)
    }

    /**
     * A nullary constructor has two legal spellings — the bare `ConstructorHead` a global lookup yields, and the
     * `VCtor(h, [], _)` `evalRef` builds for one reached through source syntax. They denote the same value, so the
     * equation is decided on the constructor form and every rule below (no-confusion, key comparison) sees one shape.
     */
    private def constructorForm(value: Value): Value =
      value match {
        case h: ConstructorHead if h.totalArity == 0 => VCtor(h, Vector.empty, h.tpe)
        case other                                   => other
      }

    def tryUnify(v1: Value, v2: Value, meta: EqStore, ctx: Ctx): Result = {
      val a = constructorForm(ValueOps.materialize(v1, meta))
      val b = constructorForm(ValueOps.materialize(v2, meta))

      // Fast path. Identity and key equality decide the equation outright (docs/kernel.md#value-identity).
      // A key *mismatch* is only conclusive when both keys are complete AND nothing can link: a
      // refinable variable's key is its id, so two different ids may still denote the same value
      // once one links to the other, and no key mismatch survives that. When the keys are conclusive
      // the answer is `stuck` rather than `apart` — a key mismatch is a failure to derive `≡`, not
      // no-confusion evidence, and only the VCtor clash below produces the latter.
      if (sameValueObject(a, b)) return Right(meta)
      if (a.key == b.key) {
        if (keyAssertionsEnabled && !keyIsIdentity(a, b)) assertKeyVerdict(a, b, meta, ctx, keysEqual = true)
        return Right(meta)
      }
      if (
        meta.refinable.isEmpty && !keysAreInconclusive(a, b) && !mismatchRefutableAtHead(a, b, meta) &&
        !familyEquationMayRefute(a, b, ctx)
      ) {
        if (keyAssertionsEnabled) assertKeyVerdict(a, b, meta, ctx, keysEqual = false)
        return stuck(a, b)
      }
      structurally(a, b, meta, ctx)
    }

    /** Two values, compared by object identity. */
    private final class AssertedPair(val a: Value, val b: Value) {
      override def equals(obj: Any): Boolean =
        obj match {
          case other: AssertedPair => sameValueObject(a, other.a) && sameValueObject(b, other.b)
          case _                   => false
        }
      override def hashCode(): Int = 31 * System.identityHashCode(a) + System.identityHashCode(b)
    }

    /** An equation decided by a key, together with the frame and store in which it was decided. */
    private final class KeyVerdict(
        val a: Value,
        val b: Value,
        val meta: EqStore,
        val ctx: Ctx,
        val keysEqual: Boolean
    )

    /** The outermost assertion's iterative work stack and its identity-based de-duplication set. */
    private final class Assertion {
      val taken = new java.util.HashSet[AssertedPair]
      val pending = new java.util.ArrayDeque[KeyVerdict]

      def take(verdict: KeyVerdict): Unit =
        if (taken.add(new AssertedPair(verdict.a, verdict.b))) pending.push(verdict)
    }

    /** The running outermost assertion, or null when no key verdict is being checked. */
    private val runningAssertion = new ThreadLocal[Assertion]

    /**
     * The rules beneath a key verdict must reach it too, and each sub-equation the keys decide is asserted in turn.
     * Within one outermost assertion each pair of objects is checked once, so the check costs one structural pass
     * however much its values share, where rechecking every repeated pair would walk a shared value as a tree. Nested
     * key verdicts are queued instead of recursively checking their structure, so deeply nested equal values use a heap
     * work stack rather than the host call stack. A pair checked once is skipped even under another store or frame: the
     * verdict under test is its keys', which neither changes, and the assertion is a debug check.
     */
    private def assertKeyVerdict(a: Value, b: Value, meta: EqStore, ctx: Ctx, keysEqual: Boolean): Unit = {
      val verdict = new KeyVerdict(a, b, meta, ctx, keysEqual)
      val running = runningAssertion.get()
      if (running != null) running.take(verdict)
      else {
        val assertion = new Assertion
        runningAssertion.set(assertion)
        try {
          assertion.take(verdict)
          while (!assertion.pending.isEmpty) {
            val next = assertion.pending.pop()
            if (structurally(next.a, next.b, next.meta, next.ctx).isRight != next.keysEqual)
              wtf(
                s"ValueKey disagrees with conversion: keys ${if (next.keysEqual) "equal" else "differ"} but the " +
                  s"structural comparison ${if (next.keysEqual) "fails" else "succeeds"} for ${next.a} and ${next.b}"
              )
          }
        } finally runningAssertion.remove()
      }
    }

    /** The rules below the key fast path: decomposition, whose leaves are decided by the fast path again. */
    private def structurally(a: Value, b: Value, meta: EqStore, rootCtx: Ctx): Result = {
      val ctx = rootCtx.nested
      (a, b) match {
        // Proof structure supplies neither links nor apartness. Reduce to the proposition equation
        // before lambda extensionality, constructor no-confusion, application decomposition, or
        // Var linking can inspect the chosen representatives.
        case ProofEquation(t1, t2) => tryUnify(t1, t2, meta, ctx)

        // Grouping is part of the type's identity, so `tryUnifyPis` relates only Pis with the same
        // binder count: a curried `(a:A) -> (b:B) -> C` is not the uncurried `(a:A)(b:B) -> C`.
        case (p1: VPi, p2: VPi) =>
          tryUnifyPis(p1, p2, meta, ctx).map(_.eqStore)

        case (l1: VLam, l2: VLam) if sameLamId(l1.id, l2.id) => Right(meta)
        // Extensional comparison runs both bodies on the SAME shared vars, so each side must take
        // exactly that many arguments. `tryUnifyPis` enforces that, and its own group-for-group rule
        // is what makes the two lambdas' types comparable in the first place.
        case (l1: VLam, l2: VLam) =>
          // The id check failed - falling back to extensional unification. Body links at the
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

        // Different constructors of a genuine inductive are disjoint for data. Proof applications
        // were handled by ProofEquation above, whether erased or reconstructed. Heads without
        // no-confusion (e.g. Quot.mk) can still only be identified or separated by their theory.
        case (VCtor(h1, _, _), VCtor(h2, _, _)) if h1.name != h2.name =>
          if (constructorClashIsRefutable(a, b, meta, h1.noConfusion && h2.noConfusion)) apart(a, b)
          else stuck(a, b)

        // Deliberately NOT a refutation: different inductive family heads (bare or applied) are only
        // definitionally distinct. Propositional generativity is not assumed — propext can equate
        // Prop-valued families (And T T = Or T T), so head clashes fall through to stuck.

        case (v1: VApp, v2: VApp) if v1.args.length == v2.args.length =>
          // Data-family N1 and constructor injectivity hold beneath arbitrary structure. Prop-family
          // inversion is justified only for this equation when it is the match's root type comparison.
          // Other heads remain arbitrary functions, so their argument equations cannot produce links or refutations.
          val invertible = invertibleApplication(v1, rootCtx) && invertibleApplication(v2, rootCtx)
          val argCtx = if (invertible) ctx else ctx.enterNonInvertibleFrame
          def frame(failed: UnifyFailure): UnifyFailure = if (invertible) failed else failed.asStuck
          val headsUnified = (v1.head, v2.head) match {
            // A constructor head is its name. Through `tryUnify`, a nullary head would be put back into
            // constructor form: the very application being decomposed.
            case (h1: ConstructorHead, h2: ConstructorHead) if h1.name == h2.name => Right(meta)
            case (h1, h2)                                                         => tryUnify(h1, h2, meta, argCtx)
          }
          headsUnified match {
            case Left(failed) => Left(frame(failed))
            case Right(m0) =>
              var curMeta = m0
              // Stuck component equations are postponed and retried after the rest of the spine:
              // an equation like `max(u, v) ~ 1` has no forced solution on its own, but becomes
              // ground once a later argument solves its atoms. Postponement reorders work without
              // ever inventing values. Apart failures are rigid and fail immediately.
              val deferred = Vector.newBuilder[Postponed]
              val args = v1.args.zip(v2.args)
              val iter = args.iterator
              while (iter.hasNext) {
                val (arg1, arg2) = iter.next()
                tryUnify(arg1, arg2, curMeta, argCtx) match {
                  case Left(failed) if failed.apart => return Left(frame(failed))
                  case Left(failed)                 => deferred += Postponed(arg1, arg2, curMeta, failed)
                  case Right(next)                  => curMeta = next
                }
              }
              val postponed = deferred.result()
              // Equal values have equal types, so the type equation is a consequence: ctx is inherited.
              tryUnify(v1.tpe, v2.tpe, curMeta, ctx) match { // Important for constructors
                // A stuck type follows from the stuck arguments, and the last of them is reported: an implicit
                // argument is read off a later one, so the last is where the two applications were written apart.
                case Left(failed) if !failed.apart && postponed.nonEmpty =>
                  return Left(frame(postponed.last.failure))
                case Left(failed) => return Left(frame(failed))
                case Right(next)  => curMeta = next
              }
              val retryIter = postponed.iterator
              while (retryIter.hasNext) {
                val equation = retryIter.next()
                if (!equation.reachesLinksOf(curMeta)) return Left(frame(equation.failure))
                tryUnify(equation.v1, equation.v2, curMeta, argCtx) match {
                  case Left(_)     => return Left(frame(equation.failure))
                  case Right(next) => curMeta = next
                }
              }
              Right(curMeta)
          }

        // Same node: capture-wise thunk identity, which may also link. Otherwise — and whenever that
        // fails — compare the eliminators themselves, which identifies two distinct match programs
        // denoting the same stuck computation (a user-written selector against the canonical field
        // projection). That comparison is a congruence check under a non-invertible frame, so it can
        // only ever succeed or report stuck.
        case (v1: NeutralThunk, v2: NeutralThunk) =>
          val byId =
            if (v1.id.nodeId == v2.id.nodeId) tryUnifyNeutralThunks(v1, v2, meta, ctx)
            else stuck(v1, v2)
          byId match {
            case right: Right[_, _] => right
            case Left(_)            => tryUnifyNeutralMatches(v1, v2, meta, ctx)
          }

        // Level arithmetic failures are never refutations: an unsolvable constraint may still be satisfiable.
        case (l1: Level, l2: Level) =>
          unifyLevels(l1, l2, meta, ctx)
            .orElse(unifyLevels(l2, l1, meta, ctx))
            .map(Right(_))
            .getOrElse(stuck(l1, l2))

        case (s1: VSort, s2: VSort) if s1.isProp == s2.isProp => tryUnify(s1.level, s2.level, meta, ctx)

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

        // Structure eta: decompose fieldwise when one side is a constructor at an eta-eligible type,
        // or the type is fieldless (then both sides have fields — one by storage, the other
        // virtually — and unit-like values are equal outright). `Value.etaDecomposable` is the single
        // statement of which side makes the rule applicable; two neutrals at a struct type *with*
        // fields never decompose, because each virtual field captures its base.
        //
        // Placed after the Var cases on purpose — a refinable var must LINK to the constructor (match
        // refinement depends on `scrut := mk(fields)`). A refinable var at an eligible struct type
        // never reaches here: `EqStore.allowEta` expanded it when it became refinable, so what
        // remains is rigid. The frame is invertible (single constructor, no-confusion, non-Prop), so
        // links made inside are consequences and ctx passes through unchanged.
        case _ if Value.etaDecomposable(a) || Value.etaDecomposable(b) =>
          (StructEta.fields(a), StructEta.fields(b)) match {
            case (Some(fa), Some(fb)) if fa.length == fb.length =>
              var curMeta = meta
              val iter = fa.zip(fb).iterator
              while (iter.hasNext) {
                val (x, y) = iter.next()
                tryUnify(x, y, curMeta, ctx) match {
                  case Left(failed) => return Left(failed)
                  case Right(next)  => curMeta = next
                }
              }
              // Equal values have equal types: the type equation is a consequence, as for VApp.
              tryUnify(a.tpe, b.tpe, curMeta, ctx)
            case _ => stuck(a, b)
          }

        // No no-confusion evidence: unsolvable, but not refutable.
        case _ => stuck(a, b)
      }
    }
  }
}
