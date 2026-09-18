package com.raccoonlang

import com.raccoonlang.Value._

import scala.util.control.NonFatal

/** Definitional equality and consequence-preserving unification for the currently available value forms. */
object ValueEquivalence {
  final case class UnifyFailure(v1: Value, v2: Value, apart: Boolean = false) {
    def asStuck: UnifyFailure = if (apart) copy(apart = false) else this
  }

  final case class Ctx(invertibleFrame: Boolean = true) {
    def canLinkForced: Boolean = invertibleFrame
    def enterNonInvertibleFrame: Ctx = if (invertibleFrame) copy(invertibleFrame = false) else this
  }

  def defEq(left: Value, right: Value): Boolean = tryUnify(left, right, EqStore.empty).isRight

  def tryUnify(left: Value, right: Value, store: EqStore): Either[UnifyFailure, EqStore] =
    unify(left, right, store, Ctx())

  private def stuck(left: Value, right: Value): Left[UnifyFailure, EqStore] =
    Left(UnifyFailure(left, right))

  private def apart(left: Value, right: Value): Left[UnifyFailure, EqStore] =
    Left(UnifyFailure(left, right, apart = true))

  private def constructorForm(value: Value): Value = value match {
    case head: ConstructorHead if head.totalArity == 0 => VCtor(head, Vector.empty, head.tpe)
    case other                                         => other
  }

  private def definitionallyInjectiveHead(head: Value): Boolean = head match {
    case h: ConstructorHead         => h.noConfusion
    case VConst(_, Inductive(_), _) => true
    case _                          => false
  }

  /** Eta can decompose a constructor (or any fieldless eligible value), but never two fieldful neutrals. */
  private def etaDecomposable(value: Value): Boolean =
    StructEta.eligibleInstance(value.tpe).exists { case (_, info) =>
      info.fieldCount == 0 || ConstructorForm.unapply(value).nonEmpty
    }

  private object ProofEquation {
    def unapply(pair: (Value, Value)): Option[(Value, Value)] = pair match {
      case (left, right) if Value.isPropositionType(left.tpe) && Value.isPropositionType(right.tpe) =>
        Some(left.tpe -> right.tpe)
      case _ => None
    }
  }

  private def unify(left0: Value, right0: Value, store: EqStore, ctx: Ctx): Either[UnifyFailure, EqStore] =
    unify(left0, right0, store, ctx, normalizeNullary = true)

  private def unify(
      left0: Value,
      right0: Value,
      store: EqStore,
      ctx: Ctx,
      normalizeNullary: Boolean
  ): Either[UnifyFailure, EqStore] = {
    val materializedLeft = ValueOps.materialize(left0, store)
    val materializedRight = ValueOps.materialize(right0, store)
    val left = if (normalizeNullary) constructorForm(materializedLeft) else materializedLeft
    val right = if (normalizeNullary) constructorForm(materializedRight) else materializedRight
    if (left.asInstanceOf[AnyRef] eq right.asInstanceOf[AnyRef]) Right(store)
    else if (!left.needsStructuralDefEq && !right.needsStructuralDefEq && left.key == right.key)
      Right(store)
    else if (store.refinable.isEmpty && !left.needsStructuralDefEq && !right.needsStructuralDefEq)
      stuck(left, right)
    else {
      (left, right) match {
        // Proof irrelevance is type-directed and must precede every Var rule: proof representatives
        // supply neither witness links nor constructor apartness.
        case ProofEquation(leftType, rightType)         => unify(leftType, rightType, store, ctx)
        case (lv: Var, rv: Var) if lv.id == rv.id       => unify(lv.tpe, rv.tpe, store, ctx)
        case (v: Var, other) if store.isRefinable(v.id) => link(v, other, store, ctx)
        case (other, v: Var) if store.isRefinable(v.id) => link(v, other, store, ctx)
        // Levels occur both directly (e.g. a builtin result) and underneath
        // VSort.  Keep this case separate so direct level equations get the
        // same forced-offset solving as sort equations.
        case (l1: Level, l2: Level) => unifyLevels(l1, l2, store, ctx)
        case (VSort(a), VSort(b))   => unifyLevels(a, b, store, ctx)
        case (VConst(ln, lk, lt), VConst(rn, rk, rt)) if ln == rn && lk == rk =>
          unify(lt, rt, store, ctx)
        case (lp: VPi, rp: VPi)   => unifyPis(lp, rp, store, ctx)
        case (ll: VLam, rr: VLam) => unifyLambdas(ll, rr, store, ctx)
        case (leftThunk: NeutralThunk, rightThunk: NeutralThunk) =>
          unifyThunks(leftThunk, rightThunk, store, ctx)
        case (leftHead: ConstructorHead, rightHead: ConstructorHead)
            if leftHead.name == rightHead.name &&
              leftHead.numErasedFamilyArgs == rightHead.numErasedFamilyArgs &&
              leftHead.totalArity == rightHead.totalArity =>
          unify(leftHead.tpe, rightHead.tpe, store, ctx)
        case (leftHead: ConstructorHead, rightHead: ConstructorHead) if leftHead.name != rightHead.name =>
          stuck(leftHead, rightHead)
        case (leftApp: VApp, rightApp: VApp) =>
          unifyApps(leftApp, rightApp, store, ctx)
        case _ if etaDecomposable(left) || etaDecomposable(right) =>
          (StructEta.fields(left), StructEta.fields(right)) match {
            case (Some(lfields), Some(rfields)) if lfields.length == rfields.length =>
              lfields
                .zip(rfields)
                .foldLeft[Either[UnifyFailure, EqStore]](Right(store)) {
                  case (Right(current), (l, r)) => unify(l, r, current, ctx)
                  case (failed @ Left(_), _)    => failed
                }
                .flatMap(next => unify(left.tpe, right.tpe, next, ctx))
            case _ => stuck(left, right)
          }
        case _ => stuck(left, right)
      }
    }
  }

  private def unifyLevels(left: Level, right: Level, store: EqStore, ctx: Ctx): Either[UnifyFailure, EqStore] = {
    if (left == right) Right(store)
    else {
      def solve(variable: VarId, offset: Int, other: Level): Either[UnifyFailure, EqStore] =
        if (ctx.canLinkForced && store.isRefinable(variable) && Level.geq(other, offset)) {
          val candidate = Level.addOffset(other, -offset)
          if (store.occurs(variable, candidate)) stuck(VSort(left), VSort(right))
          else Right(store.addLink(variable, candidate))
        } else stuck(VSort(left), VSort(right))
      Level
        .singleVariableOffset(left)
        .map { case (id, k) => solve(id, k, right) }
        .orElse(Level.singleVariableOffset(right).map { case (id, k) => solve(id, k, left) })
        .getOrElse(stuck(VSort(left), VSort(right)))
    }
  }

  private def unifyApps(left: VApp, right: VApp, store: EqStore, ctx: Ctx): Either[UnifyFailure, EqStore] = {
    (left.head, right.head) match {
      case (a: ConstructorHead, b: ConstructorHead) if a.name != b.name && a.noConfusion && b.noConfusion =>
        return apart(left, right)
      case _ =>
    }
    if (left.args.length != right.args.length) return stuck(left, right)
    val invertible = definitionallyInjectiveHead(left.head) && definitionallyInjectiveHead(right.head)
    val argCtx = if (invertible) ctx else ctx.enterNonInvertibleFrame
    val frame: UnifyFailure => UnifyFailure = if (invertible) identity else _.asStuck
    unify(left.head, right.head, store, argCtx, normalizeNullary = false) match {
      case Left(failure) => Left(frame(failure))
      case Right(headStore) =>
        var current = headStore
        var apartFailure: Option[UnifyFailure] = None
        val deferred = Vector.newBuilder[(Value, Value)]
        left.args.zip(right.args).foreach { case (leftArg, rightArg) =>
          if (current != null) {
            unify(leftArg, rightArg, current, argCtx) match {
              case Right(next)                    => current = next
              case Left(failure) if failure.apart => apartFailure = Some(failure); current = null
              case Left(_)                        => deferred += leftArg -> rightArg
            }
          }
        }
        if (current == null) Left(frame(apartFailure.get))
        else {
          unify(left.tpe, right.tpe, current, ctx) match {
            case Left(failure) => Left(frame(failure))
            case Right(next) =>
              deferred.result().foldLeft[Either[UnifyFailure, EqStore]](Right(next)) {
                case (Right(existing), (a, b)) => unify(a, b, existing, argCtx).left.map(frame)
                case (failed @ Left(_), _)     => failed
              }
          }
        }
    }
  }

  private def link(variable: Var, other: Value, store: EqStore, ctx: Ctx): Either[UnifyFailure, EqStore] = {
    if (!ctx.canLinkForced) stuck(variable, other)
    else {
      val result = for {
        typed <- unify(variable.tpe, other.tpe, store, ctx)
        candidate = ValueOps.materialize(other, typed)
        next <-
          if (typed.occurs(variable.id, candidate)) Left(UnifyFailure(variable, other))
          else Right(typed)
      } yield next
      result.map { typed =>
        other match {
          case otherVar: Var if typed.isRefinable(otherVar.id) && otherVar.id < variable.id =>
            typed.addLink(variable.id, otherVar)
          case otherVar: Var if typed.isRefinable(otherVar.id) =>
            typed.addLink(otherVar.id, variable)
          case _ => typed.addLink(variable.id, ValueOps.materialize(other, typed))
        }
      }
    }
  }

  private def unifyPis(left: VPi, right: VPi, store: EqStore, ctx: Ctx): Either[UnifyFailure, EqStore] = {
    if (
      left.binders.length != right.binders.length || left.binders.map(_.isImplicit) != right.binders.map(_.isImplicit)
    )
      stuck(left, right)
    else {
      val inner = ctx.enterNonInvertibleFrame
      var current = store
      var leftEnv = left.env
      var rightEnv = right.env
      val watermark = FreshVar.currentId
      var failed: Option[UnifyFailure] = None
      left.binders.zip(right.binders).foreach { case (lb, rb) =>
        if (failed.isEmpty) {
          unify(Interpreter.evalTerm(lb.ty, leftEnv), Interpreter.evalTerm(rb.ty, rightEnv), current, inner) match {
            case Left(error) => failed = Some(error.asStuck)
            case Right(next) =>
              current = next
              val sharedType = ValueOps.materialize(Interpreter.evalTerm(lb.ty, leftEnv), current)
              val shared = Value.canonicalizeRigidBinder(sharedType, FreshVar.freshVar(lb.name, sharedType))
              leftEnv = leftEnv.putLocal(lb.localRef, shared)
              rightEnv = rightEnv.putLocal(rb.localRef, shared)
          }
        }
      }
      failed match {
        case Some(error) => Left(error)
        case None =>
          unify(left.codomain(leftEnv), right.codomain(rightEnv), current, inner).flatMap { next =>
            val escaped = next.subst.exists { case (id, solution) =>
              !store.subst.contains(id) && solution.synDeps.nonEmpty && solution.synDeps.max > watermark
            }
            if (escaped) stuck(left, right) else Right(next)
          }
      }
    }
  }

  private def unifyLambdas(left: VLam, right: VLam, store: EqStore, ctx: Ctx): Either[UnifyFailure, EqStore] =
    (left.body, right.body) match {
      case (LamBody.Core(lt, le), LamBody.Core(rt, re)) =>
        if (sameLambdaId(left.id, right.id)) Right(store)
        else
          alignLambdaPis(left.tpe, right.tpe, store, ctx, le, re).flatMap { case (next, leftEnv, rightEnv, watermark) =>
            unify(Interpreter.evalTerm(lt.body, leftEnv), Interpreter.evalTerm(rt.body, rightEnv), next, ctx).left
              .map(_.asStuck)
              .flatMap { result =>
                val escaped = result.subst.exists { case (id, solution) =>
                  !store.subst.contains(id) && solution.synDeps.nonEmpty && solution.synDeps.max > watermark
                }
                if (escaped) stuck(left, right) else Right(result)
              }
          }
      case (LamBody.Native(_, _, _), LamBody.Native(_, _, _)) if sameLambdaId(left.id, right.id) => Right(store)
      case (LamBody.ProofEta, LamBody.ProofEta) => unify(left.tpe, right.tpe, store, ctx)
      case _                                    => stuck(left, right)
    }

  private def alignLambdaPis(
      left: VPi,
      right: VPi,
      store: EqStore,
      ctx: Ctx,
      leftBase: Env,
      rightBase: Env
  ): Either[UnifyFailure, (EqStore, Env, Env, Value.VarId)] = {
    if (
      left.binders.length != right.binders.length || left.binders.map(_.isImplicit) != right.binders.map(_.isImplicit)
    )
      return Left(UnifyFailure(left, right))
    val inner = ctx.enterNonInvertibleFrame
    val watermark = FreshVar.currentId
    var current = store
    var leftEnv = leftBase
    var rightEnv = rightBase
    left.binders.zip(right.binders).foreach { case (lb, rb) =>
      unify(Interpreter.evalTerm(lb.ty, leftEnv), Interpreter.evalTerm(rb.ty, rightEnv), current, inner) match {
        case Left(error) => return Left(error.asStuck)
        case Right(next) =>
          current = next
          val sharedType = Interpreter.evalTerm(lb.ty, leftEnv)
          val shared = Value.canonicalizeRigidBinder(sharedType, FreshVar.freshVar(lb.name, sharedType))
          leftEnv = leftEnv.putLocal(lb.localRef, shared)
          rightEnv = rightEnv.putLocal(rb.localRef, shared)
      }
    }
    unify(left.codomain(leftEnv), right.codomain(rightEnv), current, inner)
      .map(next => (next, leftEnv, rightEnv, watermark))
  }

  private def sameLambdaId(left: ValueId, right: ValueId): Boolean = (left, right) match {
    case (ValueId.Const(a), ValueId.Const(b)) => a == b
    case (ValueId.LocalId(ln, lc), ValueId.LocalId(rn, rc)) if ln == rn && lc.length == rc.length =>
      lc.zip(rc).forall { case (a, b) => defEq(a, b) }
    case _ => false
  }

  private def unifyThunks(
      left: NeutralThunk,
      right: NeutralThunk,
      store: EqStore,
      ctx: Ctx
  ): Either[UnifyFailure, EqStore] = {
    if (left.id.nodeId == right.id.nodeId && left.id.captures.length == right.id.captures.length) {
      val inner = ctx.enterNonInvertibleFrame
      val direct = unify(left.tpe, right.tpe, store, ctx).flatMap { typed =>
        left.id.captures.zip(right.id.captures).foldLeft[Either[UnifyFailure, EqStore]](Right(typed)) {
          case (Right(current), (a, b)) => unify(a, b, current, inner).left.map(_.asStuck)
          case (failed @ Left(_), _)    => failed
        }
      }
      direct match {
        case success @ Right(_) => success
        case Left(_)            => tryUnifyNeutralMatches(left, right, store, ctx)
      }
    } else tryUnifyNeutralMatches(left, right, store, ctx)
  }

  private val neutralComparisonDepth = new ThreadLocal[Int] {
    override def initialValue(): Int = 0
  }

  private def tryUnifyNeutralMatches(
      left: NeutralThunk,
      right: NeutralThunk,
      store: EqStore,
      ctx: Ctx
  ): Either[UnifyFailure, EqStore] = {
    val depth = neutralComparisonDepth.get()
    if (depth >= 16) return stuck(left, right)
    neutralComparisonDepth.set(depth + 1)
    try {
      val inner = ctx.enterNonInvertibleFrame
      val leftScrut = Interpreter.evalTerm(left.term.scrut, left.env)
      val rightScrut = Interpreter.evalTerm(right.term.scrut, right.env)
      val sameShape = left.term.cases.length == right.term.cases.length &&
        left.term.cases.zip(right.term.cases).forall { case (a, b) =>
          a.ctorName == b.ctorName && a.argRefs.length == b.argRefs.length
        }
      if (!sameShape) stuck(left, right)
      else {
        var current = store
        def step(a: Value, b: Value): Boolean = unify(a, b, current, inner) match {
          case Right(next) => current = next; true
          case Left(_)     => false
        }
        if (!step(left.tpe, right.tpe) || !step(leftScrut, rightScrut)) stuck(left, right)
        else {
          val agreed = left.term.cases.zip(right.term.cases).forall { case (lc, rc) =>
            left.env(lc.ctorName) match {
              case head: ConstructorHead =>
                val (args, result) = com.raccoonlang.telescope.BinderOps.freshCtorArgsAndResult(head)
                val fields = constructorStoredArgs(head, args)
                step(result, leftScrut.tpe) && step(result, rightScrut.tpe) &&
                step(Interpreter.evalBranch(lc, fields, left.env), Interpreter.evalBranch(rc, fields, right.env))
              case _ => false
            }
          }
          if (agreed) Right(current) else stuck(left, right)
        }
      }
    } catch { case NonFatal(_) => stuck(left, right) }
    finally {
      if (depth == 0) neutralComparisonDepth.remove() else neutralComparisonDepth.set(depth)
    }
  }

  def whnf(value: Value): Value = value match {
    case VApp(fn, args, tpe, blocked) =>
      whnf(fn) match {
        case lambda: VLam => whnf(Interpreter.evalApply(lambda, args))
        case head => if (head.asInstanceOf[AnyRef] eq fn.asInstanceOf[AnyRef]) value else VApp(head, args, tpe, blocked)
      }
    case other => other
  }
}
