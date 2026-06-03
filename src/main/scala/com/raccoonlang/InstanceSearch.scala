package com.raccoonlang
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.collection.mutable

object InstanceSearch {
  private val MaxDepth = 256
  private val MaxNodes = 65536

  private final class SearchContext {
    private val cache = mutable.HashMap.empty[ValueKey.Key, Value]

    def get(key: ValueKey.Key): Option[Value] = cache.get(key)

    def put(key: ValueKey.Key, cached: Value): Unit = cache.update(key, cached)
  }

  private final case class SearchState(stack: List[ValueKey.Key], depth: Int, nodes: Int) {
    def enter(goal: Value, key: ValueKey.Key): SearchState = {
      if (stack.contains(key)) throw CyclicInstanceSearch(goal)
      if (depth >= MaxDepth || nodes >= MaxNodes) throw InstanceSearchBudgetExceeded(goal, MaxDepth, MaxNodes)
      SearchState(key :: stack, depth + 1, nodes + 1)
    }
  }

  private object SearchState {
    val empty: SearchState = SearchState(Nil, 0, 0)
  }

  private final case class CandidateSearch(
      success: Option[Value],
      hasCycle: Boolean = false,
      hasBudgetExceeded: Boolean = false
  )

  def resultHeadKey(tpe: Value): Option[String] =
    resultType(tpe).flatMap(headKey)

  def instanceKey(name: String, value: Value): String =
    resultHeadKey(value.tpe).getOrElse(throw InvalidInstance(name, value.tpe))

  def solve(goal: Value, searchEnv: Env): Value = {
    val ctx = new SearchContext
    solveInternal(goal, searchEnv, SearchState.empty, ctx)
  }

  private def solveInternal(goal: Value, searchEnv: Env, state: SearchState, ctx: SearchContext): Value = {
    val (head, key) = headKey(goal).getOrElse(throw NoInstanceFound(goal)) -> goal.key

    ctx.get(key) match {
      case Some(cached) => return cached
      case None         =>
    }

    val entered = state.enter(goal, key)

    val tiers = searchEnv.instanceSearchTiers(head)
    val local = tryCandidates(tiers.locals, goal, searchEnv, entered, ctx)
    local.success match {
      case Some(success) =>
        ctx.put(key, success)
        success
      case None =>
        val global = tryCandidates(tiers.globals, goal, searchEnv, entered, ctx)
        global.success match {
          case Some(success) =>
            ctx.put(key, success)
            success
          case None =>
            if (local.hasCycle || global.hasCycle) throw CyclicInstanceSearch(goal)
            if (local.hasBudgetExceeded || global.hasBudgetExceeded)
              throw InstanceSearchBudgetExceeded(goal, MaxDepth, MaxNodes)
            throw NoInstanceFound(goal)
        }
    }
  }

  private def tryCandidates(
      candidates: Vector[Value],
      goal: Value,
      searchEnv: Env,
      state: SearchState,
      ctx: SearchContext
  ): CandidateSearch = {
    var hasCycle = false
    var hasBudgetExceeded = false

    val iter = candidates.iterator
    while (iter.hasNext) {
      val candidate = iter.next()
      try {
        val result = tryCandidate(candidate, goal, searchEnv, state, ctx)
        return CandidateSearch(Some(result), hasCycle, hasBudgetExceeded)
      } catch {
        case _: CyclicInstanceSearch         => hasCycle = true
        case _: InstanceSearchBudgetExceeded => hasBudgetExceeded = true
        case _: UnificationFailed | _: OccursCheckFailed | _: TypeMismatch | _: CannotApplyNonFunction |
            _: NoInstanceFound | _: InvalidInstance =>
          ()
      }
    }

    CandidateSearch(None, hasCycle, hasBudgetExceeded)
  }

  private def tryCandidate(
      candidate: Value,
      goal: Value,
      searchEnv: Env,
      state: SearchState,
      ctx: SearchContext
  ): Value = {
    candidate.tpe match {
      case pi: VPi =>
        val freshEnv = BinderOps.freshen(pi)
        val resultTy = pi.codomain(freshEnv)

        val candidateDeps = freshEnv.allDeps -- pi.env.allDeps
        val candidateEq =
          ValueEquivalence.unify(resultTy, goal, EqStore.empty.allow(candidateDeps), searchEnv.normalizers)
        val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))

        val values = Vector.newBuilder[Value]
        val binders = pi.binders

        binders.indices.foreach { idx =>
          val binder = binders(idx)
          val freshArg = freshArgs(idx)
          val inferred = ValueOps.materialize(freshArg, candidateEq)

          val arg =
            if (!inferred.synDeps.intersects(candidateDeps)) {
              inferred
            } else if (binder.isInstance) {
              val instanceGoal = ValueOps.materialize(freshArg.tpe, candidateEq)
              solveInternal(instanceGoal, searchEnv, state, ctx)
            } else {
              throw NoInstanceFound(goal)
            }

          values += arg
        }

        val args = values.result()
        Interpreter.evalApply(candidate, args)

      case resultTy =>
        ValueEquivalence.unify(resultTy, goal, EqStore.empty, searchEnv.normalizers)
        candidate
    }
  }

  private def resultType(tpe: Value): Option[Value] =
    tpe match {
      case pi: VPi =>
        val freshEnv = BinderOps.freshen(pi)
        Some(pi.codomain(freshEnv))
      case other => Some(other)
    }

  private def headKey(value: Value): Option[String] =
    value match {
      case ConstSpine(head, _) => Some(head.name)
      case _                   => None
    }

}
