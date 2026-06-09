package com.raccoonlang
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.collection.mutable

object InstanceSearch {
  private val MaxDepth = 256

  private final case class SearchState(stack: List[ValueKey.Key], depth: Int) {
    def enter(goal: Value, key: ValueKey.Key): SearchState = {
      if (stack.contains(key)) throw CyclicInstanceSearch(goal)
      if (depth >= MaxDepth) throw InstanceSearchBudgetExceeded(goal, MaxDepth)
      SearchState(key :: stack, depth + 1)
    }
  }

  private sealed trait SearchResult

  private object SearchResult {
    final case class Found(value: Value) extends SearchResult
    final case class Failed(hasCycle: Boolean, hitDepthLimit: Boolean) extends SearchResult

    val failed: Failed = Failed(false, false)
    val cycle: Failed = Failed(true, false)
    val depthLimit: Failed = Failed(false, true)

    def mergeFailures(a: Failed, b: Failed): Failed =
      Failed(a.hasCycle || b.hasCycle, a.hitDepthLimit || b.hitDepthLimit)
  }

  def resultHeadKey(tpe: Value): Option[String] = {
    val resultTy =
      tpe match {
        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          pi.codomain(freshEnv)
        case other => other
      }
    headKey(resultTy)
  }

  def instanceKey(name: String, value: Value): String =
    resultHeadKey(value.tpe).getOrElse(throw InvalidInstance(name, value.tpe))

  def solve(goal: Value, searchEnv: Env): Value = {
    val cache = mutable.HashMap.empty[ValueKey.Key, Value]
    solveInternal(goal, searchEnv, SearchState(Nil, 0), cache) match {
      case SearchResult.Found(value) => value
      case failed: SearchResult.Failed =>
        if (failed.hasCycle) throw CyclicInstanceSearch(goal)
        if (failed.hitDepthLimit) throw InstanceSearchBudgetExceeded(goal, MaxDepth)
        throw NoInstanceFound(goal)
    }
  }

  private def solveInternal(
      goal: Value,
      searchEnv: Env,
      state: SearchState,
      cache: mutable.HashMap[ValueKey.Key, Value]
  ): SearchResult = {
    val head = headKey(goal).getOrElse(return SearchResult.failed)
    val key = goal.key

    cache.get(key) match {
      case Some(cached) => return SearchResult.Found(cached)
      case None         =>
    }

    val entered =
      try state.enter(goal, key)
      catch {
        case _: CyclicInstanceSearch         => return SearchResult.cycle
        case _: InstanceSearchBudgetExceeded => return SearchResult.depthLimit
      }

    val tiers = searchEnv.instanceSearchTiers(head)
    val local = tryCandidates(tiers.locals, goal, searchEnv, entered, cache)
    local match {
      case SearchResult.Found(success) =>
        cache.update(key, success)
        local
      case localFailed: SearchResult.Failed =>
        val global = tryCandidates(tiers.globals, goal, searchEnv, entered, cache)
        global match {
          case SearchResult.Found(success) =>
            cache.update(key, success)
            global
          case globalFailed: SearchResult.Failed => SearchResult.mergeFailures(localFailed, globalFailed)
        }
    }
  }

  private def tryCandidates(
      candidates: Vector[Value],
      goal: Value,
      searchEnv: Env,
      state: SearchState,
      cache: mutable.HashMap[ValueKey.Key, Value]
  ): SearchResult = {
    var hasCycle = false
    var hitDepthLimit = false

    val iter = candidates.iterator
    while (iter.hasNext) {
      val candidate = iter.next()
      try {
        tryCandidate(candidate, goal, searchEnv, state, cache) match {
          case found: SearchResult.Found => return found
          case failed: SearchResult.Failed =>
            hasCycle ||= failed.hasCycle
            hitDepthLimit ||= failed.hitDepthLimit
        }
      } catch {
        case _: CyclicInstanceSearch         => hasCycle = true
        case _: InstanceSearchBudgetExceeded => hitDepthLimit = true
        case _: TypeMismatch | _: CannotApplyNonFunction | _: NoInstanceFound | _: InvalidInstance =>
          ()
      }
    }

    SearchResult.Failed(hasCycle, hitDepthLimit)
  }

  private def tryCandidate(
      candidate: Value,
      goal: Value,
      searchEnv: Env,
      state: SearchState,
      cache: mutable.HashMap[ValueKey.Key, Value]
  ): SearchResult = {
    candidate.tpe match {
      case pi: VPi =>
        val freshEnv = BinderOps.freshen(pi)
        val resultTy = pi.codomain(freshEnv)

        val candidateDeps = freshEnv.allDeps -- pi.env.allDeps
        val candidateEq =
          ValueEquivalence.tryUnify(resultTy, goal, EqStore.empty.allow(candidateDeps), searchEnv.normalizers) match {
            case Right(eqStore) => eqStore
            case Left(_)        => return SearchResult.failed
          }
        val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))

        val values = Vector.newBuilder[Value]
        val binders = pi.binders

        var idx = 0
        while (idx < binders.length) {
          val binder = binders(idx)
          val freshArg = freshArgs(idx)
          val inferred = ValueOps.materialize(freshArg, candidateEq)

          val arg =
            if (!inferred.synDeps.intersects(candidateDeps)) {
              inferred
            } else if (binder.isInstance) {
              val instanceGoal = ValueOps.materialize(freshArg.tpe, candidateEq)
              solveInternal(instanceGoal, searchEnv, state, cache) match {
                case SearchResult.Found(instance) => instance
                case failed: SearchResult.Failed  => return failed
              }
            } else {
              return SearchResult.failed
            }

          values += arg
          idx += 1
        }

        val args = values.result()
        SearchResult.Found(Interpreter.evalApply(candidate, args, searchEnv))

      case resultTy =>
        ValueEquivalence.tryUnify(resultTy, goal, EqStore.empty, searchEnv.normalizers) match {
          case Right(_) => SearchResult.Found(candidate)
          case Left(_)  => SearchResult.failed
        }
    }
  }

  private def headKey(value: Value): Option[String] =
    value match {
      case ConstSpine(head, _) => Some(head.name)
      case _                   => None
    }

}
