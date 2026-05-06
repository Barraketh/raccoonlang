package com.raccoonlang

import com.raccoonlang.ElabAst.Term
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

import scala.collection.mutable

object InstanceSearch {
  private val MaxDepth = 256
  private val MaxNodes = 65536

  private final case class ResolvedGoal(key: ValueKey.Key, head: String)
  private final case class SearchResult(value: Value, term: Term)

  private final class SearchContext {
    private val cache = mutable.HashMap.empty[ValueKey.Key, SearchResult]

    def get(key: ValueKey.Key): Option[SearchResult] = cache.get(key)

    def put(key: ValueKey.Key, cached: SearchResult): Unit = cache.update(key, cached)
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
      success: Option[SearchResult],
      hasCycle: Boolean = false,
      hasBudgetExceeded: Boolean = false
  )

  def resultHeadKey(tpe: Value, eqStore: EqStore): Option[String] = {
    implicit val meta: EqStore = eqStore
    resultType(tpe).flatMap(headKey)
  }

  def instanceKey(name: String, value: Value, eqStore: EqStore): String = {
    validateInstanceType(name, value.tpe, eqStore)
    resultHeadKey(value.tpe, eqStore).getOrElse(throw InvalidInstance(name, value.tpe))
  }

  def solve(goal: Value, searchEnv: Env)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): BinderOps.CheckedArg = {
    val ctx = new SearchContext
    val res = solveInternal(goal, searchEnv, SearchState.empty, ctx)(
      eqStore.copy(refinable = DepSet.empty),
      normalizers
    )
    BinderOps.CheckedArg(res.value, res.term)
  }

  private def solveInternal(goal: Value, searchEnv: Env, state: SearchState, ctx: SearchContext)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): SearchResult = {
    val resolvedGoal = resolveGoal(goal)
    ctx.get(resolvedGoal.key) match {
      case Some(cached) => return cached
      case None         =>
    }

    val entered = state.enter(goal, resolvedGoal.key)

    val tiers = searchEnv.instanceSearchTiers(resolvedGoal.head)
    val local = tryCandidates(tiers.locals, goal, searchEnv, entered, ctx)
    local.success match {
      case Some(success) =>
        ctx.put(resolvedGoal.key, success)
        success
      case None =>
        val global = tryCandidates(tiers.globals, goal, searchEnv, entered, ctx)
        global.success match {
          case Some(success) =>
            ctx.put(resolvedGoal.key, success)
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
      candidates: Vector[InstanceCandidate],
      goal: Value,
      searchEnv: Env,
      state: SearchState,
      ctx: SearchContext
  )(implicit eqStore: EqStore, normalizers: NormalizerMap): CandidateSearch = {
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
      candidate: InstanceCandidate,
      goal: Value,
      searchEnv: Env,
      state: SearchState,
      ctx: SearchContext
  )(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): SearchResult = {
    Interpreter.resolveInEqStore(candidate.value.tpe) match {
      case pi: VPi =>
        val fresh = BinderOps.freshen(pi)
        val resultTy = pi.codomain(fresh.env, eqStore)
        val candidateEq = Unify.unify(resultTy, goal, eqStore.allow(fresh.newVars))
        val goals = fresh.vars.map(v => ValueOps.materialize(v.tpe, candidateEq))

        val (args, argTerms) = fillCandidateArgs(candidate, pi, goals, searchEnv, state, ctx)
        val res = Interpreter.evalApply(candidate.value, NEL.mk(args))
        val resTerm = Term.App(candidate.term, argTerms, candidate.term.span)
        SearchResult(res, resTerm)

      case resultTy =>
        Unify.unify(resultTy, goal, eqStore)
        SearchResult(candidate.value, candidate.term)
    }
  }

  private def fillCandidateArgs(
      candidate: InstanceCandidate,
      pi: VPi,
      goals: Vector[Value],
      initialSearchEnv: Env,
      state: SearchState,
      ctx: SearchContext
  )(implicit eqStore: EqStore, normalizerMap: NormalizerMap): (Vector[Value], Vector[Term]) = {
    val values = Vector.newBuilder[Value]
    val terms = Vector.newBuilder[Term]
    val binders = pi.binders.toVector

    var telescopeEnv = pi.env
    var idx = 0

    while (idx < binders.length) {
      val binder = binders(idx)
      val goal = goals(idx)
      val s = solveInternal(goal, initialSearchEnv, state, ctx)
      telescopeEnv = TypePatternOps.bindValue(telescopeEnv, binder, s.value)
      values += s.value
      terms += s.term
      idx += 1
    }

    val filledValues = values.result()
    if (filledValues.isEmpty) throw WTF(s"Instance candidate ${candidate.name} has empty telescope")
    (filledValues, terms.result())
  }

  private def resolveGoal(goal: Value)(implicit eqStore: EqStore): ResolvedGoal = {
    val resolved = Interpreter.resolveInEqStore(goal)
    ResolvedGoal(ValueKey.orderKey(resolved), headKeyResolved(resolved).getOrElse(throw NoInstanceFound(goal)))
  }

  private def resultType(tpe: Value)(implicit eqStore: EqStore): Option[Value] =
    Interpreter.resolveInEqStore(tpe) match {
      case pi: VPi =>
        val fresh = BinderOps.freshen(pi)
        Some(pi.codomain(fresh.env, eqStore))
      case other => Some(other)
    }

  private def validateInstanceType(name: String, tpe: Value, eqStore: EqStore): Unit = {
    implicit val meta: EqStore = eqStore
    Interpreter.resolveInEqStore(tpe) match {
      case pi: VPi =>
        pi.binders.toVector.find(!_.isDerived).foreach { binder =>
          throw InvalidInstance(name, tpe, s"function instance binder ${binder.name} must be derived")
        }
      case _ => ()
    }
  }

  private def headKey(value: Value)(implicit eqStore: EqStore): Option[String] =
    headKeyResolved(Interpreter.resolveInEqStore(value))

  private def headKeyResolved(value: Value): Option[String] = value match {
    case VApp(VConst(name, _, _), _, _) => Some(name)
    case VConst(name, _, _)             => Some(name)
    case _                              => None
  }

}
