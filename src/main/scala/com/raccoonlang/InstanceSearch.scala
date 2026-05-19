package com.raccoonlang
import com.raccoonlang.Value._
import com.raccoonlang.telescope.{BinderOps, TypePatternOps}

import scala.collection.mutable

object InstanceSearch {
  private val MaxDepth = 256
  private val MaxNodes = 65536

  private final case class SearchResult(value: Value, term: ElabAst.Term)

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
    resultHeadKey(value.tpe, eqStore).getOrElse(throw InvalidInstance(name, value.tpe))
  }

  def solve(goal: Value, searchEnv: TypecheckEnv)(implicit
      eqStore: EqStore
  ): BinderOps.CheckedArg = {
    val ctx = new SearchContext
    val res = solveInternal(goal, searchEnv, SearchState.empty, ctx)(
      eqStore.copy(refinable = DepSet.empty)
    )
    BinderOps.CheckedArg(res.value, res.term)
  }

  private def solveInternal(goal: Value, searchEnv: TypecheckEnv, state: SearchState, ctx: SearchContext)(implicit
      eqStore: EqStore
  ): SearchResult = {
    val (head, key) = goal.use(rv => headKeyResolved(rv).getOrElse(throw NoInstanceFound(goal)) -> rv.value.key)

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
      candidates: Vector[InstanceCandidate],
      goal: Value,
      searchEnv: TypecheckEnv,
      state: SearchState,
      ctx: SearchContext
  )(implicit eqStore: EqStore): CandidateSearch = {
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
      searchEnv: TypecheckEnv,
      state: SearchState,
      ctx: SearchContext
  )(implicit
      eqStore: EqStore
  ): SearchResult = {
    candidate.value.tpe.caseOf {
      case pi: VPi =>
        val freshEnv = BinderOps.freshen(pi)
        val resultTy = pi.codomain(freshEnv, eqStore)

        val candidateDeps = freshEnv.allDeps -- pi.env.allDeps
        val candidateEq = ValueEquivalence.unify(resultTy, goal, eqStore.allow(candidateDeps), searchEnv.normalizers)
        val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))

        val values = Vector.newBuilder[Value]
        val terms = Vector.newBuilder[ElabAst.Term]
        val binders = pi.binders
        var telescopeEnv = pi.env
        var idx = 0

        while (idx < binders.length) {
          val binder = binders(idx)
          val freshArg = freshArgs(idx)
          val inferred = ValueOps.materialize(freshArg, candidateEq)

          val (arg, term) =
            if (!inferred.synDeps.intersects(candidateDeps)) {
              val term = ValueQuote.quoteTerm(inferred, searchEnv, candidate.term.span)(candidateEq)
              inferred -> term
            } else if (binder.isInstance) {
              val instanceGoal = ValueOps.materialize(freshArg.tpe, candidateEq)
              val solved = solveInternal(instanceGoal, searchEnv, state, ctx)
              solved.value -> solved.term
            } else {
              throw NoInstanceFound(goal)
            }

          telescopeEnv = TypePatternOps.bindValue(telescopeEnv, binder, arg)(candidateEq)
          values += arg
          terms += term
          idx += 1
        }

        val args = values.result()
        if (args.isEmpty) throw WTF(s"Instance candidate ${candidate.name} has empty telescope")
        val res = Interpreter.evalApply(candidate.value, args)
        val resTerm = ElabAst.Term.App(candidate.term, terms.result(), candidate.term.span)
        SearchResult(res, resTerm)

      case resultTy =>
        ValueEquivalence.unify(resultTy, goal, eqStore, searchEnv.normalizers)
        SearchResult(candidate.value, candidate.term)
    }
  }

  private def resultType(tpe: Value)(implicit eqStore: EqStore): Option[Value] =
    tpe.caseOf {
      case pi: VPi =>
        val freshEnv = BinderOps.freshen(pi)
        Some(pi.codomain(freshEnv, eqStore))
      case other => Some(other)
    }

  private def headKey(value: Value)(implicit eqStore: EqStore): Option[String] = value.use(headKeyResolved)

  private def headKeyResolved(value: ResolvedValue): Option[String] = value.caseOf {
    case VApp(VConst(name, _, _), _, _) => Some(name)
    case VConst(name, _, _)             => Some(name)
    case _                              => None
  }

}
