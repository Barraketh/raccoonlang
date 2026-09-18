package com.raccoonlang

import com.raccoonlang.Value.VarId

// Tracks equalities between variables through substitution
final case class EqStore(subst: Map[VarId, Value], refinable: DepSet) {
  @annotation.tailrec
  def force(v: Value): Value = v match {
    case Value.Var(_, id, _) =>
      subst.get(id) match {
        case Some(v) => force(v)
        case None    => v
      }
    case other => other
  }

  def isRefinable(id: VarId): Boolean = refinable.contains(id)

  def allow(ids: DepSet): EqStore = copy(refinable = refinable ++ ids)

  /**
   * Make `ids` refinable, expanding structure eta at the boundary. This is the one entry point through which match
   * refinement admits variables, and it establishes the invariant:
   *
   * *the store never contains an unsolved refinable variable at an eta-eligible struct type.*
   *
   * Every such variable is linked here, at once, to its own constructor applied to fresh field variables, and those
   * fields are admitted the same way — a field may itself stand at an eligible struct type, so the expansion is
   * recursive. Structure eta is what makes each link a consequence rather than a choice: `v` and `mk(v.0, …, v.n)` are
   * the same value, so the link records an identity, and every link made under it afterwards stays forced.
   *
   * Stating the expansion here rather than inside unification means an equation blocked on a struct variable — a
   * projection of a match scrutinee, say — never has to search for the variable to expand: by the time any equation is
   * presented, no such variable is left unsolved.
   *
   * `ids` is what becomes refinable and is the authority on that; `vars` supplies the `Var` objects for deciding which
   * of them stand at an eligible struct type. The two are not interchangeable: a level parameter occurs in `synDeps`
   * without any `Var` to recover, so passing only the variables found would silently narrow refinability.
   */
  def allowEta(ids: DepSet, vars: Vector[Value.Var]): EqStore = {
    var store = allow(ids)
    var frontier = vars
    while (frontier.nonEmpty) {
      val next = Vector.newBuilder[Value.Var]
      frontier.foreach { v =>
        if (store.refinable.contains(v.id) && !store.subst.contains(v.id)) {
          StructEta.eligibleInstance(v.tpe).foreach { case (inst, info) =>
            val head = info.ctorHead
            val fieldEnv = telescope.BinderOps.freshen(head.fieldBinders, head.fieldEnv(inst.args))
            val fields = head.fieldBinders.map(binder => fieldEnv(binder.localRef))
            val witness = Value.VCtor(head, fields, v.tpe)
            // The fresh fields stand for `v`'s own fields and must be as refinable as `v` was, or
            // linking `v` would leave later equations less solvable than before.
            store = store.allow(witness.synDeps).addLink(v.id, witness)
            fields.foreach {
              case field: Value.Var => next += field
              case _                =>
            }
          }
        }
      }
      frontier = next.result()
    }
    store
  }

  def addLink(id: VarId, v: Value): EqStore = {
    if (subst.contains(id)) throw VarAlreadyLinked(id)
    if (!refinable.contains(id)) throw WTF("Tried to solve a var not in refinable set")
    copy(subst = subst + (id -> v))
  }

  def occurs(id: VarId, in: Value): Boolean = transitiveDeps(in).contains(id)

  lazy val solvedIds: DepSet = DepSet.from(subst.keySet)

  private def transitiveDeps(v: Value): DepSet = {
    val seen = DepSet.newBuilder(v.synDeps)
    var frontier = v.synDeps

    while (frontier.nonEmpty) {
      val toExpand = frontier & solvedIds
      val next = DepSet.newBuilder

      toExpand.foreach { id =>
        next.unionInPlace(subst(id).synDeps)
      }

      next.diffInPlace(seen)
      if (next.isEmpty) return seen.result()

      seen.unionInPlace(next)
      frontier = next.result()
    }

    seen.result()
  }

}

object EqStore {
  val empty: EqStore = EqStore(Map(), DepSet.empty)
}
