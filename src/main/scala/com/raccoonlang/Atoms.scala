package com.raccoonlang

import com.raccoonlang.Value.{Lifetime, LifetimeTpe}

import scala.collection.mutable

/**
 * The atoms `scope` terms open (spec §4.1). An atom is unique to its `scope` term, identified by the term's node
 * identity: two `scope` terms are two atoms, and one term checked or evaluated any number of times is one atom.
 * Checking and evaluation share this registry, so both bind the variable of a `scope` to the same lifetime.
 *
 * An atom is an id in a lifetime's set, allocated by FreshVar like a variable's and named by its binder, but it is not
 * a variable: it is never refinable, so refinement never links it (spec §6.2), and nothing abstracts over it. Like
 * FreshVar, the registry assumes a single checking thread.
 */
object Atoms {
  private val byNode = mutable.HashMap.empty[AstNodeId, Lifetime]
  private var allocated: DepSet = DepSet.empty

  /** Every atom opened so far. Empty until the first `scope` term is checked, which is the confinement fast path. */
  def all: DepSet = allocated

  /** The lifetime holding exactly the atom of this `scope` term. */
  def of(scope: CoreAst.Term.Scope): Lifetime =
    byNode.getOrElseUpdate(
      scope.nodeId, {
        val (id, _) = FreshVar.freshValue(scope.ref.name, LifetimeTpe)
        allocated = allocated + id
        Lifetime.variable(id)
      }
    )
}
