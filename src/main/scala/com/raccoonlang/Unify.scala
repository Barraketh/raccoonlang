package com.raccoonlang

import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

import scala.collection.immutable.BitSet

object Unify {

  def expandedDeps(rhsSyn: BitSet, meta: EqStore): BitSet = {
    val seen = scala.collection.mutable.BitSet.empty
    val work = scala.collection.mutable.ArrayDeque.empty[Int]
    rhsSyn.foreach(id => { val r = id; if (!seen(r)) { seen += r; work += r } })

    while (work.nonEmpty) {
      val id = work.removeHead()
      meta.links.get(id) match {
        case None => ()
        case Some(sol) =>
          sol.synDeps.foreach { j =>
            if (!seen(j)) { seen += j; work += j }
          }
      }
    }
    seen.toImmutable
  }

  def occurs(id: VarId, rhs: Value, meta: EqStore): Boolean =
    expandedDeps(rhs.synDeps, meta).contains(id)

  private def unifyPis(pi1: VPi, pi2: VPi, eqStore: EqStore)(implicit
      normalizers: NormalizerMap
  ): (EqStore, Vector[Var]) = {
    val related = TypeChecker.relatePis(pi1, pi2)(eqStore, normalizers)
    val nextEqStore = unify(related.out1, related.out2, related.eqStore)
    (nextEqStore, related.vars)
  }

  private def unifyStuckMatches(v1: VMatch, v2: VMatch, meta: EqStore)(implicit
      normalizers: NormalizerMap
  ): EqStore = {
    val m0 = unify(v1.scrut, v2.scrut, meta)
    val m1 = unify(v1.tpe, v2.tpe, m0)

    if (v1.id.params.length != v2.id.params.length) throw UnificationFailed(v1, v2) // Sanity check

    v1.id.params.zip(v2.id.params).foldLeft(m1) { case (curMeta, (p1, p2)) => unify(p1, p2, curMeta) }
  }

  private def unifyLevels(l1: Level, l2: Level, meta: EqStore): Option[EqStore] = {
    if (l1.atoms.size == 1 && l1.c == 0) {
      val (varId, k) = l1.atoms.head
      if (
        meta.isRefinable(varId) && !occurs(varId, l2, meta)
        && l2.atoms.values.forall(k2 => k2 >= k) // For now make sure that offsets don't go negative
        && (l2.c >= k || (l2.c == 0 && l2.atoms.nonEmpty))
      ) {
        val other = Level.addOffset(l2, -k)
        Some(meta.addLink(varId, other))
      } else None
    } else None
  }

  private def unifySorts(v1: VSort, v2: VSort, meta: EqStore): EqStore = {
    // Broad idea: we can unify (v + k) = other as v = other - k.  Everything else fails.
    val l1 = Interpreter.resolveInEqStore(v1.level)(meta)
    val l2 = Interpreter.resolveInEqStore(v2.level)(meta)

    (l1, l2) match {
      case (l1: Level, l2: Level) =>
        unifyLevels(l1, l2, meta).orElse(unifyLevels(l2, l1, meta)).getOrElse {
          throw UnificationFailed(l1, l2)
        }
      case _ => throw UnificationFailed(l1, l2)
    }

  }

  private def linkVar(v: Var, other: Value, meta: EqStore)(implicit normlizers: NormalizerMap): EqStore = {
    val m1 = if (TypeChecker.sortLeq(other.tpe, v.tpe)(meta)) meta else unify(v.tpe, other.tpe, meta)
    if (occurs(v.id, other, m1))
      throw OccursCheckFailed(v.id, other)
    m1.addLink(v.id, other)
  }

  def unify(v1: Value, v2: Value, meta: EqStore)(implicit normalizers: NormalizerMap): EqStore = {
    val normalizerF = TypeChecker.getNormalizerF(v1, v2)(meta, normalizers)

    val a = normalizerF(Interpreter.resolveInEqStore(v1)(meta))
    val b = normalizerF(Interpreter.resolveInEqStore(v2)(meta))

    if (TypeChecker.defEq(a, b)(meta, normalizers)) return meta

    (a, b) match {

      case (p1: VPi, p2: VPi) if p1.binders.length == p2.binders.length           => unifyPis(p1, p2, meta)._1
      case (l1: VLam, l2: VLam) if l1.tpe.binders.length == l2.tpe.binders.length =>
        // We know that the id check failed - falling back to extensional unification
        val (nextMeta, newVars) = unifyPis(l1.tpe, l2.tpe, meta)
        val varsNEL = NEL.mk(newVars)
        val res1 = l1.run(varsNEL, nextMeta)
        val res2 = l2.run(varsNEL, nextMeta)
        unify(res1, res2, nextMeta)
      case (v1: AppliedValue, v2: AppliedValue) if v1.args.length == v2.args.length =>
        val startCtx = unify(v1.head, v2.head, meta)
        v1.args.zip(v2.args).foldLeft(startCtx) { case (newCtx, (arg1, arg2)) => unify(arg1, arg2, newCtx) }

      case (c1: VCtor, c2: VCtor) if c1.fields.length == c2.fields.length =>
        val m0 = unify(c1.head, c2.head, meta)
        val m1 = c1.fields.zip(c2.fields).foldLeft(m0) { case (cur, (x, y)) => unify(x, y, cur) }
        unify(c1.tpe, c2.tpe, m1)

      case (v1: VMatch, v2: VMatch) if v1.id.nodeId == v2.id.nodeId =>
        unifyStuckMatches(v1, v2, meta)

      case (s1: VSort, s2: VSort) => unifySorts(s1, s2, meta)

      // Unify FreshVars through ctx. Basic idea: FreshVars can point at things through context
      // unify creates a ctx of pointers. We only create pointers from the top of the chain

      // Link unlinked Var (left) to a non-Var value
      case (v: Var, other) if meta.isRefinable(v.id) => linkVar(v, other, meta)

      // Symmetric: link unlinked Var (right) to non-Var value
      case (other, v: Var) if meta.isRefinable(v.id) => linkVar(v, other, meta)

      case _ => throw UnificationFailed(v1, v2)
    }
  }
}
