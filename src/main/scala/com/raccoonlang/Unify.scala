package com.raccoonlang

import com.raccoonlang.Interpreter._
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

  // Extensionally unify Pi types
  private def unifyPis(pi1: VPi, pi2: VPi, meta: EqStore)(implicit
      normalizers: NormalizerMap
  ): (EqStore, Vector[Var]) = {
    val (resMeta, nextEnv1, nextEnv2, vars) =
      pi1.binders.zip(pi2.binders).foldLeft((meta, pi1.env.newScope, pi2.env.newScope, Vector.empty[Var])) {
        case ((curMeta, curEnv1, curEnv2, curVars), (b1, b2)) =>
          val t1 = evalTerm(b1.ty, curEnv1)(curMeta)
          val t2 = evalTerm(b2.ty, curEnv2)(curMeta)
          val nextMeta = unify(t1, t2, curMeta)

          val x = FreshVar.freshVar(b1.name, t1)
          (nextMeta, curEnv1.putLocal(b1.name, x), curEnv2.putLocal(b2.name, x), curVars :+ x)
      }
    val out1 = evalTerm(pi1.out, nextEnv1)(resMeta)
    val out2 = evalTerm(pi2.out, nextEnv2)(resMeta)
    (unify(out1, out2, resMeta), vars)
  }

  def unifyStuckMatches(v1: VMatch, v2: VMatch, meta: EqStore)(implicit
      normalizers: NormalizerMap
  ): EqStore = {
    val m0 = unify(v1.scrut, v2.scrut, meta)
    val m1 = unify(v1.tpe, v2.tpe, m0)

    if (v1.id.params.length != v2.id.params.length) throw UnificationFailed(v1, v2) // Sanity check

    v1.id.params.zip(v2.id.params).foldLeft(m1) { case (curMeta, (p1, p2)) => unify(p1, p2, curMeta) }
  }

  def unify(v1: Value, v2: Value, meta: EqStore)(implicit normalizers: NormalizerMap): EqStore = {
    val normalizerF = TypeChecker.getNormalizerF(v1, v2)(meta, normalizers)

    val a = normalizerF(Interpreter.whnf(v1)(meta))
    val b = normalizerF(Interpreter.whnf(v2)(meta))

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

      case (v1: VMatch, v2: VMatch) if v1.id.nodeId == v2.id.nodeId =>
        unifyStuckMatches(v1, v2, meta)

      // Unify FreshVars through ctx. Basic idea: FreshVars can point at things through context
      // unify creates a ctx of pointers. We only create pointers from the top of the chain

      // Link unlinked Var (left) to a non-Var value
      case (Var(_, id, ty), other) =>
        if (!meta.isRefinable(id)) throw UnificationFailed(a, b)

        val m1 = unify(ty, other.tpe, meta)
        if (occurs(id, other, m1))
          throw OccursCheckFailed(id, other)
        m1.addLink(id, other)

      // Symmetric: link unlinked Var (right) to non-Var value
      case (other, Var(_, id, ty)) =>
        if (!meta.isRefinable(id)) throw UnificationFailed(a, b)

        val m1 = unify(ty, other.tpe, meta)
        if (occurs(id, other, m1))
          throw OccursCheckFailed(id, other)
        m1.addLink(id, other)

      case _ => throw UnificationFailed(v1, v2)
    }
  }
}
