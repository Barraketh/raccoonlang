package com.raccoonlang

import com.raccoonlang.Interpreter._

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
  private def unifyPis(pi1: VPi, pi2: VPi, meta: EqStore, rigid: Set[VarId]): (EqStore, Env, Env, Set[VarId]) = {
    val (resMeta, nextEnv1, nextEnv2, nextRigid) =
      pi1.binders.zip(pi2.binders).foldLeft((meta, pi1.env.newScope, pi2.env.newScope, rigid)) {
        case ((curMeta, curEnv1, curEnv2, curRigid), (b1, b2)) =>
          val t1 = evalTerm(b1.ty, curEnv1)(curMeta)
          val t2 = evalTerm(b2.ty, curEnv2)(curMeta)
          val nextMeta = unify(t1, t2, curMeta, curRigid)

          val x = FreshVar.freshVar(b1.name, t1)
          (nextMeta, curEnv1.putLocal(b1.name, x), curEnv2.putLocal(b2.name, x), curRigid + x.id)
      }
    val out1 = evalTerm(pi1.out, nextEnv1)(resMeta)
    val out2 = evalTerm(pi2.out, nextEnv2)(resMeta)
    (unify(out1, out2, resMeta, nextRigid), nextEnv1, nextEnv2, nextRigid)
  }

  def unifyStuckMatches(v1: StuckMatch, v2: StuckMatch, meta: EqStore, rigid: Set[VarId]): EqStore = {
    val m0 = unify(v1.scrut, v2.scrut, meta, rigid)
    val m1 = unify(v1.tpe, v2.tpe, m0, rigid)

    if (v1.id.params.length != v2.id.params.length) throw UnificationFailed(v1, v2) // Sanity check

    v1.id.params.zip(v2.id.params).foldLeft(m1) { case (curMeta, (p1, p2)) => unify(p1, p2, curMeta, rigid) }
  }

  def unify(v1: Value, v2: Value, meta: EqStore, rigid: Set[VarId]): EqStore = {
    val a = Interpreter.whnf(v1)(meta)
    val b = Interpreter.whnf(v2)(meta)

    (a, b) match {
      case (VProp, VProp)                                                 => meta
      case (VType(u1), VType(u2)) if u1 == u2                             => meta
      case (VConst(n1, c1, _), VConst(n2, c2, _)) if n1 == n2 && c1 == c2 => meta

      case (p1: VPi, p2: VPi) if p1.binders.length == p2.binders.length           => unifyPis(p1, p2, meta, rigid)._1
      case (l1: VLam, l2: VLam) if l1.tpe.binders.length == l2.tpe.binders.length =>
        // Lambda equality: first try ids, then referential equality, then extensional fallback
        if (l1.eq(l2) || l1.id == l2.id) meta
        else {
          val (nextMeta, nextEnv1, nextEnv2, nextRigid) = unifyPis(l1.tpe, l2.tpe, meta, rigid)
          val res1 = evalTerm(l1.body, nextEnv1)(nextMeta)
          val res2 = evalTerm(l2.body, nextEnv2)(nextMeta)
          unify(res1, res2, nextMeta, nextRigid)
        }
      case (VApp(h1, args1, _), VApp(h2, args2, _)) if args1.length == args2.length =>
        val startCtx = unify(h1, h2, meta, rigid)
        args1.zip(args2).foldLeft(startCtx) { case (newCtx, (arg1, arg2)) => unify(arg1, arg2, newCtx, rigid) }

      case (v1: StuckMatch, v2: StuckMatch) if v1.id.nodeId == v2.id.nodeId =>
        unifyStuckMatches(v1, v2, meta, rigid)

      // Unify FreshVars through ctx. Basic idea: FreshVars can point at things through context
      // unify creates a ctx of pointers. We only create pointers from the top of the chain

      case (Var(_, id1, _), Var(_, id2, _)) if id1 == id2 => meta

      // Link unlinked Var (left) to a non-Var value
      case (Var(_, id, ty), other) =>
        if (rigid.contains(id)) throw UnificationFailed(a, b)

        val m1 = unify(ty, other.tpe, meta, rigid)
        if (occurs(id, other, m1))
          throw OccursCheckFailed(id, other)
        m1.addLink(id, other)

      // Symmetric: link unlinked Var (right) to non-Var value
      case (other, Var(_, id, ty)) =>
        if (rigid.contains(id)) throw UnificationFailed(a, b)

        val m1 = unify(ty, other.tpe, meta, rigid)
        if (occurs(id, other, m1))
          throw OccursCheckFailed(id, other)
        m1.addLink(id, other)

      case _ => throw UnificationFailed(v1, v2)
    }
  }
}
