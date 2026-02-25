package com.raccoonlang

import com.raccoonlang.Interpreter._

import scala.collection.immutable.BitSet

object Unify {

  def expandedDeps(rhsSyn: BitSet, meta: MetaStore): BitSet = {
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

  def occurs(id: MetaId, rhs: Value, meta: MetaStore): Boolean =
    expandedDeps(rhs.synDeps, meta).contains(id)

  // Extensionally unify Pi types
  private def unifyPis(pi1: VPi, pi2: VPi, meta: MetaStore): (MetaStore, Env, Env) = {
    val (resMeta, nextEnv1, nextEnv2) =
      pi1.binders.zip(pi2.binders).foldLeft((meta, pi1.env.newScope, pi2.env.newScope)) {
        case ((curMeta, curEnv1, curEnv2), (b1, b2)) =>
          val t1 = evalTerm(b1.ty, curMeta)(curEnv1)
          val t2 = evalTerm(b2.ty, curMeta)(curEnv2)
          val nextMeta = unify(t1, t2, curMeta)
          val x = FreshVar.freshVar(b1.name, t1)
          (nextMeta, curEnv1.putLocal(b1.name, x), curEnv2.putLocal(b2.name, x))
      }
    val out1 = evalTerm(pi1.out, resMeta)(nextEnv1)
    val out2 = evalTerm(pi2.out, resMeta)(nextEnv2)
    (unify(out1, out2, resMeta), nextEnv1, nextEnv2)
  }

  def unify(v1: Value, v2: Value, meta: MetaStore): MetaStore = {
    val a = Interpreter.whnf(v1, meta)
    val b = Interpreter.whnf(v2, meta)

    (a, b) match {
      case (VUniverse, VUniverse)                                         => meta
      case (VConst(n1, c1, _), VConst(n2, c2, _)) if n1 == n2 && c1 == c2 => meta

      case (p1: VPi, p2: VPi) if p1.binders.length == p2.binders.length           => unifyPis(p1, p2, meta)._1
      case (l1: VLam, l2: VLam) if l1.tpe.binders.length == l2.tpe.binders.length =>
        // Lambda equality: first try ids, then referential equality, then extensional fallback
        if (l1.eq(l2) || l1.id == l2.id) meta
        else {
          val (nextMeta, nextEnv1, nextEnv2) = unifyPis(l1.tpe, l2.tpe, meta)
          val res1 = evalTerm(l1.body, nextMeta)(nextEnv1)
          val res2 = evalTerm(l2.body, nextMeta)(nextEnv2)
          unify(res1, res2, nextMeta)
        }
      case (VApp(h1, args1, _), VApp(h2, args2, _)) if args1.length == args2.length =>
        val startCtx = unify(h1, h2, meta)
        args1.zip(args2).foldLeft(startCtx) { case (newCtx, (arg1, arg2)) => unify(arg1, arg2, newCtx) }

      // Unify FreshVars through ctx. Basic idea: FreshVars can point at things through context
      // unify creates a ctx of pointers. We only create pointers from the top of the chain

      case (Meta(_, id1, _), Meta(_, id2, _)) if id1 == id2 => meta

      // Link unlinked Var (left) to a non-Var value
      case (Meta(_, id, ty), other) =>
        val m1 = unify(ty, other.tpe, meta)
        if (occurs(id, other, m1))
          throw OccursCheckFailed(id, other)
        m1.addLink(id, other)

      // Symmetric: link unlinked Var (right) to non-Var value
      case (other, Meta(_, id, ty)) =>
        val m1 = unify(ty, other.tpe, meta)
        if (occurs(id, other, m1))
          throw OccursCheckFailed(id, other)
        m1.addLink(id, other)

      case _ => throw UnificationFailed(v1, v2)
    }
  }
}
