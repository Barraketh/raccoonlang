package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

object ValueEquivalence {
  def defEq(
      v1: Value,
      v2: Value,
      normalizerMap: Normalizers.NormalizerMap,
      propIrrelevant: Boolean
  ): Boolean =
    DefEq.defEq(v1, v2)(normalizerMap, propIrrelevant)

  def unify(v1: Value, v2: Value, meta: EqStore, normalizerMap: Normalizers.NormalizerMap): EqStore =
    tryUnify(v1, v2, meta, normalizerMap) match {
      case Right(eqStore)           => eqStore
      case Left((failed1, failed2)) => throw UnificationFailed(failed1, failed2)
    }

  def tryUnify(
      v1: Value,
      v2: Value,
      meta: EqStore,
      normalizerMap: Normalizers.NormalizerMap
  ): Either[(Value, Value), EqStore] =
    Unify.tryUnify(v1, v2, meta)(normalizerMap)

  private object DefEq {
    case class RelatedPis(vars: Vector[Value], out1: Value, out2: Value)

    def relatePis(pi1: VPi, pi2: VPi)(implicit normalizerMap: Normalizers.NormalizerMap): Option[RelatedPis] = {
      if (pi1.binders.zip(pi2.binders).exists { case (b1, b2) => b1.isInstance != b2.isInstance })
        return None

      val nextEnv1 = BinderOps.freshen(pi1)
      val sharedVars = pi1.binders.map(binder => nextEnv1(binder.localRef))
      val nextEnv2 =
        try BinderOps.checkAndInstantiate(pi2.binders, pi2.env, sharedVars, normalizerMap)
        catch { case _: TypeMismatch => return None }

      val out1 = pi1.codomain(nextEnv1)
      val out2 = pi2.codomain(nextEnv2)

      Some(RelatedPis(sharedVars, out1, out2))
    }

    private def defEqPi(pi1: VPi, pi2: VPi)(implicit
        normalizerMap: Normalizers.NormalizerMap,
        propIrrelevant: Boolean
    ): Option[Vector[Value]] =
      relatePis(pi1, pi2) match {
        case Some(related) if defEq(related.out1, related.out2) => Some(related.vars)
        case _                                                  => None
      }

    private def defEqLamId(id1: ValueId, id2: ValueId)(implicit
        normalizerMap: Normalizers.NormalizerMap,
        propIrrelevant: Boolean
    ): Boolean = {
      (id1, id2) match {
        case (ValueId.Const(n1), ValueId.Const(n2)) if n1 == n2 => true
        case (l1: ValueId.LocalId, l2: ValueId.LocalId)
            if l1.nodeId == l2.nodeId && l1.captures.length == l2.captures.length =>
          l1.captures.zip(l2.captures).forall { case (v1, v2) => defEq(v1, v2) }
        case _ => false
      }
    }

    def getNormalizerF(v1: Value, v2: Value)(implicit normalizerMap: Normalizers.NormalizerMap): Value => Value = {
      val key1 = Normalizers.getCarrierKey(v1.tpe)
      val key2 = Normalizers.getCarrierKey(v2.tpe)
      val normalizer =
        if (key1 == key2) key1.flatMap(normalizerMap.get)
        else None

      normalizer match {
        case Some(n) => (v: Value) => n.normalize(v)
        case None    => (v: Value) => v
      }
    }

    private def sameValueObject(v1: Value, v2: Value): Boolean =
      v1.asInstanceOf[AnyRef] eq v2.asInstanceOf[AnyRef]

    private def shouldTryStructuralDefEq(a: Value, b: Value): Boolean =
      a.needsStructuralDefEq || b.needsStructuralDefEq

    private def typeLivesInProp(tpe: Value): Boolean =
      tpe match {
        case PropTpe => false
        case tpe0 =>
          tpe0.tpe match {
            case PropTpe => true
            case _       => false
          }
      }

    private def proofIrrelevant(a: Value, b: Value)(implicit
        normalizerMap: Normalizers.NormalizerMap,
        propIrrelevant: Boolean
    ): Boolean =
      propIrrelevant && typeLivesInProp(a.tpe) && defEq(a.tpe, b.tpe)

    private def defEqStructural(a: Value, b: Value)(implicit
        normalizerMap: Normalizers.NormalizerMap,
        propIrrelevant: Boolean
    ): Boolean =
      (a, b) match {
        case (PropTpe, PropTpe)                               => true
        case (NormalizerType, NormalizerType)                 => true
        case (LevelTpe, LevelTpe)                             => true
        case (l1: Level, l2: Level)                           => l1 == l2 || Level.leq(l1, l2) && Level.leq(l2, l1)
        case (s1: VSort, s2: VSort)                           => defEq(s1.level, s2.level)
        case (VConst(n1, _, _), VConst(n2, _, _)) if n1 == n2 => true
        case (p1: VPi, p2: VPi) if p1.binders.length == p2.binders.length => defEqPi(p1, p2).isDefined
        case (l1: VLam, l2: VLam) if l1.tpe.binders.length == l2.tpe.binders.length =>
          if (l1.eq(l2) || defEqLamId(l1.id, l2.id)) true
          else {
            defEqPi(l1.tpe, l2.tpe) match {
              case Some(vars) =>
                val res1 = Interpreter.runLam(l1, vars)
                val res2 = Interpreter.runLam(l2, vars)
                defEq(res1, res2)
              case None => false
            }
          }

        case (v1: VApp, v2: VApp) if v1.args.length == v2.args.length =>
          defEq(v1.head, v2.head) &&
          v1.args.zip(v2.args).forall { case (arg1, arg2) => defEq(arg1, arg2) } &&
          defEq(v1.tpe, v2.tpe) // Important for constructors

        case (c1: ConstructorHead, c2: ConstructorHead) if c1.name == c2.name => true

        case (s1: NeutralThunk, s2: NeutralThunk) => defEqLamId(s1.id, s2.id)

        case (Var(_, id1, _), Var(_, id2, _)) if id1 == id2 => true
        case _                                              => false
      }

    def defEq(v1: Value, v2: Value)(implicit
        normalizerMap: Normalizers.NormalizerMap,
        propIrrelevant: Boolean
    ): Boolean = {
      if (sameValueObject(v1, v2)) true
      else if (proofIrrelevant(v1, v2)) true
      else {
        val normalizerF = getNormalizerF(v1, v2)

        val a = normalizerF(v1)
        val b = normalizerF(v2)

        sameValueObject(a, b) || a.key == b.key || (shouldTryStructuralDefEq(a, b) && defEqStructural(a, b))
      }
    }
  }

  private object Unify {
    private type Result = Either[(Value, Value), EqStore]

    private def tryUnifyPis(pi1: VPi, pi2: VPi, eqStore: EqStore)(implicit
        normalizerMap: Normalizers.NormalizerMap
    ): Either[(Value, Value), (EqStore, Vector[Value])] = {
      DefEq.relatePis(pi1, pi2) match {
        case None => Left((pi1, pi2))
        case Some(related) =>
          tryUnify(related.out1, related.out2, eqStore) match {
            case Right(nextEqStore) => Right((nextEqStore, related.vars))
            case Left(failed)       => Left(failed)
          }
      }
    }

    private def tryUnifyNeutralThunks(v1: NeutralThunk, v2: NeutralThunk, meta: EqStore)(implicit
        normalizerMap: Normalizers.NormalizerMap
    ): Result =
      tryUnify(v1.tpe, v2.tpe, meta) match {
        case Left(failed) => Left(failed)
        case Right(m1) =>
          if (v1.id.captures.length != v2.id.captures.length) Left((v1, v2))
          else {
            var curMeta = m1
            val captures = v1.id.captures.zip(v2.id.captures)
            val iter = captures.iterator
            while (iter.hasNext) {
              val (p1, p2) = iter.next()
              tryUnify(p1, p2, curMeta) match {
                case Left(failed) => return Left(failed)
                case Right(next)  => curMeta = next
              }
            }
            Right(curMeta)
          }
      }

    // Broad idea: we can unify (v + k) = other as v = other - k.  Everything else fails.
    private def unifyLevels(l1: Level, l2: Level, meta: EqStore): Option[EqStore] = {
      if (l1.atoms.size == 1 && l1.c == 0) {
        val (varId, k) = l1.atoms.head
        if (meta.isRefinable(varId) && !meta.occurs(varId, l2) && Level.geq(l2, k)) {
          val other = Level.addOffset(l2, -k)
          Some(meta.addLink(varId, other))
        } else None
      } else None
    }

    private def tryUnifySorts(v1: VSort, v2: VSort, meta: EqStore): Result = {
      (v1.level, v2.level) match {
        case (l1: Level, l2: Level) =>
          unifyLevels(l1, l2, meta)
            .orElse(unifyLevels(l2, l1, meta))
            .map(Right(_))
            .getOrElse(Left((l1, l2)))
        case _ => Left((v1, v2))
      }

    }

    private def tryLinkVar(v: Var, other: Value, meta: EqStore)(implicit
        normalizerMap: Normalizers.NormalizerMap
    ): Result = {
      val m1 =
        if (TypeChecker.sortLeq(other.tpe, v.tpe)) meta
        else
          tryUnify(v.tpe, other.tpe, meta) match {
            case Left(failed) => return Left(failed)
            case Right(next)  => next
          }
      if (m1.occurs(v.id, other)) Left((v, other))
      else Right(m1.addLink(v.id, other))
    }

    /**
     * This specifically handles wildcard vars during pattern matching. The problem is that wildcard vars never actually
     * get stored in Env, so they can't be properly quoted. This forces us to prefer the other var as the representative
     */
    private def tryLinkVarToPreferredRepresentative(v1: Var, v2: Var, meta: EqStore)(implicit
        normalizerMap: Normalizers.NormalizerMap
    ): Result = {
      val v1Anonymous = v1.name == "_"
      val v2Anonymous = v2.name == "_"
      val (toLink, representative) =
        if (v1Anonymous && !v2Anonymous) (v1, v2)
        else if (v2Anonymous && !v1Anonymous) (v2, v1)
        else if (v1.id > v2.id) (v1, v2)
        else (v2, v1)

      tryLinkVar(toLink, representative, meta)
    }

    def tryUnify(v1: Value, v2: Value, meta: EqStore)(implicit
        normalizerMap: Normalizers.NormalizerMap
    ): Result = {
      val resolved1 = ValueOps.materialize(v1, meta)
      val resolved2 = ValueOps.materialize(v2, meta)
      val normalizerF = DefEq.getNormalizerF(resolved1, resolved2)(normalizerMap)

      val a = normalizerF(resolved1)
      val b = normalizerF(resolved2)

      if (DefEq.defEq(a, b)(normalizerMap, propIrrelevant = true)) return Right(meta)

      (a, b) match {

        case (p1: VPi, p2: VPi) if p1.binders.length == p2.binders.length =>
          tryUnifyPis(p1, p2, meta) match {
            case Right((nextMeta, _)) => Right(nextMeta)
            case Left(failed)         => Left(failed)
          }
        case (l1: VLam, l2: VLam) if l1.tpe.binders.length == l2.tpe.binders.length =>
          // We know that the id check failed - falling back to extensional unification
          tryUnifyPis(l1.tpe, l2.tpe, meta) match {
            case Left(failed) => Left(failed)
            case Right((nextMeta, sharedVars)) =>
              val mappedVars = sharedVars.map(arg => ValueOps.materialize(arg, nextMeta))
              val res1 = Interpreter.runLam(ValueOps.materialize(l1, nextMeta).asInstanceOf[VLam], mappedVars)
              val res2 = Interpreter.runLam(ValueOps.materialize(l2, nextMeta).asInstanceOf[VLam], mappedVars)
              tryUnify(res1, res2, nextMeta)
          }
        case (v1: VApp, v2: VApp) if v1.args.length == v2.args.length =>
          tryUnify(v1.head, v2.head, meta) match {
            case Left(failed) => Left(failed)
            case Right(m0) =>
              var curMeta = m0
              val args = v1.args.zip(v2.args)
              val iter = args.iterator
              while (iter.hasNext) {
                val (arg1, arg2) = iter.next()
                tryUnify(arg1, arg2, curMeta) match {
                  case Left(failed) => return Left(failed)
                  case Right(next)  => curMeta = next
                }
              }
              tryUnify(v1.tpe, v2.tpe, curMeta) // Important for constructors
          }

        case (v1: NeutralThunk, v2: NeutralThunk) if v1.id.nodeId == v2.id.nodeId =>
          tryUnifyNeutralThunks(v1, v2, meta)

        case (s1: VSort, s2: VSort) => tryUnifySorts(s1, s2, meta)

        // Unify FreshVars through ctx. Basic idea: FreshVars can point at things through context
        // unify creates a ctx of pointers. We only create pointers from the top of the chain
        case (v1: Var, v2: Var) if meta.isRefinable(v1.id) && meta.isRefinable(v2.id) =>
          tryLinkVarToPreferredRepresentative(v1, v2, meta)

        // Link unlinked Var (left) to a non-Var value
        case (v: Var, other) if meta.isRefinable(v.id) => tryLinkVar(v, other, meta)

        // Symmetric: link unlinked Var (right) to non-Var value
        case (other, v: Var) if meta.isRefinable(v.id) => tryLinkVar(v, other, meta)

        case _ => Left((a, b))
      }
    }
  }
}
