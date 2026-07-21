package com.raccoonlang.telescope

import com.raccoonlang.Value._
import com.raccoonlang._

import scala.collection.mutable

/**
 * Implicit binders are legal only when *forced*: recoverable from the values of the non-implicit binders by a
 * structural projection compiled at Pi formation. This module owns both halves:
 *
 *   - `compile` pattern-matches the *evaluated* types of the non-implicit binders (as patterns over the implicits'
 *     fresh vars) and produces a per-implicit `Spec` — which provided argument to start from and the path to walk.
 *     Every position used is rigid (irreducible head applications, no-confusion constructor fields, sorts/levels, Pi
 *     domains), so following the same path on the actual arguments at any later time re-derives the value. Projection
 *     is a *choice*, not a proof: application checking re-verifies every argument against its instantiated binder type,
 *     so soundness never rests on injectivity of these positions.
 *   - `project` follows a Spec against actual argument values. It is the single implementation used by check-time
 *     application, run-world residual evaluation, and check-world evaluation of checked syntax (match motives,
 *     termination measures, lambda-body quoting).
 *
 * Determinism: roots are tried leftmost-first and within a root in discovery order; the first path found for an
 * implicit wins everywhere (both worlds compile from the same telescope).
 */
object Projection {

  sealed trait Step
  object Step {

    /** value -> its type. */
    case object Tpe extends Step

    /** Application of an irreducible constant head (inductive family, axiom, opaque symbol) -> arg. */
    final case class SpineArg(head: String, idx: Int) extends Step

    /** No-confusion constructor value -> stored field (family args are erased from storage). */
    final case class CtorField(ctor: String, idx: Int) extends Step

    /** VSort -> its level. */
    case object SortLevel extends Step

    /** Level of the exact shape u + k -> u (single atom, no constant), mirroring unifyLevels. */
    final case class LevelOffset(k: Int) extends Step

    /** VPi -> evaluated domain of binder idx; valid only when independent of earlier binders. */
    final case class PiDomain(idx: Int) extends Step

    /** VPi -> codomain; valid only when it does not depend on the Pi's own binders. */
    case object PiCodomain extends Step
  }

  /**
   * Path from provided argument `rootArgIdx` (an index into the explicit args of a call) to the value of one implicit
   * binder.
   */
  final case class Spec(rootArgIdx: Int, steps: Vector[Step])

  final case class BinderInput(
      name: String,
      span: Span,
      isImplicit: Boolean,
      fresh: Value,
      holeId: Option[VarId]
  )

  /**
   * Final binder classification: family params of a constructor telescope that no field forces are demoted to explicit
   * instead of erroring, so `isImplicit` may differ from the input.
   */
  final case class BinderResult(isImplicit: Boolean, projection: Option[Spec])

  /**
   * Compile projection specs for a freshened telescope. The first `familyParams` binders are a constructor telescope's
   * synthesized family params: their author never wrote the braces, so when unforced they are demoted to explicit
   * instead of erroring. Everywhere else — defs, axioms, lambdas, and constructor binders the user wrote — an unforced
   * implicit throws NonForcedImplicitParam.
   */
  def compile(binders: Vector[BinderInput], familyParams: Int = 0): Vector[BinderResult] =
    compileDemotable(binders, (0 until familyParams).toSet)

  private[raccoonlang] def compileDemotable(
      binders: Vector[BinderInput],
      demotable: Set[Int]
  ): Vector[BinderResult] = {
    if (binders.forall(!_.isImplicit))
      return binders.map(_ => BinderResult(isImplicit = false, projection = None))

    // Recognize non-proof fresh ids inside visited values. Proof binders are handled separately by
    // proposition below: VProof deliberately contains no hidden witness to recover an id from.
    def valueHoleId(v: Value): Option[VarId] =
      v match {
        case Var(_, id, _) => Some(id)
        case level: Level =>
          Level.singleVariableOffset(level).collect { case (id, 0) => id }
        case _ => None
      }

    val holeOfVar = mutable.Map.empty[VarId, Int]
    val proofHoles = Vector.newBuilder[(Int, Value)]
    binders.zipWithIndex.foreach { case (b, idx) =>
      if (b.isImplicit) {
        if (Value.isPropositionType(b.fresh.tpe)) proofHoles += idx -> b.fresh.tpe
        else b.holeId.foreach(id => holeOfVar.update(id, idx))
      }
    }
    val proofHolesByType = proofHoles.result()
    val proofHolesByKey = proofHolesByType.groupBy(_._2.key)
    val structurallyComparableProofHoles = proofHolesByType.filter(_._2.needsStructuralDefEq)
    val proofHoleIndexes = proofHolesByType.iterator.map(_._1).toSet
    var remainingProofHoles = proofHoleIndexes.size

    // Eta-expanded structure-like binders have no top-level Var id: their rigid representation is already a VCtor of
    // fresh fields. Retain the whole fresh pattern as their occurrence marker so an exact occurrence in a later root
    // can still force the implicit. The key is only an index; defEq below verifies each candidate before trusting it.
    val etaHolesByKey = binders.zipWithIndex
      .collect {
        case (b, idx)
            if b.isImplicit && b.holeId.isEmpty && !Value.isPropositionType(b.fresh.tpe) &&
              StructEta.eligibleInstance(b.fresh.tpe).nonEmpty =>
          b.fresh.key -> (idx, b.fresh)
      }
      .groupMap(_._1)(_._2)

    val demoted = mutable.Set.empty[Int]
    val solved = mutable.LinkedHashMap.empty[Int, (Int, Vector[Step])]
    val queue = mutable.ArrayDeque.empty[(Int, Vector[Step], Value)]

    def isRoot(idx: Int): Boolean = !binders(idx).isImplicit || demoted(idx)

    def solveHole(hole: Int, root: Int, steps: Vector[Step], tpe: Value): Unit =
      if (!isRoot(hole) && !solved.contains(hole)) {
        solved.update(hole, (root, steps))
        if (proofHoleIndexes(hole)) remainingProofHoles -= 1
        // Saturation: the hole's own declared type is a pattern over earlier implicits,
        // reachable from the projected value by one more Tpe step.
        queue.append((root, steps :+ Step.Tpe, tpe))
      }

    def rigidHead(head: VConst): Boolean =
      head.constType match {
        case Inductive(_) => true
        case Symbol       => true
        // A stuck projection reduces once its base becomes constructor-headed, so its spine is
        // not a stable pattern to project from.
        case StructField(_, _, _) => false
      }

    def visit(root: Int, steps: Vector[Step], v: Value): Unit = {
      etaHolesByKey.get(v.key).foreach { candidates =>
        candidates.foreach { case (hole, pattern) =>
          if (ValueEquivalence.defEq(pattern, v)) solveHole(hole, root, steps, v.tpe)
        }
      }

      // Proof binders carry no occurrence marker at runtime. Proof irrelevance makes any proof of
      // the same proposition a valid reconstruction, so a proof-valued position in a later
      // argument type forces every matching implicit proof binder through that projection path.
      // This is checker-only analysis; no witness is added to VProof and runtime merely follows
      // the compiled structural path.
      if (remainingProofHoles > 0 && Value.isPropositionType(v.tpe)) {
        // Key-equal propositions cover the ordinary case. Structural propositions (notably Pis)
        // can be defEq despite different identity-based keys, so retain that narrow fallback.
        val keyed = proofHolesByKey.getOrElse(v.tpe.key, Vector.empty)
        val structural =
          if (v.tpe.needsStructuralDefEq) proofHolesByType
          else structurallyComparableProofHoles
        (keyed.iterator ++ structural.iterator).foreach { case (hole, proposition) =>
          if (!solved.contains(hole) && ValueEquivalence.defEq(proposition, v.tpe))
            solveHole(hole, root, steps, v.tpe)
        }
      }

      v match {
        // Level occurrences have one path: single-atom `u + k` (k = 0 included) inverts to u.
        case level: Level =>
          Level.singleVariableOffset(level).foreach { case (id, k) =>
            holeOfVar.get(id).foreach { hole =>
              val path = if (k == 0) steps else steps :+ Step.LevelOffset(k)
              solveHole(hole, root, path, LevelTpe)
            }
          }

        case _ =>
          valueHoleId(v).flatMap(holeOfVar.get) match {
            case Some(hole) => solveHole(hole, root, steps, v.tpe)
            case None =>
              v match {
                case VSort(level) =>
                  queue.append((root, steps :+ Step.SortLevel, level))

                case VCtor(head, stored, tpe) =>
                  if (head.noConfusion)
                    stored.zipWithIndex.foreach { case (field, idx) =>
                      queue.append((root, steps :+ Step.CtorField(head.name, idx), field))
                    }
                  // Erased family args live only in the constructor value's type.
                  queue.append((root, steps :+ Step.Tpe, tpe))

                case ConstSpine(head, args) if args.nonEmpty && rigidHead(head) =>
                  args.zipWithIndex.foreach { case (arg, idx) =>
                    queue.append((root, steps :+ Step.SpineArg(head.name, idx), arg))
                  }

                case p: VProof =>
                  queue.append((root, steps :+ Step.Tpe, p.tpe))

                case pi: VPi =>
                  pi.binders.indices.foreach { idx =>
                    independentPiDomain(pi, idx).foreach { domain =>
                      queue.append((root, steps :+ Step.PiDomain(idx), domain))
                    }
                  }
                  independentPiCodomain(pi).foreach { out =>
                    queue.append((root, steps :+ Step.PiCodomain, out))
                  }

                case _ => ()
              }
          }
      }
    }

    def drain(): Unit =
      while (queue.nonEmpty) {
        val (root, steps, v) = queue.removeHead()
        visit(root, steps, v)
      }

    binders.zipWithIndex.foreach { case (b, idx) =>
      if (isRoot(idx)) queue.append((idx, Vector(Step.Tpe), b.fresh.tpe))
    }
    drain()

    // Demoting a family param turns it into a root, which can force further implicits (demoting A
    // in `Option {u}(A)` forces u through `A : Sort(u)`), so demote minimally: rightmost unforced
    // param first. Binder types only mention earlier binders, so forcing flows right-to-left and
    // this order never demotes a param a later demotion would have forced. Demotion only adds a
    // root — existing solutions stay valid — so saturation resumes with just the new root.
    if (demotable.nonEmpty) {
      var progress = true
      while (progress) {
        val rightmostUnforced = binders.indices.reverse.find { idx =>
          demotable(idx) &&
          binders(idx).isImplicit && !demoted(idx) && !solved.contains(idx)
        }
        rightmostUnforced match {
          case Some(idx) =>
            demoted.add(idx)
            if (proofHoleIndexes(idx)) remainingProofHoles -= 1
            queue.append((idx, Vector(Step.Tpe), binders(idx).fresh.tpe))
            drain()
          case None => progress = false
        }
      }
    }

    binders.zipWithIndex.map { case (b, idx) =>
      val implicitNow = b.isImplicit && !demoted(idx)
      if (!implicitNow) BinderResult(isImplicit = false, projection = None)
      else
        solved.get(idx) match {
          case Some((rootTelescopeIdx, steps)) =>
            // Convert the telescope index of the root into its position among provided args.
            val rootArgIdx = (0 until rootTelescopeIdx).count { j =>
              !binders(j).isImplicit || demoted(j)
            }
            BinderResult(isImplicit = true, projection = Some(Spec(rootArgIdx, steps)))
          case None =>
            throw NonForcedImplicitParam(b.name, Some(b.span))
        }
    }
  }

  /**
   * Domain of binder `idx`, evaluated under fresh earlier binders; None when it depends on them (such a position is not
   * stable across instantiations).
   */
  private def independentPiDomain(pi: VPi, idx: Int): Option[Value] = {
    val freshEnv = BinderOps.freshen(pi.binders.take(idx), pi.env)
    val freshIds = Value.envDeps(freshEnv) -- Value.envDeps(pi.env)
    val domain = Interpreter.evalTerm(pi.binders(idx).ty, freshEnv)
    if (domain.synDeps.intersects(freshIds)) None else Some(domain)
  }

  private def independentPiCodomain(pi: VPi): Option[Value] = {
    val freshEnv = BinderOps.freshen(pi)
    val freshIds = Value.envDeps(freshEnv) -- Value.envDeps(pi.env)
    val out = pi.codomain(freshEnv)
    if (out.synDeps.intersects(freshIds)) None else Some(out)
  }

  /** Follow a compiled spec against the provided (explicit) arguments of a call. */
  def project(spec: Spec, providedArgs: Vector[Value]): Either[String, Value] = {
    if (spec.rootArgIdx >= providedArgs.length)
      return Left(s"projection root ${spec.rootArgIdx} out of range (${providedArgs.length} args)")

    def toLevel(v: Value): Either[String, Level] =
      Level.fromValue(v).toRight(s"expected a level, got $v")

    spec.steps.foldLeft[Either[String, Value]](Right(providedArgs(spec.rootArgIdx))) {
      case (left @ Left(_), _) => left
      case (Right(v), step) =>
        step match {
          case Step.Tpe => Right(v.tpe)

          case Step.SpineArg(head, idx) =>
            v match {
              case ConstSpine(c, args) if c.name == head && idx < args.length => Right(args(idx))
              case other => Left(s"expected an application of $head, got $other")
            }

          case Step.CtorField(ctor, idx) =>
            v match {
              case VCtor(h, stored, _) if h.name == ctor && idx < stored.length => Right(stored(idx))
              case p: VPacked =>
                val (name, decoded) = p.codec.decodeHead(p)
                if (name == ctor && idx < decoded.length) Right(decoded(idx))
                else Left(s"expected a $ctor value, got $p")
              case other => Left(s"expected a $ctor value, got $other")
            }

          case Step.SortLevel =>
            v match {
              case VSort(level) => Right(level)
              case other        => Left(s"expected a sort, got $other")
            }

          case Step.LevelOffset(k) =>
            toLevel(v).flatMap { l =>
              if (k == 0) Right(l)
              else if (Level.geq(l, k)) Right(Level.addOffset(l, -k))
              else Left(s"level $l does not cover offset $k")
            }

          case Step.PiDomain(idx) =>
            v match {
              case pi: VPi if idx < pi.binders.length =>
                independentPiDomain(pi, idx).toRight(s"domain $idx of $pi depends on earlier binders")
              case other => Left(s"expected a function type, got $other")
            }

          case Step.PiCodomain =>
            v match {
              case pi: VPi =>
                independentPiCodomain(pi).toRight(s"codomain of $pi depends on its binders")
              case other => Left(s"expected a function type, got $other")
            }
        }
    }
  }
}
