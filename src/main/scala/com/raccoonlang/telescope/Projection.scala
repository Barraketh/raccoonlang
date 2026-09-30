package com.raccoonlang.telescope

import com.raccoonlang.Value._
import com.raccoonlang._

import scala.collection.mutable

/**
 * Implicit binders are legal only when *forced*: recoverable from the values of the explicit binders by a structural
 * projection compiled at Pi formation. An evidence binder is never a root, supplied or not (PROOF_BY_EVALUATION §1.5):
 * its argument is discharged from its proposition, so it is no source for forcing. This module owns both halves:
 *
 *   - `compile` pattern-matches the *evaluated* types of the explicit binders (as patterns over the implicits' fresh
 *     vars) and produces a per-implicit `Spec` — which provided argument to start from and the path to walk. Every
 *     position used is rigid (irreducible head applications, no-confusion constructor fields, sort fields and levels,
 *     Pi closures and domains), so following the same path on the actual arguments at any later time re-derives the
 *     value. Projection is a *choice*, not a proof: application checking re-verifies every argument against its
 *     instantiated binder type, so soundness never rests on injectivity of these positions.
 *   - `project` follows a Spec against actual argument values. It is the single implementation used by check-time
 *     application, run-world residual evaluation, and check-world evaluation of checked syntax (match motives,
 *     termination measures, lambda-body quoting).
 *
 * Determinism: positions are visited breadth-first from the roots, leftmost root first, with closures last; the first
 * path found for an implicit wins everywhere (both worlds compile from the same telescope).
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

    /** VSort -> its kind; it recovers a kind variable only when the kind is exactly that variable. */
    case object SortKind extends Step

    /** VSort -> its scope; it recovers a lifetime variable only when the scope is exactly that variable. */
    case object SortScope extends Step

    /** Level of the exact shape u + k -> u (single atom, no constant), mirroring unifyLevels. */
    final case class LevelOffset(k: Int) extends Step

    /** VPi -> its closure kind; it recovers a kind variable only when the closure kind is exactly that variable. */
    case object PiClosureKind extends Step

    /**
     * VPi -> its closure scope; it recovers a lifetime variable only when the closure scope is exactly that variable.
     */
    case object PiClosureScope extends Step

    /** VPi -> evaluated domain of binder idx; valid only when independent of earlier binders. */
    final case class PiDomain(idx: Int) extends Step

    /** VPi -> codomain after one binder; valid only when that tail does not depend on the removed binder. */
    case object PiCodomain extends Step

    /** VPi -> final result after every binder; valid only when the result is independent of all binders. */
    case object PiResult extends Step
  }

  /**
   * Path from provided argument `rootArgIdx` (an index into the explicit args of a call) to the value of one implicit
   * binder.
   */
  final case class Spec(rootArgIdx: Int, steps: Vector[Step])

  /**
   * Why `project` could not follow a spec, as data, so that a diagnostic prints the values it holds as every other
   * value it prints (`ErrorRendering`).
   */
  sealed trait Failure
  object Failure {

    /** The spec's root is argument `root`, but only `provided` were given. */
    final case class RootOutOfRange(root: Int, provided: Int) extends Failure

    /** A step that reads a level met `got`. */
    final case class NotALevel(got: Value) extends Failure

    /** A step that reads an argument of an application of `head` met `got`. */
    final case class NotAnApplication(head: String, got: Value) extends Failure

    /** A step that reads a field of `ctor` met `got`. */
    final case class NotAConstructor(ctor: String, got: Value) extends Failure

    /** A step that reads a sort's field met `got`. */
    final case class NotASort(got: Value) extends Failure

    /** A step that reads part of a function type met `got`. */
    final case class NotAFunctionType(got: Value) extends Failure

    /** A step that takes `offset` off a level met `level`, which does not cover it. */
    final case class LevelBelowOffset(level: Level, offset: Int) extends Failure

    /** The domain of binder `idx` of `pi` depends on earlier binders. */
    final case class DependentDomain(idx: Int, pi: VPi) extends Failure

    /** The codomain of `pi` past its first binder depends on it. */
    final case class DependentCodomain(pi: VPi) extends Failure

    /** The result of `pi` depends on its binders. */
    final case class DependentResult(pi: VPi) extends Failure
  }

  final case class BinderInput(
      name: String,
      span: Span,
      mode: BinderMode,
      fresh: Value,
      holeId: Option[VarId]
  )

  /**
   * Final binder classification: family params of a constructor telescope that no field forces are demoted to explicit
   * instead of erroring, so `mode` may differ from the input.
   */
  final case class BinderResult(mode: BinderMode, projection: Option[Spec])

  /**
   * Compile projection specs for a freshened telescope. The first `familyParams` binders are a constructor telescope's
   * synthesized family params: their author never wrote the braces, so when unforced they are demoted to explicit
   * instead of erroring. Everywhere else — defs, axioms, lambdas, and constructor binders the user wrote — an unforced
   * implicit throws NonForcedImplicitParam. `site` is where the telescope is written: a path reads a sealed
   * constructor's field only inside its family's module (spec §7.1).
   */
  def compile(binders: Vector[BinderInput], familyParams: Int, site: Span): Vector[BinderResult] =
    compileDemotable(binders, (0 until familyParams).toSet, site)

  private def compileDemotable(
      binders: Vector[BinderInput],
      demotable: Set[Int],
      site: Span
  ): Vector[BinderResult] = {
    if (binders.forall(_.mode != BinderMode.Implicit))
      return binders.map(b => BinderResult(b.mode, projection = None))

    // Recognize non-proof fresh ids inside visited values. Proof binders are handled separately by
    // proposition below: VProof deliberately contains no hidden witness to recover an id from.
    def valueHoleId(v: Value): Option[VarId] =
      v match {
        case Var(_, id, _) => Some(id)
        case level: Level =>
          Level.singleVariableOffset(level).collect { case (id, 0) => id }
        case kind: Kind         => Kind.singleVariable(kind)
        case lifetime: Lifetime => Lifetime.singleVariable(lifetime)
        case _                  => None
      }

    val holeOfVar = mutable.Map.empty[VarId, Int]
    val proofHoles = Vector.newBuilder[(Int, Value)]
    // A token is never read off a type, since no type contains one (spec §3.2): an implicit of linear type has no hole,
    // so it is never forced.
    binders.zipWithIndex.foreach { case (b, idx) =>
      if (b.mode == BinderMode.Implicit) {
        if (Sorts.isProposition(b.fresh.tpe)) proofHoles += idx -> b.fresh.tpe
        else if (!Linearity.isLinear(b.fresh.tpe)) b.holeId.foreach(id => holeOfVar.update(id, idx))
      }
    }
    val proofHolesByType = proofHoles.result()
    val proofHolesByKey = proofHolesByType.groupBy(_._2.key)
    val structurallyComparableProofHoles = proofHolesByType.filter(_._2.needsStructuralDefEq)
    val proofHoleIndexes = proofHolesByType.iterator.map(_._1).toSet
    var remainingProofHoles = proofHoleIndexes.size

    val demoted = mutable.Set.empty[Int]
    val solved = mutable.LinkedHashMap.empty[Int, (Int, Vector[Step])]
    val queue = mutable.ArrayDeque.empty[(Int, Vector[Step], Value)]
    // A closure is read only once nothing else is left to visit. It is the one part of a function type that a lambda
    // derives from its captures, so it is the part an argument most often gets wrong; an implicit read there would turn
    // that into a mismatch wherever else the implicit occurs, while one read elsewhere leaves the argument's own check
    // to report the closure.
    val closures = mutable.ArrayDeque.empty[(Int, Vector[Step], Value)]

    def isRoot(idx: Int): Boolean = binders(idx).mode == BinderMode.Explicit || demoted(idx)

    def solveHole(hole: Int, root: Int, steps: Vector[Step], tpe: Value): Unit =
      if (binders(hole).mode == BinderMode.Implicit && !demoted(hole) && !solved.contains(hole)) {
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
      }

    def visit(root: Int, steps: Vector[Step], v: Value): Unit = {
      // Proof binders carry no occurrence marker at runtime. Proof irrelevance makes any proof of
      // the same proposition a valid reconstruction, so a proof-valued position in a later
      // argument type forces every matching implicit proof binder through that projection path.
      // This is checker-only analysis; no witness is added to VProof and runtime merely follows
      // the compiled structural path.
      if (remainingProofHoles > 0 && Sorts.isProposition(v.tpe)) {
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
                case sort: VSort =>
                  queue.append((root, steps :+ Step.SortLevel, sort.level))
                  queue.append((root, steps :+ Step.SortKind, sort.kind))
                  queue.append((root, steps :+ Step.SortScope, sort.scope))

                case VCtor(head, stored, tpe) =>
                  if (head.noConfusion && Sealing.accessible(familySeal(tpe), site))
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
                  closures.append((root, steps :+ Step.PiClosureKind, pi.closureKind))
                  closures.append((root, steps :+ Step.PiClosureScope, pi.closureScope))
                  pi.binders.indices.foreach { idx =>
                    independentPiDomain(pi, idx).foreach { domain =>
                      queue.append((root, steps :+ Step.PiDomain(idx), domain))
                    }
                  }
                  independentPiCodomain(pi) match {
                    case Some(out) => queue.append((root, steps :+ Step.PiCodomain, out))
                    case None if pi.binders.length > 1 =>
                      independentPiResult(pi).foreach { out =>
                        queue.append((root, steps :+ Step.PiResult, out))
                      }
                    case None =>
                  }

                case _ => ()
              }
          }
      }
    }

    def drain(): Unit =
      while (queue.nonEmpty || closures.nonEmpty) {
        val (root, steps, v) = if (queue.nonEmpty) queue.removeHead() else closures.removeHead()
        visit(root, steps, v)
      }

    binders.zipWithIndex.foreach { case (b, idx) =>
      if (isRoot(idx)) queue.append((idx, Vector(Step.Tpe), b.fresh.tpe))
    }
    drain()

    // Demoting a family param turns it into a root, which can force further implicits (demoting A
    // in `Option {u}(A)` forces u through `A : Sort { level = u }`), so demote minimally: rightmost unforced
    // param first. Binder types only mention earlier binders, so forcing flows right-to-left and
    // this order never demotes a param a later demotion would have forced. Demotion only adds a
    // root — existing solutions stay valid — so saturation resumes with just the new root.
    if (demotable.nonEmpty) {
      var progress = true
      while (progress) {
        val rightmostUnforced = binders.indices.reverse.find { idx =>
          demotable(idx) &&
          binders(idx).mode == BinderMode.Implicit && !demoted(idx) && !solved.contains(idx)
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
      if (demoted(idx)) BinderResult(BinderMode.Explicit, projection = None)
      else if (b.mode != BinderMode.Implicit) BinderResult(b.mode, projection = None)
      else
        solved.get(idx) match {
          case Some((rootTelescopeIdx, steps)) =>
            // Convert the telescope index of the root into its position among provided args.
            val rootArgIdx = (0 until rootTelescopeIdx).count(isRoot)
            BinderResult(BinderMode.Implicit, projection = Some(Spec(rootArgIdx, steps)))
          case None =>
            at(b.span) { fail(NonForcedImplicitParam(b.name, Sorts.isProposition(b.fresh.tpe))) }
        }
    }
  }

  /** The seal of the family a constructor value belongs to, read off its type. */
  private def familySeal(ctorTpe: Value): Option[Sealing.Seal] =
    ctorTpe match {
      case InductiveFamilyValue(instance) => instance.meta.seal
      case other => wtf(s"A constructor value has the type $other, which is no family instance")
    }

  /**
   * Domain of binder `idx`, evaluated under fresh earlier binders; None when it depends on them (such a position is not
   * stable across instantiations). Indices are into the Pi's own binder group: grouping is part of the type's identity,
   * so a curried and an uncurried spelling are different types and project differently.
   */
  private def independentPiDomain(pi: VPi, idx: Int): Option[Value] = {
    val freshEnv = BinderOps.freshen(pi.binders.take(idx), pi.env)
    val freshIds = Value.envDeps(freshEnv) -- Value.envDeps(pi.env)
    val domain = Interpreter.evalTerm(pi.binders(idx).ty, freshEnv)
    if (domain.synDeps.intersects(freshIds)) None else Some(domain)
  }

  /**
   * The type that remains after removing the Pi group's *first* binder; None when anything left depends on it. With a
   * single binder that is the codomain itself; otherwise it is a Pi over the remaining binders.
   */
  private def independentPiCodomain(pi: VPi): Option[Value] = {
    val firstEnv = BinderOps.freshen(pi.binders.take(1), pi.env)
    val firstIds = Value.envDeps(firstEnv) -- Value.envDeps(pi.env)
    val remaining = pi.binders.drop(1)
    if (remaining.isEmpty) {
      val out = pi.codomain(firstEnv)
      Option.when(!out.synDeps.intersects(firstIds))(out)
    } else {
      val fullEnv = BinderOps.freshen(remaining, firstEnv)
      val binderTypes = remaining.map(binder => fullEnv(binder.localRef).tpe)
      val out = pi.codomain(fullEnv)
      if ((binderTypes :+ out).exists(_.synDeps.intersects(firstIds))) None
      else {
        // The remaining group keeps the closure: it is the same function's, applied one binder further. It keeps the
        // node identity and captures too, which is sound: a Pi's key counts its binders (docs/kernel.md#value-identity),
        // so the only Pis sharing this key are this node's, at these captures, less as many leading binders.
        Some(
          pi.copy(
            env = firstEnv,
            binders = remaining,
            synDeps = pi.synDeps,
            classifier0 =
              () => Interpreter.piClassifierFromChecked(remaining, fullEnv, out, pi.closureKind, pi.closureScope)
          )
        )
      }
    }
  }

  /** The Pi's result, past its own binder group; None when it depends on any of them. */
  private def independentPiResult(pi: VPi): Option[Value] = {
    val freshEnv = BinderOps.freshen(pi)
    val freshIds = Value.envDeps(freshEnv) -- Value.envDeps(pi.env)
    val out = pi.codomain(freshEnv)
    Option.when(!out.synDeps.intersects(freshIds))(out)
  }

  /**
   * Follow a compiled spec against the provided (explicit) arguments of a call. A step reads the one argument or field
   * it names, as stored, and forces only that one: evaluation projects implicits at every call, and must evaluate no
   * proposition of an evidence argument beside it.
   */
  def project(spec: Spec, providedArgs: Vector[Value]): Either[Failure, Value] = {
    if (spec.rootArgIdx >= providedArgs.length)
      return Left(Failure.RootOutOfRange(spec.rootArgIdx, providedArgs.length))

    def toLevel(v: Value): Either[Failure, Level] =
      v match {
        case l: Level => Right(l)
        case other    => Left(Failure.NotALevel(other))
      }

    spec.steps.foldLeft[Either[Failure, Value]](Right(providedArgs(spec.rootArgIdx))) {
      case (left @ Left(_), _) => left
      case (Right(v), step) =>
        step match {
          case Step.Tpe => Right(v.tpe)

          case Step.SpineArg(head, idx) =>
            v match {
              case app: VApp if app.blockedOn.isEmpty && idx < app.storedArgs.length =>
                app.head match {
                  case c: VConst if c.name == head => Right(Value.forced(app.storedArgs(idx)))
                  case _                           => Left(Failure.NotAnApplication(head, app))
                }
              case other => Left(Failure.NotAnApplication(head, other))
            }

          case Step.CtorField(ctor, idx) =>
            v match {
              case ConstructorForm.Stored(name, stored) if name == ctor && idx < stored.length =>
                Right(Value.forced(stored(idx)))
              case other => Left(Failure.NotAConstructor(ctor, other))
            }

          case Step.SortLevel =>
            v match {
              case sort: VSort => Right(sort.level)
              case other       => Left(Failure.NotASort(other))
            }

          case Step.SortKind =>
            v match {
              case sort: VSort => Right(sort.kind)
              case other       => Left(Failure.NotASort(other))
            }

          case Step.SortScope =>
            v match {
              case sort: VSort => Right(sort.scope)
              case other       => Left(Failure.NotASort(other))
            }

          case Step.LevelOffset(k) =>
            toLevel(v).flatMap { l =>
              if (k == 0) Right(l)
              else if (Level.geq(l, k)) Right(Level.addOffset(l, -k))
              else Left(Failure.LevelBelowOffset(l, k))
            }

          case Step.PiClosureKind =>
            v match {
              case pi: VPi => Right(pi.closureKind)
              case other   => Left(Failure.NotAFunctionType(other))
            }

          case Step.PiClosureScope =>
            v match {
              case pi: VPi => Right(pi.closureScope)
              case other   => Left(Failure.NotAFunctionType(other))
            }

          case Step.PiDomain(idx) =>
            v match {
              case pi: VPi if idx < pi.binders.length =>
                independentPiDomain(pi, idx).toRight(Failure.DependentDomain(idx, pi))
              case other => Left(Failure.NotAFunctionType(other))
            }

          case Step.PiCodomain =>
            v match {
              case pi: VPi =>
                independentPiCodomain(pi).toRight(Failure.DependentCodomain(pi))
              case other => Left(Failure.NotAFunctionType(other))
            }

          case Step.PiResult =>
            v match {
              case pi: VPi => independentPiResult(pi).toRight(Failure.DependentResult(pi))
              case other   => Left(Failure.NotAFunctionType(other))
            }
        }
    }
  }
}
