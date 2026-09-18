package com.raccoonlang.telescope

import com.raccoonlang.Value._
import com.raccoonlang._
import scala.collection.mutable

/** Structural, deterministic reconstruction of forced implicit binders. */
object Projection {
  sealed trait Step
  object Step {
    case object Tpe extends Step
    final case class SpineArg(head: String, idx: Int) extends Step
    final case class CtorField(ctor: String, idx: Int) extends Step
    case object SortLevel extends Step
    final case class LevelOffset(k: Int) extends Step
    final case class PiDomain(idx: Int) extends Step
    case object PiCodomain extends Step
    case object PiResult extends Step
  }
  final case class Spec(rootArgIdx: Int, steps: Vector[Step])
  final case class BinderInput(name: String, span: Span, isImplicit: Boolean, fresh: Value, holeId: Option[Value.VarId])
  final case class BinderResult(isImplicit: Boolean, projection: Option[Spec])

  def compile(binders: Vector[BinderInput], familyParams: Int = 0): Vector[BinderResult] = {
    val demotable = (0 until familyParams).toSet
    if (binders.forall(!_.isImplicit)) return binders.map(_ => BinderResult(false, None))
    val holes = mutable.Map.empty[Value.VarId, Int]
    binders.zipWithIndex.foreach { case (b, i) => if (b.isImplicit) b.holeId.foreach(id => holes.update(id, i)) }
    val demoted = mutable.Set.empty[Int]
    val solved = mutable.LinkedHashMap.empty[Int, (Int, Vector[Step])]
    val queue = mutable.ArrayDeque.empty[(Int, Vector[Step], Value)]
    def isRoot(i: Int): Boolean = !binders(i).isImplicit || demoted(i)
    def solve(hole: Int, root: Int, path: Vector[Step], tpe: Value): Unit =
      if (!isRoot(hole) && !solved.contains(hole)) {
        solved.update(hole, root -> path)
        queue.append((root, path :+ Step.Tpe, tpe))
      }
    def rigid(head: VConst): Boolean = head.constType match { case Inductive(_) | Symbol => true }
    def valueHoleId(value: Value): Option[Value.VarId] = value match {
      case Var(_, id, _) => Some(id)
      case _             => None
    }
    val proofHoles = binders.zipWithIndex.collect {
      case (b, i) if b.isImplicit && Value.isPropositionType(b.fresh.tpe) => i -> b.fresh.tpe
    }
    val proofHolesByKey = proofHoles.groupBy(_._2.key)
    val structurallyComparableProofHoles = proofHoles.filter(_._2.needsStructuralDefEq)
    val proofHoleIndexes = proofHoles.iterator.map(_._1).toSet
    var remainingProofHoles = proofHoleIndexes.size

    def solveProof(hole: Int, root: Int, path: Vector[Step], tpe: Value): Unit =
      if (!isRoot(hole) && !solved.contains(hole)) {
        solved.update(hole, root -> path)
        remainingProofHoles -= 1
        queue.append((root, path :+ Step.Tpe, tpe))
      }

    def visit(root: Int, path: Vector[Step], value: Value): Unit = {
      if (remainingProofHoles > 0 && Value.isPropositionType(value.tpe)) {
        val keyed = proofHolesByKey.getOrElse(value.tpe.key, Vector.empty)
        val structural = if (value.tpe.needsStructuralDefEq) proofHoles else structurallyComparableProofHoles
        (keyed.iterator ++ structural.iterator).foreach { case (hole, proposition) =>
          if (!solved.contains(hole) && ValueEquivalence.defEq(proposition, value.tpe))
            solveProof(hole, root, path, value.tpe)
        }
      }

      value match {
        case level: Level =>
          Level.singleVariableOffset(level).foreach { case (id, k) =>
            holes.get(id).foreach(h => solve(h, root, if (k == 0) path else path :+ Step.LevelOffset(k), LevelTpe))
          }
        case _ if valueHoleId(value).exists(holes.contains) =>
          solve(holes(valueHoleId(value).get), root, path, value.tpe)
        case VSort(level) => queue.append((root, path :+ Step.SortLevel, level))
        case VCtor(head, fields, tpe) =>
          if (head.noConfusion) fields.zipWithIndex.foreach { case (field, i) =>
            queue.append((root, path :+ Step.CtorField(head.name, i), field))
          }
          queue.append((root, path :+ Step.Tpe, tpe))
        case ConstSpine(head, args) if args.nonEmpty && rigid(head) =>
          args.zipWithIndex.foreach { case (arg, i) => queue.append((root, path :+ Step.SpineArg(head.name, i), arg)) }
        case pi: VPi =>
          pi.binders.indices.foreach(i =>
            independentPiDomain(pi, i).foreach(v => queue.append((root, path :+ Step.PiDomain(i), v)))
          )
          independentPiCodomain(pi) match {
            case Some(v) => queue.append((root, path :+ Step.PiCodomain, v))
            case None if pi.binders.length > 1 =>
              independentPiResult(pi).foreach(v => queue.append((root, path :+ Step.PiResult, v)))
            case _ =>
          }
        case p: VProof =>
          queue.append((root, path :+ Step.Tpe, p.tpe))
        case _ =>
      }
    }
    def drain(): Unit = while (queue.nonEmpty) { val (r, p, v) = queue.removeHead(); visit(r, p, v) }
    binders.indices.foreach(i => if (isRoot(i)) queue.append((i, Vector(Step.Tpe), binders(i).fresh.tpe)))
    drain()
    var more = true
    while (more) {
      binders.indices.reverse.find(i =>
        demotable(i) && binders(i).isImplicit && !demoted(i) && !solved.contains(i)
      ) match {
        case Some(i) =>
          demoted += i
          if (proofHoleIndexes(i)) remainingProofHoles -= 1
          queue.append((i, Vector(Step.Tpe), binders(i).fresh.tpe))
          drain()
        case None => more = false
      }
    }
    binders.zipWithIndex.map { case (b, i) =>
      if (!b.isImplicit || demoted(i)) BinderResult(false, None)
      else
        solved.get(i) match {
          case Some((root, path)) =>
            BinderResult(true, Some(Spec((0 until root).count(j => !binders(j).isImplicit || demoted(j)), path)))
          case None => throw NonForcedImplicitParam(b.name, Some(b.span))
        }
    }
  }

  private def independentPiDomain(pi: VPi, idx: Int): Option[Value] = {
    val env = BinderOps.freshen(pi.binders.take(idx), pi.env)
    val ids = Value.envDeps(env) -- Value.envDeps(pi.env)
    val domain = Interpreter.evalTerm(pi.binders(idx).ty, env)
    Option.when(!domain.synDeps.intersects(ids))(domain)
  }
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
      else
        Some(
          pi.copy(
            env = firstEnv,
            binders = remaining,
            synDeps = pi.synDeps,
            classifier0 = () => Interpreter.piClassifierFromChecked(remaining, fullEnv, out)
          )
        )
    }
  }
  private def independentPiResult(pi: VPi): Option[Value] = {
    val env = BinderOps.freshen(pi)
    val ids = Value.envDeps(env) -- Value.envDeps(pi.env)
    val out = pi.codomain(env)
    Option.when(!out.synDeps.intersects(ids))(out)
  }

  def project(spec: Spec, args: Vector[Value]): Either[String, Value] = {
    if (spec.rootArgIdx >= args.length)
      return Left(s"projection root ${spec.rootArgIdx} out of range (${args.length} args)")
    def asLevel(v: Value): Either[String, Level] = Level.fromValue(v).toRight(s"expected a level, got $v")
    spec.steps.foldLeft[Either[String, Value]](Right(args(spec.rootArgIdx))) {
      case (left @ Left(_), _) => left
      case (Right(v), step) =>
        step match {
          case Step.Tpe => Right(v.tpe)
          case Step.SpineArg(h, i) =>
            v match {
              case ConstSpine(c, as) if c.name == h && i < as.length => Right(as(i));
              case x                                                 => Left(s"expected an application of $h, got $x")
            }
          case Step.CtorField(c, i) =>
            v match {
              case ConstructorForm(name, fs) if name == c && i < fs.length => Right(fs(i));
              case packed: VPacked =>
                val (name, fs) = packed.codec.decodeHead(packed)
                if (name == c && i < fs.length) Right(fs(i)) else Left(s"expected a $c value, got $v")
              case x => Left(s"expected a $c value, got $x")
            }
          case Step.SortLevel => v match { case VSort(l) => Right(l); case x => Left(s"expected a sort, got $x") }
          case Step.LevelOffset(k) =>
            asLevel(v).flatMap(l =>
              if (k == 0) Right(l)
              else if (Level.geq(l, k)) Right(Level.addOffset(l, -k))
              else Left(s"level $l does not cover offset $k")
            )
          case Step.PiDomain(i) =>
            v match {
              case pi: VPi if i < pi.binders.length =>
                independentPiDomain(pi, i).toRight(s"domain $i depends on earlier binders");
              case x => Left(s"expected a function type, got $x")
            }
          case Step.PiCodomain =>
            v match {
              case pi: VPi => independentPiCodomain(pi).toRight(s"codomain depends on its binders");
              case x       => Left(s"expected a function type, got $x")
            }
          case Step.PiResult =>
            v match {
              case pi: VPi => independentPiResult(pi).toRight(s"result depends on its binders");
              case x       => Left(s"expected a function type, got $x")
            }
        }
    }
  }
}
