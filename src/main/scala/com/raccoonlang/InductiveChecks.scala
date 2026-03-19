package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Value._

object InductiveChecks {

  // ------------ Occurrence and Positivity ------------

  private def sameInductiveHead(v: Value, inductiveHead: VConst): Boolean =
    v match {
      case VConst(name, Inductive(_), _) => name == inductiveHead.name
      case _                             => false
    }

  private def occursInductive(v: Value, inductiveHead: VConst)(implicit eqStore: EqStore): Boolean =
    v match {
      case _: Blocked => true // Be conservative: blocked types may hide an occurrence
      case _: VMatch  => true

      case h: VConst => sameInductiveHead(h, inductiveHead)
      case VApp(h, args, _) =>
        sameInductiveHead(h, inductiveHead) || args.exists(arg => occursInductive(arg, inductiveHead))
      case pi: VPi =>
        val (binderVars, bodyEnv) = FreshVar.assignFreshVars(pi, eqStore)
        val allTypes = binderVars.map(_.tpe) :+ Interpreter.evalTerm(pi.out, bodyEnv)
        allTypes.exists(v => occursInductive(v, inductiveHead))

      case _: Level | LevelTpe | _: Normalizer | NormalizerType | _: VLam | _: VSort | _: Var => false
    }

  // Conservative strict positivity:
  // - in Pi(x : A) -> B, the inductive may not occur in A, and must be strictly positive in B
  // - a direct recursive occurrence I args is allowed, provided I does not occur in the args
  // - under any other type constructor application F args, recursive occurrence in args is rejected
  private def isStrictlyPositive(v: Value, inductiveHead: VConst)(implicit eqStore: EqStore): Boolean =
    v match {
      case _: Blocked => false // Be conservative: blocked shapes are not strictly positive
      case _: VMatch  => false

      case pi: VPi =>
        val (binderVars, bodyEnv) = FreshVar.assignFreshVars(pi, eqStore)
        !binderVars.exists(v => occursInductive(v.tpe, inductiveHead)) && isStrictlyPositive(
          Interpreter.evalTerm(pi.out, bodyEnv),
          inductiveHead
        )
      case VApp(_, args, _) =>
        // For any head F (including the inductive), reject if I occurs in any argument.
        !args.exists(arg => occursInductive(arg, inductiveHead))

      case _: Level | LevelTpe | _: Normalizer | NormalizerType | _: VLam | _: VSort | _: Var | _: VConst => true
    }

  private def sortLevelOfType(v: Value): Level =
    v.tpe match {
      case VSort(u) => u
      case other    => throw WTF(s"Expected a type with a sort, got $v : $other")
    }

  def evalInductiveDecl(decl: Decl.InductiveDecl, env: Env): Env = {
    implicit val eqStore: EqStore = EqStore.empty
    implicit val normalizers: NormalizerMap = NormalizerMap.empty

    val inductiveType = TypeChecker.getType(decl.ty, env)

    val inductiveLevel = {
      val outTpe = inductiveType match {
        case pi: VPi =>
          val (_, bodyEnv) = FreshVar.assignFreshVars(pi, eqStore)
          Interpreter.evalTerm(pi.out, bodyEnv)
        case other => other
      }
      outTpe match {
        case VSort(u) => u
        case other    => throw InductiveTypeNotASort(other, Some(decl.ty.span))
      }
    }

    val inductiveHead = VConst(decl.name, Inductive(decl.ctors.map(_.name)), inductiveType)

    // Constructors are checked in an environment that contains the inductive
    // but not the other constructors.
    val envWithInductive = env.putGlobal(decl.name, inductiveHead)

    decl.ctors.foreach { ctor =>
      // 1) Constructor as a whole must still be a valid type
      val ctorTy = TypeChecker.getType(ctor.ty, envWithInductive)

      val outputTpe = ctorTy match {
        case pi: VPi =>
          val (fields, bodyEnv) = FreshVar.assignFreshVars(pi, eqStore)

          fields.zipWithIndex.foreach { case (field, idx) =>
            val binder = pi.binders(idx)

            // 2) Every constructor field type must live in a sort <= the inductive sort
            val tpeLevel = sortLevelOfType(field.tpe)
            if (!Level.leq(tpeLevel, inductiveLevel))
              throw InductiveUniverseTooSmall(
                decl.name,
                s"${ctor.name}.${binder.name}",
                field.tpe,
                tpeLevel,
                inductiveLevel,
                Some(binder.span)
              )

            // 3) Every constructor field type must be strictly positive in the inductive
            if (!isStrictlyPositive(field.tpe, inductiveHead))
              throw NonStrictlyPositive(
                inductive = inductiveHead.name,
                ctor = ctor.name,
                field = binder.name,
                fieldTy = field.tpe,
                span = Some(binder.span)
              )
          }

          Interpreter.evalTerm(pi.out, bodyEnv)
        case other => other
      }

      // 4) Constructor result must be the inductive family head applied to the full family arity
      (inductiveType, outputTpe) match {
        case (_: VPi, VApp(h, _, _)) if h.name == inductiveHead.name =>
        case (_, VConst(name, _, _)) if name == inductiveHead.name   =>
        case (_, other) => throw InvalidConstructorResult(ctor.name, decl.name, other, Some(ctor.span))
      }
    }

    // Only after all constructor checks succeed do we add the constructors to the environment.
    decl.ctors.foldLeft(envWithInductive) { case (curEnv, ctor) =>
      val ctorTy = TypeChecker.getType(ctor.ty, envWithInductive)
      curEnv.putGlobal(ctor.name, VConst(ctor.name, ConstructorHead, ctorTy))
    }
  }
}
