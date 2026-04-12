package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Interpreter.Worlds
import com.raccoonlang.Util.NEL
import com.raccoonlang.Value._

import scala.annotation.tailrec

object InductiveChecks {

  // ------------ Occurrence and Positivity ------------

  private def sameInductiveHead(v: Value, inductiveHead: VConst): Boolean =
    v match {
      case VConst(name, Inductive(_), _) => name == inductiveHead.name
      case _                             => false
    }

  @tailrec
  private def collectBlocked(v: Value, acc: Vector[Value] = Vector.empty): (Value, Vector[Value]) =
    v match {
      case VBlockedApp(h, args, _, _) => collectBlocked(h, args.toVector ++ acc)
      case h                          => (h, acc)
    }

  private def occursInductive(v: Value, inductiveHead: VConst)(implicit
      eqStore: EqStore,
      normalizers: NormalizerMap
  ): Boolean =
    v match {
      // Be conservative: blocked types may hide an occurrence
      case _: VBlockedThunk => true

      case vb @ VBlockedApp(_, _, resultTy, _) =>
        val (head0, flatArgs) = collectBlocked(vb)
        head0 match {
          case _: Var =>
            flatArgs.exists(arg => occursInductive(arg, inductiveHead)) || occursInductive(resultTy, inductiveHead)
          case _ => true
        }

      case h: VConst => sameInductiveHead(h, inductiveHead)
      case VApp(h, args, _) =>
        sameInductiveHead(h, inductiveHead) || args.exists(arg => occursInductive(arg, inductiveHead))
      case pi: VPi =>
        val (binderVars, bodyEnv, _) = FreshVar.assignFreshVars(pi, eqStore)
        val allTypes = binderVars.map(_.tpe) :+ pi.codomain(bodyEnv, eqStore)
        allTypes.exists(v => occursInductive(v, inductiveHead))

      case _: ConstructorHead | _: VCtor => false
      case _: Level | LevelTpe | _: Normalizer | NormalizerType | _: VLam | _: VSort | _: Var | PropTpe |
          KernelObject =>
        false
    }

  // Conservative strict positivity:
  // - in Pi(x : A) -> B, the inductive may not occur in A, and must be strictly positive in B
  // - a direct recursive occurrence I args is allowed, provided I does not occur in the args
  // - under any other type constructor application F args, recursive occurrence in args is rejected
  @tailrec
  private def isStrictlyPositive(v: Value, inductiveHead: VConst)(implicit
      eqStore: EqStore,
      normalizer: NormalizerMap
  ): Boolean =
    v match {
      // Be conservative: blocked shapes are not strictly positive
      case _: VBlockedThunk => false

      case vb @ VBlockedApp(_, _, resultTy, _) =>
        val (head0, flatArgs) = collectBlocked(vb)
        head0 match {
          case _: Var =>
            !flatArgs.exists(arg => occursInductive(arg, inductiveHead)) && isStrictlyPositive(resultTy, inductiveHead)
          case _ => false
        }

      case pi: VPi =>
        val (binderVars, bodyEnv, _) = FreshVar.assignFreshVars(pi, eqStore)
        !binderVars.exists(v => occursInductive(v.tpe, inductiveHead)) && isStrictlyPositive(
          pi.codomain(bodyEnv, eqStore),
          inductiveHead
        )
      case VApp(_, args, _) =>
        // For any head F (including the inductive), reject if I occurs in any argument.
        !args.exists(arg => occursInductive(arg, inductiveHead))

      case _: ConstructorHead | _: VCtor => true
      case _: Level | LevelTpe | _: Normalizer | NormalizerType | _: VLam | _: VSort | _: Var | _: VConst | PropTpe |
          KernelObject =>
        true
    }

  private def installInductive(decl: Decl.InductiveDecl, baseEnv: Env, inductiveHead: VConst)(implicit
      eqStore: EqStore,
      normalizerMap: NormalizerMap
  ): Env = {
    val envWithInductive = baseEnv.putGlobal(decl.header.name, inductiveHead)

    decl.ctors.foldLeft(envWithInductive) { case (curEnv, ctor) =>
      val allBinders = decl.header.params ++ ctor.fields
      val fullTypeTerm =
        if (allBinders.isEmpty) ctor.resultTy
        else Term.Pi(NEL.mk(allBinders), ctor.resultTy, ctor.span)

      val fullType = TypeChecker.getType(fullTypeTerm, envWithInductive)

      curEnv.putGlobal(
        ctor.name,
        ConstructorHead(ctor.name, decl.header.params.length, allBinders.length, fullType)
      )
    }
  }

  def evalInductiveDecl(decl: Decl.InductiveDecl, worlds: Worlds): Worlds = {
    implicit val eqStore: EqStore = EqStore.empty
    implicit val normalizers: NormalizerMap = NormalizerMap.empty

    val ty = {
      val binders = decl.header.params ++ decl.header.indices
      if (binders.isEmpty) decl.header.resultTy
      else Term.Pi(NEL.mk(binders), decl.header.resultTy, decl.header.span)
    }

    val inductiveTypeCheck = TypeChecker.getType(ty, worlds.checkEnv)
    val inductiveTypeRun = Interpreter.evalTypeTerm(ty, worlds.runEnv)

    val meta = InductiveMeta(decl.ctors.map(_.name), decl.header.params.length, decl.header.indices.length)

    val inductiveHeadCheck = VConst(decl.header.name, Inductive(meta), inductiveTypeCheck)
    val inductiveHeadRun = VConst(decl.header.name, Inductive(meta), inductiveTypeRun)

    // Constructors are checked in an environment that contains the inductive and inductive params assigned
    val checkEnvWithInductive = worlds.checkEnv.putGlobal(decl.header.name, inductiveHeadCheck)
    val (paramVars, envWithParams, _) = FreshVar.assignFreshVars(decl.header.params, checkEnvWithInductive, eqStore)

    val resTpe = TypeChecker.getType(decl.header.resultTy, envWithParams)
    val familyUniverse: Universe = resTpe match {
      case v: VSort => v
      case PropTpe  => PropTpe
      case other    => throw InductiveTypeNotASort(other, Some(decl.header.resultTy.span))
    }

    decl.ctors.foreach { ctor =>
      val outputTpe = {
        val (fieldVars, bodyEnv, _) = FreshVar.assignFreshVars(ctor.fields, envWithParams, eqStore)

        fieldVars.zipWithIndex.foreach { case (field, idx) =>
          val binder = ctor.fields(idx)

          // 2) Universe bound: skip for Prop families; enforce for Sort families
          familyUniverse match {
            case VSort(inductiveLevel) =>
              TypeChecker.getUniverse(field.tpe) match {
                case VSort(tpeLevel) =>
                  if (!Level.leq(tpeLevel, inductiveLevel))
                    throw InductiveUniverseTooSmall(
                      decl.header.name,
                      s"${ctor.name}.${binder.name}",
                      field.tpe,
                      tpeLevel,
                      inductiveLevel,
                      Some(binder.span)
                    )
                case Value.PropTpe =>
              }

            case PropTpe => // no universe restriction
          }

          // 3) Every constructor field type must be strictly positive in the inductive
          if (!isStrictlyPositive(field.tpe, inductiveHeadCheck))
            throw NonStrictlyPositive(
              inductive = inductiveHeadCheck.name,
              ctor = ctor.name,
              field = binder.name,
              fieldTy = field.tpe,
              span = Some(binder.span)
            )
        }

        Interpreter.evalTypeTerm(ctor.resultTy, bodyEnv)
      }

      // 4) Constructor result must be the inductive family head applied to the full family arity,
      // and params must be uniform - must equal to the original paramVars
      val resultErr = InvalidConstructorResult(ctor.name, decl.header.name, outputTpe, Some(ctor.span))
      val outputArgs = outputTpe match {
        case VApp(h, args, _) if h.name == inductiveHeadCheck.name => args.toVector
        case VConst(name, _, _) if name == inductiveHeadCheck.name => Vector.empty[Value]
        case _                                                     => throw resultErr
      }

      if (outputArgs.length != decl.header.arity) throw resultErr

      outputArgs.take(paramVars.length).zip(paramVars).foreach { case (arg, paramVar) =>
        if (!TypeChecker.defEq(arg, paramVar)) throw resultErr
      }

    }

    // Only after all constructor checks succeed do we add the decl to the environments.
    val nextCheckEnv = installInductive(decl, worlds.checkEnv, inductiveHeadCheck)
    val nextRunEnv = installInductive(decl, worlds.runEnv, inductiveHeadRun)

    Worlds(nextCheckEnv, nextRunEnv)
  }
}
