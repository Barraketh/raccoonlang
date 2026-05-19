package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Interpreter.Worlds
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

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
      case VBlockedApp(h, args, _, _) => collectBlocked(h, args ++ acc)
      case h                          => (h, acc)
    }

  private def occursInductive(v: Value, inductiveHead: VConst)(implicit
      eqStore: EqStore
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
        val freshEnv = BinderOps.freshen(pi)
        val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
        val allTypes = freshArgs.map(_.tpe) :+ pi.codomain(freshEnv, eqStore)
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
      eqStore: EqStore
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
        val freshEnv = BinderOps.freshen(pi)
        val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
        !freshArgs.exists(v => occursInductive(v.tpe, inductiveHead)) &&
        isStrictlyPositive(pi.codomain(freshEnv, eqStore), inductiveHead)
      case VApp(_, args, _) =>
        // For any head F (including the inductive), reject if I occurs in any argument.
        !args.exists(arg => occursInductive(arg, inductiveHead))

      case _: ConstructorHead | _: VCtor => true
      case _: Level | LevelTpe | _: Normalizer | NormalizerType | _: VLam | _: VSort | _: Var | _: VConst | PropTpe |
          KernelObject =>
        true
    }

  private def installInductive(
      decl: Decl.InductiveDecl,
      baseEnv: TypecheckEnv,
      inductiveHead: VConst,
      isStruct: Boolean
  )(implicit
      eqStore: EqStore
  ): TypecheckEnv = {
    val envWithInductive = baseEnv.putGlobal(decl.header.name, inductiveHead)

    decl.ctors.foldLeft(envWithInductive) { case (curEnv, ctor) =>
      val allBinders = ctor.erasedBinders ++ ctor.fields
      val fullTypeTerm =
        if (allBinders.isEmpty) ctor.resultTy
        else Term.Pi(allBinders, ctor.resultTy, ctor.span)

      val fullType = TypeChecker.getType(fullTypeTerm, curEnv)

      curEnv.putGlobal(
        ctor.canonicalName,
        ConstructorHead(ctor.canonicalName, ctor.erasedBinders.length, allBinders.length, fullType, isStruct)
      )
    }
  }

  def evalInductiveDecl(decl: Decl.InductiveDecl, worlds: Worlds): Worlds = {
    implicit val eqStore: EqStore = EqStore.empty

    // All direct Value matches in this function and its private helpers
    // rely on EqStore.empty: no Vars are solved in this pass.

    val header = decl.header
    val name = header.name
    val ty = {
      if (header.binders.isEmpty) decl.header.resultTy
      else Term.Pi(header.binders, decl.header.resultTy, decl.header.span)
    }

    val checkedInductiveType = TypeChecker.getCheckedType(ty, worlds.checkEnv)
    val inductiveTypeCheck = checkedInductiveType.value
    val inductiveTypeRun = Interpreter.evalTypeTerm(checkedInductiveType.term, worlds.runEnv)

    val meta =
      InductiveMeta(
        decl.ctors.map(ctor => ConstructorMeta(ctor.shortName, ctor.canonicalName)),
        decl.header.binders.length,
        decl.isStruct
      )

    val inductivedHead = VConst(name, Inductive(meta), inductiveTypeCheck)

    val checkEnvWithInductive = worlds.checkEnv.putGlobal(name, inductivedHead)
    val envWithFamilyBinders = {
      inductiveTypeCheck match {
        case pi: VPi =>
          assert(checkEnvWithInductive.locals.isEmpty) // Sanity check
          BinderOps.freshen(pi.binders, checkEnvWithInductive)
        case _ => checkEnvWithInductive
      }
    }

    val resTpe = TypeChecker.getType(header.resultTy, envWithFamilyBinders)
    val familyUniverse: Universe = resTpe match {
      case v: VSort => v
      case other    => throw InductiveTypeNotASort(other, Some(header.resultTy.span))
    }

    // Determine whether this inductive is a valid struct (after computing universe)
    if (decl.isStruct) {
      if (decl.ctors.length != 1)
        throw InvalidStruct(name, s"has ${decl.ctors.length} constructors (expected exactly 1)", Some(header.span))
      if (decl.ctors.head.fields.exists(_.name == "_"))
        throw InvalidStruct(name, "constructor has anonymous '_' fields", Some(header.span))

    }

    decl.ctors.foreach { ctor =>
      val (erasedBinders, _) = BinderOps.toVBinders(ctor.erasedBinders, checkEnvWithInductive)
      val envWithErased = BinderOps.freshen(erasedBinders, checkEnvWithInductive)
      val erasedDeps = envWithErased.allDeps
      val (fieldBinders, _) = BinderOps.toVBinders(ctor.fields, envWithErased)
      val fieldsEnv = BinderOps.freshen(fieldBinders, envWithErased)
      val fieldVars = fieldBinders.map(binder => fieldsEnv(binder.localRef))

      val outputTpe = TypeChecker.getType(ctor.resultTy, fieldsEnv)

      // 4) Constructor result must be the inductive family head applied to the full family arity.
      val resultErr = InvalidConstructorResult(ctor.canonicalName, name, outputTpe, Some(ctor.span))
      val outputArgs = outputTpe match {
        case VApp(h, args, _) if h.name == name => args
        case VConst(n, _, _) if n == name       => Vector.empty[Value]
        case _                                  => throw resultErr
      }

      if (outputArgs.length != header.arity) throw resultErr

      val constructorUniverse = TypeChecker.getUniverse(outputTpe)

      ctor.fields.zip(fieldVars).foreach { case (binder, field) =>
        // 2) Universe bound: skip for Prop families; enforce for Sort families
        constructorUniverse match {
          case PropTpe => // no universe restriction
          case VSort(inductiveLevel) =>
            TypeChecker.getUniverse(field.tpe) match {
              case Value.PropTpe =>

              case VSort(tpeLevel) =>
                if (!Level.leq(tpeLevel, inductiveLevel))
                  throw InductiveUniverseTooSmall(
                    name,
                    s"${ctor.canonicalName}.${binder.name}",
                    field.tpe,
                    tpeLevel,
                    inductiveLevel,
                    Some(binder.span)
                  )
            }
        }

        // 3) Every stored constructor field type must be strictly positive in the inductive
        if (!isStrictlyPositive(field.tpe, inductivedHead))
          throw NonStrictlyPositive(
            inductive = name,
            ctor = ctor.canonicalName,
            field = binder.name,
            fieldTy = field.tpe,
            span = Some(binder.span)
          )
      }

      if (decl.isStruct) {
        val invalidArg = header.binders.zip(outputArgs).find { case (_, familyArg) =>
          (familyArg.synDeps -- erasedDeps).nonEmpty
        }

        invalidArg.foreach { case (familyBinder, _) =>
          throw InvalidStruct(
            name,
            s"constructor result family argument ${familyBinder.name} depends on constructor fields",
            Some(ctor.resultTy.span)
          )
        }
      }

    }

    val inductiveHeadCheck = VConst(name, Inductive(meta), inductiveTypeCheck)
    val inductiveHeadRun = VConst(name, Inductive(meta), inductiveTypeRun)

    // Only after all constructor checks succeed do we add the decl to the environments.
    val nextCheckEnv = installInductive(decl, worlds.checkEnv, inductiveHeadCheck, decl.isStruct)
    val nextRunEnv = installInductive(decl, worlds.runEnv, inductiveHeadRun, decl.isStruct)

    Worlds(nextCheckEnv, nextRunEnv)
  }
}
