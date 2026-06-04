package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Interpreter.Worlds
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

object InductiveChecks {

  // ------------ Occurrence and Positivity ------------

  private final case class InductiveFamilyInstance(head: VConst, meta: InductiveMeta, args: Vector[Value])

  private object InductiveFamilyValue {
    def unapply(value: Value): Option[InductiveFamilyInstance] =
      value match {
        case c @ VConst(_, Inductive(meta), _) if meta.familyArity == 0 =>
          Some(InductiveFamilyInstance(c, meta, Vector.empty))
        case VApp(c @ VConst(_, Inductive(meta), _), args, _) if args.length == meta.familyArity =>
          Some(InductiveFamilyInstance(c, meta, args))
        case _ => None
      }
  }

  // A positivity target is the thing whose occurrences we are checking.
  // The traversal only needs two queries:
  //
  // - isDirectOccurrence identifies a value that is exactly the target.
  // - mayOccurIn is the conservative fallback for values we do not inspect
  //   structurally, such as neutral computations and opaque leaves.
  private sealed trait PositivityTarget {
    def isDirectOccurrence(value: Value): Boolean
    def mayOccurIn(value: Value): Boolean
  }

  private object PositivityTarget {
    final case class InductiveHead(name: String) extends PositivityTarget {
      override def isDirectOccurrence(value: Value): Boolean =
        value match {
          case VConst(valueName, Inductive(_), _) => valueName == name
          case _                                  => false
        }

      override def mayOccurIn(value: Value): Boolean =
        value match {
          case _: NeutralThunk => true
          case _               => false
        }
    }

    final case class LocalVar(id: VarId) extends PositivityTarget {
      override def isDirectOccurrence(value: Value): Boolean =
        value match {
          case Var(_, valueId, _) => valueId == id
          case _                  => false
        }

      override def mayOccurIn(value: Value): Boolean = value.synDeps.contains(id)
    }
  }

  private def doesNotOccur(target: PositivityTarget, value: Value): Boolean =
    if (target.isDirectOccurrence(value)) false
    else
      value match {
        case _: NeutralThunk => !target.mayOccurIn(value)

        case InductiveFamilyValue(instance) =>
          if (target.isDirectOccurrence(instance.head)) false
          else instance.args.forall(arg => doesNotOccur(target, arg))

        case app: AppliedValue =>
          doesNotOccur(target, app.head) &&
          app.args.forall(arg => doesNotOccur(target, arg)) &&
          doesNotOccur(target, app.tpe)

        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
          freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
          doesNotOccur(target, pi.codomain(freshEnv))

        case _: ConstructorHead => !target.mayOccurIn(value)

        case _: Level | LevelTpe | _: Normalizer | NormalizerType | _: VLam | _: VSort | _: Var | _: VConst | PropTpe |
            KernelObject =>
          !target.mayOccurIn(value)
      }

  /**
   * Checks that the target only occurs positively in value: 1) Does not occur in the domain of any Pis 2) Only appears
   * in positive args of Inductives
   */
  private def occursPositively(target: PositivityTarget, value: Value): Boolean =
    if (target.isDirectOccurrence(value)) true
    else
      value match {
        case _: NeutralThunk => !target.mayOccurIn(value)

        case InductiveFamilyValue(instance) =>
          if (target.isDirectOccurrence(instance.head)) true
          else
            instance.args.zipWithIndex.forall { case (arg, idx) =>
              if (instance.meta.positiveArgs.contains(idx)) occursPositively(target, arg)
              else doesNotOccur(target, arg)
            }

        case app: AppliedValue =>
          doesNotOccur(target, app.head) &&
          app.args.forall(arg => doesNotOccur(target, arg)) &&
          occursPositively(target, app.tpe)

        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
          freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
          occursPositively(target, pi.codomain(freshEnv))

        case _: ConstructorHead => true

        case _: Level | LevelTpe | _: Normalizer | NormalizerType | _: VLam | _: VSort | _: Var | _: VConst | PropTpe |
            KernelObject =>
          true
      }

  /**
   * Checks that we don't have things of the shape Foo(Foo(A)) as a constructor field of Foo.
   */
  private def sameFamilyArgsDoNotContain(inductiveName: String, target: PositivityTarget, value: Value): Boolean =
    value match {
      case _: NeutralThunk => false

      case InductiveFamilyValue(instance) =>
        if (instance.head.name == inductiveName)
          instance.args.forall(arg => doesNotOccur(target, arg))
        else
          instance.args.forall(arg => sameFamilyArgsDoNotContain(inductiveName, target, arg))

      case app: AppliedValue =>
        doesNotOccur(target, app.head) &&
        app.args.forall(arg => sameFamilyArgsDoNotContain(inductiveName, target, arg)) &&
        sameFamilyArgsDoNotContain(inductiveName, target, app.tpe)

      case pi: VPi =>
        val freshEnv = BinderOps.freshen(pi)
        val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
        freshArgs.forall(arg => sameFamilyArgsDoNotContain(inductiveName, target, arg.tpe)) &&
        sameFamilyArgsDoNotContain(inductiveName, target, pi.codomain(freshEnv))

      case _: ConstructorHead | _: Level | LevelTpe | _: Normalizer | NormalizerType | _: VLam | _: VSort | _: Var |
          _: VConst | PropTpe | KernelObject =>
        true
    }

  private def positiveArgIndexes(args: Vector[Value], values: Vector[Value]): DepSet = {
    val positive = DepSet.newBuilder
    args.zipWithIndex.foreach { case (arg, idx) =>
      arg match {
        case Var(_, id, _) =>
          val target = PositivityTarget.LocalVar(id)
          if (values.forall(value => occursPositively(target, value)))
            positive.add(idx)
        case _ =>
      }
    }
    positive.result()
  }

  private def installInductive(
      decl: Decl.InductiveDecl,
      baseEnv: Env,
      inductiveHead: VConst
  ): Env = {
    val envWithInductive = baseEnv.putGlobal(decl.header.name, inductiveHead)

    decl.ctors.foldLeft(envWithInductive) { case (curEnv, ctor) =>
      val allBinders = ctor.erasedBinders ++ ctor.fields
      val fullTypeTerm =
        if (allBinders.isEmpty) ctor.resultTy
        else Term.Pi(allBinders, ctor.resultTy, ctor.span)

      val fullType = TypeChecker.getType(fullTypeTerm, curEnv)

      curEnv.putGlobal(
        ctor.canonicalName,
        ConstructorHead(ctor.canonicalName, ctor.erasedBinders.length, allBinders.length, fullType)
      )
    }
  }

  def evalInductiveDecl(decl: Decl.InductiveDecl, worlds: Worlds): Worlds = {
    // All direct Value matches in this function and its private helpers
    // rely on EqStore.empty: no Vars are solved in this pass.

    val header = decl.header
    val name = header.name
    val ty = {
      if (header.binders.isEmpty) decl.header.resultTy
      else Term.Pi(header.binders, decl.header.resultTy, decl.header.span)
    }

    val inductiveTypeCheck = TypeChecker.getType(ty, worlds.checkEnv)
    val inductiveTypeRun = TypeChecker.getType(ty, worlds.runEnv)

    val initialPositiveArgs = DepSet.from(0 until header.arity)
    val initialMeta =
      InductiveMeta(
        decl.ctors.map(ctor => ConstructorMeta(ctor.shortName, ctor.canonicalName)),
        decl.header.binders.length,
        decl.isStruct,
        initialPositiveArgs
      )

    val inductivedHead = VConst(name, Inductive(initialMeta), inductiveTypeCheck)

    val checkEnvWithInductive = worlds.checkEnv.putGlobal(name, inductivedHead)
    val envWithFamilyBinders = {
      inductiveTypeCheck match {
        case pi: VPi =>
          assert(checkEnvWithInductive.locals.isEmpty) // Sanity check
          BinderOps.freshen(pi.binders, checkEnvWithInductive)
        case _ => checkEnvWithInductive
      }
    }

    TypeChecker.getType(header.resultTy, envWithFamilyBinders) match {
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

    val recursiveTarget = PositivityTarget.InductiveHead(name)
    val familyArgs =
      inductiveTypeCheck match {
        case pi: VPi => pi.binders.map(binder => envWithFamilyBinders(binder.localRef))
        case _       => Vector.empty[Value]
      }
    var positiveArgs = positiveArgIndexes(familyArgs, familyArgs.map(_.tpe))

    decl.ctors.foreach { ctor =>
      val (erasedBinders, _) = BinderOps.toVBinders(ctor.erasedBinders, checkEnvWithInductive)
      val envWithErased = BinderOps.freshen(erasedBinders, checkEnvWithInductive)
      val (fieldBinders, _) = BinderOps.toVBinders(ctor.fields, envWithErased)
      val fieldsEnv = BinderOps.freshen(fieldBinders, envWithErased)
      val fieldVars = fieldBinders.map(binder => fieldsEnv(binder.localRef))
      val fieldTypes = fieldVars.map(_.tpe)

      val outputTpe = TypeChecker.getType(ctor.resultTy, fieldsEnv)

      // 4) Constructor result must be the inductive family head applied to the full family arity.
      val resultErr = InvalidConstructorResult(ctor.canonicalName, name, outputTpe, Some(ctor.span))
      val outputArgs = outputTpe match {
        case VApp(h, args, _) if h.name == name => args
        case VConst(n, _, _) if n == name       => Vector.empty[Value]
        case _                                  => throw resultErr
      }

      if (outputArgs.length != header.arity) throw resultErr

      // Check param uniformity
      header.params.zip(outputArgs).foreach { case (param, outputArg) =>
        val erasedWitnesses = erasedBinders.collect {
          case binder if binder.name == param.name => envWithErased(binder.localRef)
        }
        val captureWitnesses = fieldBinders.flatMap { binder =>
          binder.captures.collect {
            case capture if capture.localRef.name == param.name => fieldsEnv(capture.localRef)
          }
        }
        val witnesses = erasedWitnesses ++ captureWitnesses
        val error =
          NonUniformInductiveParam(header.name, ctor.canonicalName, param.name, outputArg, Some(ctor.resultTy.span))

        if (witnesses.length != 1) throw error

        if (!ValueEquivalence.defEq(outputArg, witnesses.head, fieldsEnv.normalizers, propIrrelevant = true))
          throw error
      }

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
        if (
          !occursPositively(recursiveTarget, field.tpe) || !sameFamilyArgsDoNotContain(name, recursiveTarget, field.tpe)
        )
          throw NonStrictlyPositive(
            inductive = name,
            ctor = ctor.canonicalName,
            field = binder.name,
            fieldTy = field.tpe,
            span = Some(binder.span)
          )
      }

      positiveArgs = positiveArgs & positiveArgIndexes(outputArgs, fieldTypes)

    }

    val meta = initialMeta.copy(positiveArgs = positiveArgs)

    val inductiveHeadCheck = VConst(name, Inductive(meta), inductiveTypeCheck)
    val inductiveHeadRun = VConst(name, Inductive(meta), inductiveTypeRun)

    // Only after all constructor checks succeed do we add the decl to the environments.
    val nextCheckEnv = installInductive(decl, worlds.checkEnv, inductiveHeadCheck)
    val nextRunEnv = installInductive(decl, worlds.runEnv, inductiveHeadRun)

    Worlds(nextCheckEnv, nextRunEnv)
  }
}
