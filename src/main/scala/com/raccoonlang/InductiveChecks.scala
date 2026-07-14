package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Interpreter.Worlds
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

object InductiveChecks {

  // ------------ Occurrence and Positivity ------------

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
          // A lambda's body (and a thunk's code) can mention the inductive without it showing
          // anywhere the traversal looks; be conservative. The surface grammar cannot currently
          // place a lambda in a field type, but that must not be what soundness rests on.
          case _: NeutralThunk => true
          case _: VLam         => true
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

        case app: VApp =>
          doesNotOccur(target, app.head) &&
          app.args.forall(arg => doesNotOccur(target, arg)) &&
          doesNotOccur(target, app.tpe)

        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
          freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
          doesNotOccur(target, pi.codomain(freshEnv))

        // A proof's interior is erased; its type is all that can carry an occurrence.
        case p: VProof => doesNotOccur(target, p.tpe)

        case _: ConstructorHead => !target.mayOccurIn(value)

        case _: Level | LevelTpe | _: VLam | _: VSort | _: Var | _: VConst | PropTpe =>
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

        case app: VApp =>
          doesNotOccur(target, app.head) &&
          app.args.forall(arg => doesNotOccur(target, arg)) &&
          occursPositively(target, app.tpe)

        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
          freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
          occursPositively(target, pi.codomain(freshEnv))

        // Strict: a proof value embedded in a type (e.g. an index) must not mention the target in
        // its proposition at all — positivity through an erased interior is unjustifiable.
        case p: VProof => doesNotOccur(target, p.tpe)

        case _: ConstructorHead => true

        case _: Level | LevelTpe | _: VLam | _: VSort | _: Var | _: VConst =>
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

      case app: VApp =>
        doesNotOccur(target, app.head) &&
        app.args.forall(arg => sameFamilyArgsDoNotContain(inductiveName, target, arg)) &&
        sameFamilyArgsDoNotContain(inductiveName, target, app.tpe)

      case pi: VPi =>
        val freshEnv = BinderOps.freshen(pi)
        val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
        freshArgs.forall(arg => sameFamilyArgsDoNotContain(inductiveName, target, arg.tpe)) &&
        sameFamilyArgsDoNotContain(inductiveName, target, pi.codomain(freshEnv))

      case p: VProof => sameFamilyArgsDoNotContain(inductiveName, target, p.tpe)

      case _: ConstructorHead | _: Level | LevelTpe | _: VLam | _: VSort | _: Var | _: VConst =>
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

  private def constructorFamilyParams(header: InductiveHeader): Vector[Binder] =
    header.params.map(_.copy(isImplicit = true, isInstance = false))

  private def constructorBinders(header: InductiveHeader, ctor: ConstructorDecl): Vector[Binder] =
    constructorFamilyParams(header) ++ ctor.binders

  private def installInductive(
      decl: Decl.InductiveDecl,
      baseContext: TypingContext,
      inductiveHead: VConst
  ): TypingContext = {
    val contextWithInductive = baseContext.putGlobal(decl.header.name, inductiveHead)

    decl.ctors.foldLeft(contextWithInductive) { case (curContext, ctor) =>
      val allBinders = constructorBinders(decl.header, ctor)
      val fullTypeTerm =
        if (allBinders.isEmpty) ctor.resultTy
        else Term.Pi(allBinders, ctor.resultTy, ctor.span)

      val fullType = TypeChecker.getConstructorType(fullTypeTerm, curContext, decl.header.params.length)
      curContext.putGlobal(
        ctor.canonicalName,
        ConstructorHead(ctor.canonicalName, decl.header.params.length, allBinders.length, fullType)
      )
    }
  }

  private def checkConstructorParamDiscipline(
      header: InductiveHeader,
      ctor: ConstructorDecl,
      envWithBinders: Env[Value],
      outputArgs: Vector[Value]
  ): Unit =
    header.params.zipWithIndex.foreach { case (param, idx) =>
      val paramValue = envWithBinders(param.localRef)
      val outputArg = outputArgs(idx)
      val error =
        NonUniformInductiveParam(header.name, ctor.canonicalName, param.name, outputArg, Some(ctor.resultTy.span))

      if (!ValueEquivalence.defEq(outputArg, paramValue))
        throw error
    }

  def evalInductiveDecl(decl: Decl.InductiveDecl, worlds: Worlds): Worlds = {
    // All direct Value matches in this function and its private helpers
    // rely on EqStore.empty: no Vars are solved in this pass.

    val header = decl.header
    val name = header.name
    rejectInstanceFamilyParams(header)
    val ty = {
      if (header.binders.isEmpty) decl.header.resultTy
      else Term.Pi(header.binders, decl.header.resultTy, decl.header.span)
    }

    val inductiveTypeCheck = TypeChecker.getType(ty, worlds.checkContext)
    val inductiveTypeRun = TypeChecker.getType(ty, worlds.runContext)

    val initialPositiveArgs = DepSet.from(0 until header.arity)
    val initialMeta =
      InductiveMeta(
        decl.ctors.map(ctor => ConstructorMeta(ctor.shortName, ctor.canonicalName)),
        decl.header.binders.length,
        decl.isStruct,
        initialPositiveArgs
      )

    val inductivedHead = VConst(name, Inductive(initialMeta), inductiveTypeCheck)

    val checkContextWithInductive = worlds.checkContext.putGlobal(name, inductivedHead)
    val contextWithFamilyBinders = {
      inductiveTypeCheck match {
        case pi: VPi =>
          assert(checkContextWithInductive.env.locals.isEmpty) // Sanity check
          BinderOps.freshen(pi.binders, checkContextWithInductive)
        case _ => checkContextWithInductive
      }
    }
    val envWithFamilyBinders = contextWithFamilyBinders.env

    TypeChecker.getType(header.resultTy, contextWithFamilyBinders) match {
      case v: VSort => v
      case other    => throw InductiveTypeNotASort(other, Some(header.resultTy.span))
    }

    // Determine whether this inductive is a valid struct (after computing universe)
    if (decl.isStruct) {
      if (decl.ctors.length != 1)
        throw InvalidStruct(name, s"has ${decl.ctors.length} constructors (expected exactly 1)", Some(header.span))
      if (decl.ctors.head.binders.exists(_.name == "_"))
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
      val allConstructorBinders = constructorBinders(header, ctor)
      val checkedBinders =
        BinderOps.toVBinders(allConstructorBinders, checkContextWithInductive, familyParams = header.params.length)
      val binders = checkedBinders.vBinders
      val contextWithBinders = checkedBinders.context
      val envWithBinders = contextWithBinders.env
      val binderVars = binders.map(binder => envWithBinders(binder.localRef))
      val ownBinderVars = binderVars.drop(header.params.length)

      val outputTpe = TypeChecker.getType(ctor.resultTy, contextWithBinders)

      // 4) Constructor result must be the inductive family head applied to the full family arity.
      val resultErr = InvalidConstructorResult(ctor.canonicalName, name, outputTpe, Some(ctor.span))
      val outputArgs = outputTpe match {
        case ConstSpine(head, args) if head.name == name => args
        case _                                           => throw resultErr
      }

      if (outputArgs.length != header.arity) throw resultErr

      checkConstructorParamDiscipline(header, ctor, envWithBinders, outputArgs)

      val constructorUniverse = TypeChecker.getUniverse(outputTpe)
      val constructorArgs = ctor.binders.zip(ownBinderVars)
      val constructorArgTypes = constructorArgs.map(_._2.tpe)

      constructorArgs.foreach { case (binder, field) =>
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

      positiveArgs = positiveArgs & positiveArgIndexes(outputArgs, constructorArgTypes)

    }

    val meta = initialMeta.copy(positiveArgs = positiveArgs)

    val inductiveHeadCheck = VConst(name, Inductive(meta), inductiveTypeCheck)
    val inductiveHeadRun = VConst(name, Inductive(meta), inductiveTypeRun)

    // Only after all constructor checks succeed do we add the decl to the environments.
    val nextCheckContext = installInductive(decl, worlds.checkContext, inductiveHeadCheck)
    val nextRunContext = installInductive(decl, worlds.runContext, inductiveHeadRun)

    // Demotion (forced-vs-unforced) is recomputed per world from world-local values, and the
    // residual/value contract requires both worlds to agree on every constructor's arity. The
    // computation is deterministic on structurally equal telescopes, so a mismatch here means a
    // cross-world value divergence upstream — fail loudly instead of misapplying residuals later.
    def implicitFlags(context: TypingContext, ctorName: String): Vector[Boolean] =
      context.env(ctorName) match {
        case head: ConstructorHead =>
          head.tpe match {
            case pi: VPi => pi.binders.map(_.isImplicit)
            case _       => Vector.empty
          }
        case _ => Vector.empty
      }
    decl.ctors.foreach { ctor =>
      if (implicitFlags(nextCheckContext, ctor.canonicalName) != implicitFlags(nextRunContext, ctor.canonicalName))
        throw WTF(
          s"Constructor ${ctor.canonicalName}: implicit telescopes disagree between check and run worlds",
          Some(ctor.span)
        )
    }

    Worlds(nextCheckContext, nextRunContext)
  }

  private def rejectInstanceFamilyParams(header: InductiveHeader): Unit =
    header.params.find(_.isInstance).foreach { binder =>
      throw InvalidInductiveParam(
        header.name,
        binder.name,
        "family parameters may be explicit or implicit, but not instance binders",
        Some(binder.span)
      )
    }
}
