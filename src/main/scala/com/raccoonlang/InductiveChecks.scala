package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

object InductiveChecks {

  // A family label stores an argument value. A universe argument costs its own
  // level, while a Pi domain costs its full classifier (the function's graph).
  private def familyArgumentLevel(tpe: Value): Level = tpe match {
    case LevelTpe | PropTpe => Level.zero
    case VSort(level)       => level
    case pi: VPi if pi.tpe != PropTpe =>
      val fresh = BinderOps.freshen(pi)
      val domainLevels = pi.binders.map { binder =>
        TypeChecker.getUniverse(fresh(binder.localRef).tpe) match {
          case PropTpe      => Level.zero
          case VSort(level) => level
        }
      }
      Level.max(domainLevels :+ familyArgumentLevel(pi.codomain(fresh)))
    case other =>
      TypeChecker.getUniverse(other) match {
        case PropTpe      => Level.zero
        case VSort(level) => level
      }
  }

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

  private def lambdaDoesNotContain(target: PositivityTarget, lam: VLam): Boolean =
    lam.id match {
      // A global or native function is closed and declared before the family being checked, so it cannot contain the
      // target. Opening a native function on fresh arguments would also return its own stuck application.
      case ValueId.Const(_) => true
      case _                =>
        // A function-valued family argument has no assumed variance. Its type alone
        // cannot reveal occurrences captured in the body, so require absence in
        // both the type and the body opened on fresh arguments. Blocked results use
        // the conservative occurrence rules below, including for named heads that
        // synDeps (which tracks only local variables) cannot detect.
        doesNotOccur(target, lam.tpe) && {
          val fresh = BinderOps.freshen(lam.tpe)
          val args = lam.tpe.binders.map(binder => fresh(binder.localRef))
          doesNotOccur(target, Interpreter.runLam(lam, args))
        }
    }

  /**
   * Whether every part of a word satisfies `part`, in one loop over its tokens: each layer's payloads and the end;
   * except that `positiveType` checks the layers' types instead, the positions where a word is a cons application
   * rather than an argument of one. Consecutive layers usually share one type object, which is checked once.
   */
  private def forallWordParts(word: VWord, part: Value => Boolean, positiveType: Value => Boolean): Boolean = {
    var checkedType: Value = null
    packed.Words.foreach(word)(
      layer = token =>
        (0 until token.payloadWidth).forall(index => part(token.payload(index))) &&
          ((token.tpe eq checkedType) || {
            checkedType = token.tpe
            positiveType(token.tpe)
          }),
      end = token => part(token.value)
    )
  }

  private def doesNotOccur(target: PositivityTarget, value: Value): Boolean =
    if (target.isDirectOccurrence(value)) false
    else
      value match {
        case _: NeutralThunk => !target.mayOccurIn(value)

        case InductiveFamilyValue(instance) =>
          if (target.isDirectOccurrence(instance.head)) false
          else instance.args.forall(arg => doesNotOccur(target, arg))

        // An operand that is a form recurses through this case.
        case poly: VNatPoly => poly.form.operands.forall(operand => doesNotOccur(target, operand))

        // A cons head is closed and has no dependencies, so the target cannot occur in it.
        case word: VWord =>
          def visit(part: Value): Boolean = doesNotOccur(target, part)
          forallWordParts(word, visit, visit)

        case app: VApp =>
          doesNotOccur(target, app.head) &&
          app.args.forall(arg => doesNotOccur(target, arg)) &&
          doesNotOccur(target, app.tpe)

        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
          freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
          doesNotOccur(target, pi.codomain(freshEnv))

        case _: ConstructorHead => !target.mayOccurIn(value)

        case lam: VLam => lambdaDoesNotContain(target, lam)

        case _: Level | LevelTpe | _: VSort | _: Var | _: VConst | PropTpe | KernelObject =>
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

        // Factor bases and symbolic exponents are arguments of Nat operations, which have no positive positions.
        case poly: VNatPoly => doesNotOccur(target, poly)

        // Payloads and the end are arguments of constructors; only the layers' types may contain the target.
        case word: VWord => forallWordParts(word, doesNotOccur(target, _), occursPositively(target, _))

        case app: VApp =>
          doesNotOccur(target, app.head) &&
          app.args.forall(arg => doesNotOccur(target, arg)) &&
          occursPositively(target, app.tpe)

        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
          freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
          occursPositively(target, pi.codomain(freshEnv))

        case _: ConstructorHead => true

        case lam: VLam => lambdaDoesNotContain(target, lam)

        case _: Level | LevelTpe | _: VSort | _: Var | _: VConst | PropTpe | KernelObject =>
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

      case poly: VNatPoly =>
        poly.form.operands.forall(operand => sameFamilyArgsDoNotContain(inductiveName, target, operand))

      case word: VWord =>
        def visit(part: Value): Boolean = sameFamilyArgsDoNotContain(inductiveName, target, part)
        forallWordParts(word, visit, visit)

      case app: VApp =>
        doesNotOccur(target, app.head) &&
        app.args.forall(arg => sameFamilyArgsDoNotContain(inductiveName, target, arg)) &&
        sameFamilyArgsDoNotContain(inductiveName, target, app.tpe)

      case pi: VPi =>
        val freshEnv = BinderOps.freshen(pi)
        val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
        freshArgs.forall(arg => sameFamilyArgsDoNotContain(inductiveName, target, arg.tpe)) &&
        sameFamilyArgsDoNotContain(inductiveName, target, pi.codomain(freshEnv))

      case lam: VLam => lambdaDoesNotContain(target, lam)

      case _: ConstructorHead | _: Level | LevelTpe | _: VSort | _: Var | _: VConst | PropTpe | KernelObject =>
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

  /**
   * How a constructor's stored fields recurse: the indexes of fields whose types mention the family being declared, and
   * whether there is exactly one, whose type is the family applied to its own parameters.
   */
  private final case class ConstructorRecursion(
      ctor: ConstructorDecl,
      recursiveFields: Vector[Int],
      soleFieldIsOwnInstance: Boolean
  )

  /**
   * The cons constructor and its shape, when the declaration is list-shaped: a family without indices whose values live
   * in a universe, other than the kernel's Nat, with at least two constructors, exactly one of which has a recursive
   * field. It has exactly one, whose type is the family applied to its own parameters, not nested in another family or
   * under a binder. Nat has the shape with an empty payload, and keeps its compact successor forms instead.
   */
  private def listShape(
      decl: Decl.InductiveDecl,
      familyUniverse: Universe,
      recursion: Vector[ConstructorRecursion]
  ): Option[(String, ListShape)] =
    if (
      familyUniverse == PropTpe || decl.header.indices.nonEmpty || decl.header.name == Kernel.NatName ||
      decl.ctors.length < 2
    ) None
    else
      recursion.filter(_.recursiveFields.nonEmpty) match {
        case Vector(ConstructorRecursion(ctor, Vector(field), true)) =>
          Some(ctor.canonicalName -> ListShape(field, ctor.fields.length - 1))
        case _ => None
      }

  private def installInductive(
      decl: Decl.InductiveDecl,
      baseEnv: Env,
      inductiveHead: VConst,
      listShape: Option[(String, ListShape)]
  ): Env = {
    val envWithInductive = baseEnv.putGlobal(decl.header.name, inductiveHead)

    decl.ctors.foldLeft(envWithInductive) { case (curEnv, ctor) =>
      val allBinders = ctor.erasedBinders ++ ctor.fields
      val fullTypeTerm =
        if (allBinders.isEmpty) ctor.resultTy
        else Term.Pi(allBinders, ctor.resultTy, ctor.span, NodeId.fresh())

      val fullType = TypeChecker.getType(fullTypeTerm, curEnv)
      val erasedFamilyArgIndexes = ctor.erasedBinders.map { binder =>
        val idx = decl.header.params.indexWhere(_.name == binder.name)
        if (idx < 0) throw InvalidErasedConstructorBinder(ctor.canonicalName, binder.name, "expected inductive param")
        idx
      }

      curEnv.putGlobal(
        ctor.canonicalName,
        ConstructorHead(
          ctor.canonicalName,
          erasedFamilyArgIndexes,
          allBinders.length,
          fullType,
          listShape.collect { case (consName, shape) if consName == ctor.canonicalName => shape }
        )
      )
    }
  }

  def evalInductiveDecl(decl: Decl.InductiveDecl, env: Env): Env = {
    // All direct Value matches in this function and its private helpers
    // rely on EqStore.empty: no Vars are solved in this pass.

    val header = decl.header
    val name = header.name
    val ty = {
      if (header.binders.isEmpty) decl.header.resultTy
      else Term.Pi(header.binders, decl.header.resultTy, decl.header.span, NodeId.fresh())
    }

    val inductiveTypeCheck = TypeChecker.getType(ty, env)

    val initialPositiveArgs = DepSet.from(0 until header.arity)
    val initialMeta =
      InductiveMeta(
        decl.ctors.map(ctor => ConstructorMeta(ctor.shortName, ctor.canonicalName)),
        decl.header.binders.length,
        decl.isStruct,
        initialPositiveArgs
      )

    val inductivedHead = VConst(name, Inductive(initialMeta), inductiveTypeCheck)

    val checkEnvWithInductive = env.putGlobal(name, inductivedHead)
    val envWithFamilyBinders = {
      inductiveTypeCheck match {
        case pi: VPi =>
          assert(checkEnvWithInductive.locals.isEmpty) // Sanity check
          BinderOps.freshen(pi.binders, checkEnvWithInductive)
        case _ => checkEnvWithInductive
      }
    }

    val familyUniverse = TypeChecker.getType(header.resultTy, envWithFamilyBinders) match {
      case v: Universe => v
      case other       => throw InductiveTypeNotASort(other, Some(header.resultTy.span))
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
    familyUniverse match {
      case PropTpe => // Impredicative Prop families have no nominal principles.
      case VSort(level) =>
        header.binders.zip(familyArgs).foreach { case (binder, argument) =>
          val required = familyArgumentLevel(argument.tpe)
          if (!Level.leq(required, level))
            throw FamilyArgumentTooLarge(name, binder.name, required, Some(binder.span))
        }
    }
    var positiveArgs = positiveArgIndexes(familyArgs, familyArgs.map(_.tpe))

    val recursion = decl.ctors.map { ctor =>
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
        case ConstSpine(head, args) if head.name == name => args
        case _                                           => throw resultErr
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

        if (!ValueEquivalence.defEq(outputArg, witnesses.head))
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

      // The result's arguments are the family's own parameters by the uniformity check above.
      val recursiveFields = fieldTypes.indices.filter(idx => !doesNotOccur(recursiveTarget, fieldTypes(idx))).toVector
      val soleFieldIsOwnInstance = recursiveFields match {
        case Vector(idx) =>
          fieldTypes(idx) match {
            case InductiveFamilyValue(instance) =>
              instance.head.name == name && instance.args.length == outputArgs.length &&
              instance.args.zip(outputArgs).forall { case (arg, own) => ValueEquivalence.defEq(arg, own) }
            case _ => false
          }
        case _ => false
      }
      ConstructorRecursion(ctor, recursiveFields, soleFieldIsOwnInstance)
    }

    val meta = initialMeta.copy(positiveArgs = positiveArgs)

    val inductiveHeadCheck = VConst(name, Inductive(meta), inductiveTypeCheck)

    // Only after all constructor checks succeed do we add the decl to the environments.
    installInductive(decl, env, inductiveHeadCheck, listShape(decl, familyUniverse, recursion))
  }
}
