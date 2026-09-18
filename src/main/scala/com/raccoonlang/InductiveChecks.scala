package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.collection.immutable.BitSet

object InductiveChecks {
  private def getType(term: Term, env: Env, familyParams: Int): Value = {
    val checked = TypeChecker.checkTypeWithFamilyParams(term, env, familyParams)
    TypeChecker.assertType(checked.value)
    checked.value
  }
  private val activeClosureScans = new ThreadLocal[java.util.IdentityHashMap[Value, java.lang.Boolean]] {
    override def initialValue(): java.util.IdentityHashMap[Value, java.lang.Boolean] =
      new java.util.IdentityHashMap[Value, java.lang.Boolean]()
  }
  private val activePositivityLambdas = new ThreadLocal[java.util.IdentityHashMap[VLam, java.lang.Boolean]] {
    override def initialValue(): java.util.IdentityHashMap[VLam, java.lang.Boolean] =
      new java.util.IdentityHashMap[VLam, java.lang.Boolean]()
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
    final case class InductiveHeads(names: Set[String]) extends PositivityTarget {
      override def isDirectOccurrence(value: Value): Boolean =
        value match {
          case VConst(valueName, Inductive(_), _) => names(valueName)
          case _                                  => false
        }

      override def mayOccurIn(value: Value): Boolean =
        value match {
          // A lambda's body (and a thunk's code) can mention the inductive without it showing
          // anywhere the traversal looks; be conservative. The surface grammar cannot currently
          // place a lambda in a field type, but that must not be what soundness rests on.
          case thunk: NeutralThunk => thunkMayContain(names, thunk)
          case lam: VLam           => lambdaMayContain(names, lam)
          case _                   => false
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

  private final case class PositiveParamOverride(key: InductiveBlockKey, positiveParams: DepSet) {
    def isPositiveArgument(meta: InductiveMeta, index: Int): Boolean =
      if (meta.block.key == key) positiveParams.contains(index)
      else meta.block.isPositiveCoreArgument(index)
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

        case _: ConstructorHead => !target.mayOccurIn(value)

        case _: Level | LevelTpe | _: VLam | _: VSort | _: Var | _: VConst | PropTpe =>
          !target.mayOccurIn(value)
      }

  private def lambdaMayContain(names: Set[String], lambda: VLam): Boolean = {
    scanClosure(lambda) {
      val target = PositivityTarget.InductiveHeads(names)
      val captured = lambda.id match {
        case ValueId.Const(_)                 => Vector.empty
        case ValueId.LocalId(_, capturedArgs) => capturedArgs
      }
      !doesNotOccur(target, lambda.tpe) || captured.exists(value => !doesNotOccur(target, value)) ||
      (lambda.body match {
        case LamBody.Core(term, bodyEnv) =>
          bodyEnv.locals.values.exists(value => !doesNotOccur(target, value)) || checkedTermContainsAny(term, names)
        case _: LamBody.Native => true
      })
    }
  }

  private def thunkMayContain(names: Set[String], thunk: NeutralThunk): Boolean = {
    scanClosure(thunk) {
      val target = PositivityTarget.InductiveHeads(names)
      !doesNotOccur(target, thunk.tpe) || thunk.id.captures.exists(value => !doesNotOccur(target, value)) ||
      thunk.env.locals.values.exists(value => !doesNotOccur(target, value)) ||
      checkedTermContainsAny(thunk.term, names)
    }
  }

  private def scanClosure(value: Value)(body: => Boolean): Boolean = {
    val active = activeClosureScans.get()
    if (active.containsKey(value)) true
    else {
      active.put(value, java.lang.Boolean.TRUE)
      try body
      finally {
        active.remove(value)
        if (active.isEmpty) activeClosureScans.remove()
      }
    }
  }

  /** Evaluate one type-level lambda layer on rigid arguments; cycles are rejected conservatively. */
  private def inspectLambda(lambda: VLam)(body: (Vector[Value], Value) => Boolean): Boolean = {
    if (lambda.body.isInstanceOf[LamBody.Native]) return false
    val active = activePositivityLambdas.get()
    if (active.containsKey(lambda)) false
    else {
      active.put(lambda, java.lang.Boolean.TRUE)
      try {
        val freshEnv = BinderOps.freshen(lambda.tpe)
        val freshArgs = lambda.tpe.binders.map(binder => freshEnv(binder.localRef))
        body(freshArgs, Interpreter.evalApply(lambda, freshArgs))
      } finally {
        active.remove(lambda)
        if (active.isEmpty) activePositivityLambdas.remove()
      }
    }
  }

  /**
   * Whether a checked term mentions any of `names` as a global. Only the two nodes that can carry an occurrence are
   * named; every other node delegates to the shared child enumeration.
   */
  private def checkedTermContainsAny(term: CoreAst.Term, names: Set[String]): Boolean = term match {
    case CoreAst.Term.GlobalRef(name, _) => names(name)
    case other                           => CoreAst.children(other).exists(checkedTermContainsAny(_, names))
  }

  /**
   * Checks that the target only occurs positively in value: 1) Does not occur in the domain of any Pis 2) Only appears
   * in positive args of Inductives
   */
  private def occursPositively(
      target: PositivityTarget,
      value: Value,
      currentBlock: Option[PositiveParamOverride] = None
  ): Boolean =
    if (target.isDirectOccurrence(value)) true
    else
      value match {
        case _: NeutralThunk => !target.mayOccurIn(value)

        case InductiveFamilyValue(instance) =>
          if (target.isDirectOccurrence(instance.head)) true
          else
            instance.args.zipWithIndex.forall { case (arg, idx) =>
              val isPositive = currentBlock.fold(instance.meta.block.isPositiveCoreArgument(idx))(
                _.isPositiveArgument(instance.meta, idx)
              )
              if (isPositive) occursPositively(target, arg, currentBlock)
              else doesNotOccur(target, arg)
            }

        case app: VApp =>
          (target.isDirectOccurrence(app.head) || doesNotOccur(target, app.head)) &&
          app.args.forall(arg => doesNotOccur(target, arg)) &&
          occursPositively(target, app.tpe, currentBlock)

        case pi: VPi =>
          val freshEnv = BinderOps.freshen(pi)
          val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
          freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
          occursPositively(target, pi.codomain(freshEnv), currentBlock)

        case lam: VLam =>
          inspectLambda(lam) { (freshArgs, result) =>
            freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
            occursPositively(target, result, currentBlock)
          }

        case _: ConstructorHead => true

        case _: Level | LevelTpe | _: VSort | _: Var | _: VConst =>
          true
      }

  /** Requires every block-family occurrence to be fully applied at the common parameters and nonrecursive indices. */
  private def blockFamilyApplicationsAreUniform(
      blockNames: Set[String],
      target: PositivityTarget,
      expectedParams: Vector[Value],
      value: Value
  ): Boolean =
    value match {
      case _: NeutralThunk => false

      case InductiveFamilyValue(instance) =>
        if (blockNames(instance.head.name))
          instance.args.length >= expectedParams.length &&
          instance.args.take(expectedParams.length).zip(expectedParams).forall { case (actual, expected) =>
            ValueEquivalence.defEq(actual, expected)
          } &&
          instance.args.drop(expectedParams.length).forall(arg => doesNotOccur(target, arg))
        else
          instance.args.forall(arg => blockFamilyApplicationsAreUniform(blockNames, target, expectedParams, arg))

      case app: VApp =>
        doesNotOccur(target, app.head) &&
        app.args.forall(arg => blockFamilyApplicationsAreUniform(blockNames, target, expectedParams, arg)) &&
        blockFamilyApplicationsAreUniform(blockNames, target, expectedParams, app.tpe)

      case pi: VPi =>
        val freshEnv = BinderOps.freshen(pi)
        val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
        freshArgs.forall(arg => blockFamilyApplicationsAreUniform(blockNames, target, expectedParams, arg.tpe)) &&
        blockFamilyApplicationsAreUniform(blockNames, target, expectedParams, pi.codomain(freshEnv))

      case lam: VLam =>
        inspectLambda(lam) { (freshArgs, result) =>
          freshArgs.forall(arg =>
            blockFamilyApplicationsAreUniform(blockNames, target, expectedParams, arg.tpe)
          ) && blockFamilyApplicationsAreUniform(blockNames, target, expectedParams, result)
        }

      case VConst(name, Inductive(_), _) if blockNames(name) => false

      case _: ConstructorHead | _: Level | LevelTpe | _: VSort | _: Var | _: VConst =>
        true
    }

  /** C12 synthesizes implicit constructor family parameters before appending constructor binders. */
  private def constructorFamilyParams(header: InductiveHeader): Vector[Binder] =
    header.params.map(_.copy(isImplicit = true))

  private def constructorBinders(header: InductiveHeader, ctor: ConstructorDecl): Vector[Binder] =
    constructorFamilyParams(header) ++ ctor.binders

  /**
   * Every local this term references. Non-lexical, like capture analysis: a ref bound inside the term still counts,
   * which is the conservative direction for the dependency questions this module asks.
   */
  private def referencedLocals(term: Term): Set[LocalRef] = {
    val refs = Set.newBuilder[LocalRef]

    def go(term: Term): Unit =
      term match {
        case Term.LocalRef(ref, _) => refs += ref
        case other                 => CoreAst.children(other).foreach(go)
      }

    go(term)
    refs.result()
  }

  /** Precise transitive preceding-field dependencies of each stored field type. */
  private def constructorFieldDependencies(ctor: ConstructorDecl): Vector[BitSet] = {
    val fieldIndex = ctor.binders.zipWithIndex.map { case (binder, idx) => binder.localRef -> idx }.toMap
    val result = Array.fill(ctor.binders.length)(BitSet.empty)
    var idx = 0
    while (idx < ctor.binders.length) {
      val direct = BitSet.fromSpecific(referencedLocals(ctor.binders(idx).ty).flatMap(fieldIndex.get).filter(_ < idx))
      result(idx) = direct.foldLeft(direct) { case (dependencies, dependency) =>
        dependencies ++ result(dependency)
      }
      idx += 1
    }
    result.toVector
  }

  private def installConstructors(decl: Decl.InductiveDecl, baseEnv: Env): Env =
    decl.ctors.foldLeft(baseEnv) { case (curEnv, ctor) =>
      val allBinders = constructorBinders(decl.header, ctor)
      val fullTypeTerm =
        if (allBinders.isEmpty) ctor.resultTy
        else Term.Pi(allBinders, ctor.resultTy, ctor.span)

      val fullType = TypeChecker.getConstructorType(fullTypeTerm, curEnv, decl.header.params.length)
      curEnv.putGlobal(
        ctor.canonicalName,
        ConstructorHead(ctor.canonicalName, decl.header.params.length, allBinders.length, fullType)
      )
    }

  private def checkConstructorParamDiscipline(
      header: InductiveHeader,
      ctor: ConstructorDecl,
      envWithBinders: Env,
      outputArgs: Vector[Value]
  ): Unit =
    header.params.zipWithIndex.foreach { case (param, idx) =>
      val paramValue = envWithBinders(param.localRef)
      val outputArg = outputArgs(idx)
      val error =
        NonUniformInductiveParam(header.name, ctor.canonicalName, param.name, outputArg, Some(ctor.resultTy.span))

      if (!sameConstructorParam(outputArg, paramValue))
        throw error
    }

  private def sameConstructorParam(actual: Value, expected: Value): Boolean = {
    val sameLevel =
      (Level.fromValue(actual), Level.fromValue(expected)) match {
        case (Some(left), Some(right)) => left == right
        case _                         => false
      }
    ValueEquivalence.defEq(actual, expected) || sameLevel
  }

  private final case class FamilySignature(
      decl: Decl.InductiveDecl,
      familyType: Value,
      declaredSort: VSort,
      familyArgs: Vector[Value]
  )

  private final case class CheckedFamily(
      signature: FamilySignature,
      initialMeta: InductiveMeta,
      positivityInputs: PositiveParamInputs,
      hasRecursiveField: Boolean
  )

  private final case class PositiveParamInputs(
      contexts: Vector[PositiveParamContext]
  ) {
    def accepts(sourceIndex: Int, currentBlock: PositiveParamOverride): Boolean =
      contexts.forall(_.accepts(sourceIndex, currentBlock))
  }

  private final case class PositiveParamContext(
      sourceParams: Vector[Value],
      forbiddenValues: Vector[Value],
      positiveValues: Vector[Value]
  ) {
    def accepts(sourceIndex: Int, currentBlock: PositiveParamOverride): Boolean =
      sourceParams(sourceIndex) match {
        case Var(_, id, _) =>
          val target = PositivityTarget.LocalVar(id)
          val blockOverride = Some(currentBlock)
          forbiddenValues.forall(doesNotOccur(target, _)) &&
          positiveValues.forall(occursPositively(target, _, blockOverride))
        case _ => false
      }
  }

  private final case class PreparedFamily(
      decl: Decl.InductiveDecl,
      head: VConst,
      completeProjection: Env => Unit
  )

  private def validateBlockLayout(block: Decl.InductiveBlock, env: Env): Unit = {
    if (block.families.isEmpty)
      throw InvalidInductiveBlock("a block must contain at least one family", Some(block.span))
    val numParams = block.numParams
    block.families.foreach { decl =>
      if (decl.header.params.length != numParams)
        throw InvalidInductiveBlock(
          s"family ${decl.header.name} has ${decl.header.params.length} common parameters; expected $numParams",
          Some(decl.header.span)
        )
    }
    var seen = Set.empty[String]
    block.families.foreach { decl =>
      val names = (decl.header.name, decl.header.span) +: decl.ctors.map(ctor => (ctor.canonicalName, ctor.span))
      names.foreach { case (name, span) =>
        if (seen(name) || env.globals.contains(name)) throw AlreadyDefined(name, Some(span))
        seen += name
      }
    }
  }

  private def familyTypeTerm(decl: Decl.InductiveDecl): Term =
    if (decl.header.binders.isEmpty) decl.header.resultTy
    else Term.Pi(decl.header.binders, decl.header.resultTy, decl.header.span)

  private def checkFamilySignatures(block: Decl.InductiveBlock, env: Env): Vector[FamilySignature] = {
    val typedFamilies =
      block.families.map(decl => (decl, getType(familyTypeTerm(decl), env, decl.header.params.length)))
    val coreParamCount = block.families.head.header.params.length
    val expectedImplicitness = block.families.head.header.params.map(_.isImplicit)
    val canonicalParams =
      if (coreParamCount == 0) Vector.empty
      else
        typedFamilies.head._2 match {
          case pi: VPi if pi.binders.length == typedFamilies.head._1.header.arity =>
            val canonicalEnv = BinderOps.freshen(pi.binders.take(coreParamCount), pi.env)
            pi.binders.take(coreParamCount).map(binder => canonicalEnv(binder.localRef))
          case _ =>
            throw InvalidInductiveBlock(
              s"family ${typedFamilies.head._1.header.name} does not expose its declared parameter telescope",
              Some(typedFamilies.head._1.header.span)
            )
        }
    val signatures = typedFamilies.map { case (decl, familyType) =>
      val (familyArgs, result) =
        familyType match {
          case pi: VPi if pi.binders.length == decl.header.arity =>
            val actualImplicitness = decl.header.params.map(_.isImplicit)
            if (actualImplicitness != expectedImplicitness)
              throw InvalidInductiveBlock(
                s"family ${decl.header.name} has a different common-parameter binder mode",
                Some(decl.header.span)
              )

            var familyEnv = pi.env
            pi.binders.take(coreParamCount).zip(canonicalParams).zipWithIndex.foreach {
              case ((binder, canonical), index) =>
                val expectedType = Interpreter.evalTerm(binder.ty, familyEnv)
                if (!ValueEquivalence.defEq(canonical.tpe, expectedType))
                  throw InvalidInductiveBlock(
                    s"family ${decl.header.name} has a different type for common parameter $index",
                    Some(decl.header.params(index).span)
                  )
                familyEnv = familyEnv.putLocal(binder.localRef, canonical)
            }
            familyEnv = BinderOps.freshen(pi.binders.drop(coreParamCount), familyEnv)
            (pi.binders.map(binder => familyEnv(binder.localRef)), pi.codomain(familyEnv))

          case value if decl.header.arity == 0 => (Vector.empty, value)

          case _ =>
            throw InvalidInductiveBlock(
              s"family ${decl.header.name} does not expose its declared telescope",
              Some(decl.header.span)
            )
        }

      val declaredSort = result match {
        case sort: VSort => sort
        case other       => throw InductiveTypeNotASort(other, Some(decl.header.resultTy.span))
      }
      FamilySignature(decl, familyType, declaredSort, familyArgs)
    }

    val commonSort = signatures.head.declaredSort
    signatures.tail.foreach { signature =>
      if (!ValueEquivalence.defEq(signature.declaredSort, commonSort))
        throw InvalidInductiveBlock(
          s"family ${signature.decl.header.name} lives in ${signature.declaredSort}, expected $commonSort",
          Some(signature.decl.header.resultTy.span)
        )
    }
    signatures
  }

  private def initialMeta(
      signature: FamilySignature,
      provisionalBlock: ProvisionalInductiveBlockInfo
  ): InductiveMeta = {
    val decl = signature.decl
    InductiveMeta(
      decl.ctors.map(ctor => ConstructorMeta(ctor.shortName, ctor.canonicalName)),
      decl.header.arity,
      provisionalBlock
    )
  }

  private def checkFamilyConstructors(
      signature: FamilySignature,
      meta: InductiveMeta,
      provisionalEnv: Env,
      block: Decl.InductiveBlock,
      blockNames: Set[String]
  ): CheckedFamily = {
    // All direct Value matches in this function and its private helpers rely on EqStore.empty:
    // no Vars are solved while an inductive block is checked.
    val decl = signature.decl

    val header = decl.header
    val name = header.name
    val recursiveTarget = PositivityTarget.InductiveHeads(blockNames)
    val sourcePrefixCount = block.numParams
    val sourceParams = signature.familyArgs.take(sourcePrefixCount)
    val positivityContexts = Vector.newBuilder[PositiveParamContext]
    var familyHasRecursiveField = false
    positivityContexts += PositiveParamContext(
      sourceParams,
      signature.familyArgs.drop(sourcePrefixCount).map(_.tpe) :+ signature.declaredSort,
      signature.familyArgs.take(sourcePrefixCount).map(_.tpe)
    )
    decl.ctors.foreach { ctor =>
      val allConstructorBinders = constructorBinders(header, ctor)
      val checkedBinders =
        BinderOps.checkBinders(allConstructorBinders, provisionalEnv, familyParams = header.params.length)
      val binders = checkedBinders.binders
      val envWithBinders = checkedBinders.env
      val binderVars = binders.map(binder => envWithBinders(binder.localRef))
      val commonParamValues = binderVars.take(header.params.length)
      val ownBinderVars = binderVars.drop(header.params.length)
      val sourceParamValues = commonParamValues
      val trueFieldVars = ownBinderVars
      // Keep the raw checked value here so an incomplete family spine can report the
      // specialized constructor-result error rather than an incidental NotAType.
      val outputTpe = TypeChecker.checkTerm(ctor.resultTy, envWithBinders).value

      // 4) Constructor result must be the inductive family head applied to the full family arity.
      val resultErr = InvalidConstructorResult(ctor.canonicalName, name, outputTpe, Some(ctor.span))
      val outputArgs = outputTpe match {
        case ConstSpine(head, args) if head.name == name => args
        case _                                           => throw resultErr
      }

      if (outputArgs.length != header.arity) throw resultErr

      checkConstructorParamDiscipline(header, ctor, envWithBinders, outputArgs)
      if (
        outputArgs.take(sourceParamValues.length).zip(sourceParamValues).exists { case (actual, expected) =>
          !sameConstructorParam(actual, expected)
        }
      )
        throw InvalidInductiveBlock(
          s"constructor ${ctor.canonicalName} does not preserve the complete source parameter prefix",
          Some(ctor.resultTy.span)
        )
      if (outputArgs.drop(sourceParamValues.length).exists(arg => !doesNotOccur(recursiveTarget, arg)))
        throw NonStrictlyPositive(
          inductive = name,
          ctor = ctor.canonicalName,
          field = "<result index>",
          fieldTy = outputTpe,
          span = Some(ctor.resultTy.span)
        )

      val constructorUniverse = TypeChecker.getUniverse(outputTpe)
      val constructorArgs = ctor.binders.zip(trueFieldVars)
      val constructorArgTypes = constructorArgs.map(_._2.tpe)
      val fieldDependencies = constructorFieldDependencies(ctor)
      val syntacticallyRecursive = Array.fill(ctor.binders.length)(false)
      ctor.binders.indices.foreach { index =>
        syntacticallyRecursive(index) = referencesAnyGlobal(ctor.binders(index).ty, blockNames) ||
          fieldDependencies(index).exists(syntacticallyRecursive)
      }
      positivityContexts += PositiveParamContext(
        sourceParamValues,
        outputArgs.drop(sourceParamValues.length),
        constructorArgTypes
      )

      constructorArgs.zipWithIndex.foreach { case ((binder, field), sourceFieldIndex) =>
        // Eta eligibility follows the checked field type, not merely the source syntax.  A
        // recursive occurrence can be exposed after elaboration/evaluation even when the raw
        // binder is not syntactically recursive.
        familyHasRecursiveField = familyHasRecursiveField || !doesNotOccur(recursiveTarget, field.tpe)

        // Universe bounds are checked before strict positivity, matching the formation pipeline.
        constructorUniverse match {
          case PropTpe => // no universe restriction
          case VSort(inductiveLevel) =>
            TypeChecker.getUniverse(field.tpe) match {
              case Value.PropTpe =>
              case VSort(tpeLevel) if !Level.leq(tpeLevel, inductiveLevel) =>
                throw InductiveUniverseTooSmall(
                  name,
                  s"${ctor.canonicalName}.${binder.name}",
                  field.tpe,
                  tpeLevel,
                  inductiveLevel,
                  Some(binder.span)
                )
              case _ =>
            }
        }

        // Every recursive source field must be strictly positive in every block family.
        if (
          syntacticallyRecursive(sourceFieldIndex) &&
          (!occursPositively(recursiveTarget, field.tpe) ||
            !blockFamilyApplicationsAreUniform(blockNames, recursiveTarget, sourceParamValues, field.tpe))
        )
          throw NonStrictlyPositive(
            inductive = name,
            ctor = ctor.canonicalName,
            field = binder.name,
            fieldTy = field.tpe,
            span = Some(binder.span)
          )
      }

    }

    CheckedFamily(
      signature,
      meta,
      PositiveParamInputs(positivityContexts.result()),
      familyHasRecursiveField
    )
  }

  /** Whether an unchecked term names any of `names` as a global. */
  private def referencesAnyGlobal(term: Term, names: Set[String]): Boolean = term match {
    case Term.GlobalRef(name, _) => names(name)
    case other                   => CoreAst.children(other).exists(referencesAnyGlobal(_, names))
  }

  private def computePositiveParams(
      block: Decl.InductiveBlock,
      blockKey: InductiveBlockKey,
      checked: Vector[CheckedFamily]
  ): DepSet = {
    var current = DepSet.from(0 until block.numParams)
    var stable = false
    while (!stable) {
      val currentBlock = PositiveParamOverride(blockKey, current)
      val next = DepSet.newBuilder
      current.foreach { sourceIndex =>
        if (checked.forall(_.positivityInputs.accepts(sourceIndex, currentBlock))) next.add(sourceIndex)
      }
      val result = next.result()
      stable = result == current
      current = result
    }
    current
  }

  private def prepareFamily(
      check: CheckedFamily,
      checkedBlock: CheckedInductiveBlockSchema,
      blockHasRecursiveField: Boolean
  ): PreparedFamily = {
    val decl = check.signature.decl
    var installedCtor: Option[ConstructorHead] = None
    val projectionInfo =
      if (decl.ctors.length == 1) {
        val ctor = decl.ctors.head
        Some(
          new ProjectionInfo(
            decl.ctors.head.canonicalName,
            constructorFieldDependencies(ctor),
            etaEligible = decl.header.indices.isEmpty && !blockHasRecursiveField,
            () => installedCtor
          )
        )
      } else None
    val meta = check.initialMeta.copy(block = checkedBlock, projectionInfo = projectionInfo)
    val head = VConst(decl.header.name, Inductive(meta), check.signature.familyType)
    val complete = (finalEnv: Env) =>
      if (decl.ctors.length == 1) {
        installedCtor = finalEnv(decl.ctors.head.canonicalName) match {
          case h: ConstructorHead => Some(h)
          case other => throw WTF(s"Constructor ${decl.ctors.head.canonicalName} resolved to non-constructor $other")
        }
        projectionInfo.foreach(_.ctorHead)
      }
    PreparedFamily(decl, head, complete)
  }

  def checkInductive(decl: Decl.InductiveDecl, env: Env): Env = evalInductiveBlock(Vector(decl), env)
  def checkInductiveBlock(decls: Vector[Decl.InductiveDecl], env: Env): Env = evalInductiveBlock(decls, env)
  def checkInductiveBlock(block: Decl.InductiveBlock, env: Env): Env = evalInductiveBlock(block, env)
  def evalInductive(decl: Decl.InductiveDecl, env: Env): Env = evalInductiveBlock(Vector(decl), env)
  def evalInductiveBlock(decls: Vector[Decl.InductiveDecl], env: Env): Env = {
    val block = Decl.InductiveBlock(decls, decls.headOption.map(_.span).getOrElse(Span(0, 0)))
    evalInductiveBlock(block, env)
  }

  def evalInductiveBlock(block: Decl.InductiveBlock, env: Env): Env = {
    validateBlockLayout(block, env)
    val signatures = checkFamilySignatures(block, env)
    val blockKey = InductiveBlockKey(block.families.map(_.header.name), block.numParams)
    val provisionalBlock = ProvisionalInductiveBlockInfo(blockKey, DepSet.from(0 until block.numParams))
    val provisional = signatures.map { signature =>
      val meta = initialMeta(signature, provisionalBlock)
      (signature, meta, VConst(signature.decl.header.name, Inductive(meta), signature.familyType))
    }
    val provisionalEnv = provisional.foldLeft(env) { case (curEnv, (_, _, head)) =>
      curEnv.putGlobal(head.name, head)
    }
    val blockNames = block.families.iterator.map(_.header.name).toSet
    val checked = provisional.map { case (signature, meta, _) =>
      checkFamilyConstructors(signature, meta, provisionalEnv, block, blockNames)
    }
    val positiveParams = computePositiveParams(block, blockKey, checked)
    val checkedBlock = CheckedInductiveBlockSchema(blockKey, positiveParams)
    val prepared = checked.map(check => prepareFamily(check, checkedBlock, checked.exists(_.hasRecursiveField)))
    val envWithFinalHeads = prepared.foldLeft(env) { case (curEnv, family) =>
      curEnv.putGlobal(family.decl.header.name, family.head)
    }
    val finalEnv = prepared.foldLeft(envWithFinalHeads) { case (curEnv, family) =>
      installConstructors(family.decl, curEnv)
    }
    prepared.foreach(_.completeProjection(finalEnv))
    finalEnv
  }
}
