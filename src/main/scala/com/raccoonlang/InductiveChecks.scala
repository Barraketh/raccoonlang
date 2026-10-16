package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.collection.immutable.BitSet

object InductiveChecks {
  // ------------ Occurrence and Positivity ------------

  // A scan belongs to one target and, for local parameter checks, one positive-parameter fixed-point state.
  private sealed trait PositivityTarget {
    def isDirectOccurrence(value: Value): Boolean
  }

  private object PositivityTarget {
    final case class InductiveHeads(names: Set[String]) extends PositivityTarget {
      override def isDirectOccurrence(value: Value): Boolean =
        value match {
          case VConst(valueName, Inductive(_), _) => names(valueName)
          case _                                  => false
        }
    }

    final case class LocalVar(id: VarId) extends PositivityTarget {
      override def isDirectOccurrence(value: Value): Boolean =
        value match {
          case Var(_, valueId, _) => valueId == id
          case _                  => false
        }
    }
  }

  private final case class PositiveParamOverride(key: InductiveBlockKey, positiveParams: DepSet) {
    def isPositiveArgument(meta: InductiveMeta, index: Int): Boolean =
      if (meta.block.key == key) positiveParams.contains(index)
      else meta.block.isPositiveCoreArgument(index)
  }

  private def memoized(
      value: Value,
      completed: java.util.IdentityHashMap[Value, java.lang.Boolean],
      active: java.util.IdentityHashMap[Value, java.lang.Boolean],
      cycleResult: Boolean
  )(compute: => Boolean): Boolean = {
    val cached = completed.get(value)
    if (cached != null) cached.booleanValue()
    else if (active.containsKey(value)) cycleResult
    else {
      active.put(value, java.lang.Boolean.TRUE)
      val result =
        try compute
        finally active.remove(value)
      completed.put(value, java.lang.Boolean.valueOf(result))
      result
    }
  }

  private def inspectLambda(lambda: VLam)(body: (Vector[Value], Value) => Boolean): Boolean =
    lambda.body match {
      case _: LamBody.Native => false
      case _ =>
        val freshEnv = BinderOps.freshen(lambda.tpe)
        val freshArgs = lambda.tpe.binders.map(binder => freshEnv(binder.localRef))
        body(freshArgs, Interpreter.evalApply(lambda, freshArgs))
    }

  /** A memoized occurrence and positivity scan for one target and parameter-analysis state. */
  private final class OccurrenceScan(
      val target: PositivityTarget,
      currentBlock: Option[PositiveParamOverride]
  ) {
    private val completedAbsent = new java.util.IdentityHashMap[Value, java.lang.Boolean]()
    private val activeAbsent = new java.util.IdentityHashMap[Value, java.lang.Boolean]()
    private val completedPositive = new java.util.IdentityHashMap[Value, java.lang.Boolean]()
    private val activePositive = new java.util.IdentityHashMap[Value, java.lang.Boolean]()

    private def localAbsentByDependencies(value: Value): Boolean =
      target match {
        case PositivityTarget.LocalVar(id)      => !value.synDeps.contains(id)
        case _: PositivityTarget.InductiveHeads => true
      }

    private def hasNoLocalDependency(value: Value): Boolean =
      target match {
        case PositivityTarget.LocalVar(id)      => !value.synDeps.contains(id)
        case _: PositivityTarget.InductiveHeads => false
      }

    def absent(value: Value): Boolean =
      memoized(value, completedAbsent, activeAbsent, cycleResult = false) {
        if (target.isDirectOccurrence(value)) false
        else if (hasNoLocalDependency(value)) true
        else
          value match {
            case thunk: NeutralThunk =>
              target match {
                case _: PositivityTarget.LocalVar => localAbsentByDependencies(thunk)
                case PositivityTarget.InductiveHeads(names) =>
                  absent(thunk.tpe) && thunk.id.captures.forall(absent) &&
                  thunk.env.locals.values.forall(absent) && !CoreAst.mentionsGlobal(thunk.term, names)
              }

            case InductiveFamilyValue(instance) =>
              !target.isDirectOccurrence(instance.head) && instance.args.forall(absent)

            case app: VApp =>
              absent(app.head) && app.args.forall(absent) && absent(app.tpe)

            case pi: VPi =>
              val freshEnv = BinderOps.freshen(pi)
              val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
              freshArgs.forall(arg => absent(arg.tpe)) && absent(pi.codomain(freshEnv))

            case proof: VProof => absent(proof.tpe)

            case lambda: VLam =>
              target match {
                case _: PositivityTarget.LocalVar => localAbsentByDependencies(lambda)
                case PositivityTarget.InductiveHeads(names) =>
                  val captures = lambda.id match {
                    case ValueId.Const(_)                 => Vector.empty
                    case ValueId.LocalId(_, capturedArgs) => capturedArgs
                  }
                  val bodyAbsent = lambda.body match {
                    case LamBody.Core(term, bodyEnv) =>
                      bodyEnv.locals.values.forall(absent) && !CoreAst.mentionsGlobal(term, names)
                    // Opaque host code can name values outside the visible environment, so it cannot certify
                    // that a declaration-time block is absent.
                    case _: LamBody.Native => false
                    case LamBody.ProofEta  => true
                  }
                  absent(lambda.tpe) && captures.forall(absent) && bodyAbsent
              }

            case _: ConstructorHead => localAbsentByDependencies(value)

            case _: Level | LevelTpe | LevelClassifier | Large | _: VSort | _: Var | _: VConst =>
              localAbsentByDependencies(value)
          }
      }

    def positive(value: Value): Boolean =
      memoized(value, completedPositive, activePositive, cycleResult = false) {
        if (absent(value)) true
        else if (target.isDirectOccurrence(value)) true
        else
          value match {
            case _: NeutralThunk => false

            case InductiveFamilyValue(instance) =>
              if (target.isDirectOccurrence(instance.head)) true
              else
                instance.args.zipWithIndex.forall { case (arg, index) =>
                  val positiveArgument = currentBlock.fold(instance.meta.block.isPositiveCoreArgument(index))(
                    _.isPositiveArgument(instance.meta, index)
                  )
                  if (positiveArgument) positive(arg) else absent(arg)
                }

            case app: VApp =>
              (target.isDirectOccurrence(app.head) || absent(app.head)) &&
              app.args.forall(absent) && positive(app.tpe)

            case pi: VPi =>
              val freshEnv = BinderOps.freshen(pi)
              val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
              freshArgs.forall(arg => absent(arg.tpe)) && positive(pi.codomain(freshEnv))

            // A proof's interior is erased; its type is all that can carry an occurrence.
            case proof: VProof => absent(proof.tpe)

            case lambda: VLam =>
              inspectLambda(lambda) { (freshArgs, result) =>
                freshArgs.forall(arg => absent(arg.tpe)) && positive(result)
              }

            case _: ConstructorHead => true

            case _: Level | LevelTpe | LevelClassifier | Large | _: VSort | _: Var | _: VConst => true
          }
      }
  }

  /** Memoized per constructor because the expected common parameters are constructor-local variables. */
  private final class UniformityScan(
      blockNames: Set[String],
      expectedParams: Vector[Value],
      occurrences: OccurrenceScan
  ) {
    private val completed = new java.util.IdentityHashMap[Value, java.lang.Boolean]()
    private val active = new java.util.IdentityHashMap[Value, java.lang.Boolean]()

    def accepts(value: Value): Boolean =
      memoized(value, completed, active, cycleResult = false) {
        if (occurrences.absent(value)) true
        else
          value match {
            case _: NeutralThunk => false

            case InductiveFamilyValue(instance) =>
              if (blockNames(instance.head.name))
                instance.args.length >= expectedParams.length &&
                instance.args.take(expectedParams.length).zip(expectedParams).forall { case (actual, expected) =>
                  ValueEquivalence.defEq(actual, expected)
                } && instance.args.drop(expectedParams.length).forall(occurrences.absent)
              else instance.args.forall(accepts)

            case app: VApp =>
              occurrences.absent(app.head) && app.args.forall(accepts) && accepts(app.tpe)

            case pi: VPi =>
              val freshEnv = BinderOps.freshen(pi)
              val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
              freshArgs.forall(arg => accepts(arg.tpe)) && accepts(pi.codomain(freshEnv))

            case proof: VProof => accepts(proof.tpe)

            case lambda: VLam =>
              inspectLambda(lambda) { (freshArgs, result) =>
                freshArgs.forall(arg => accepts(arg.tpe)) && accepts(result)
              }

            case VConst(name, Inductive(_), _) if blockNames(name) => false

            case _: ConstructorHead | _: Level | LevelTpe | LevelClassifier | Large | _: VSort | _: Var | _: VConst =>
              true
          }
      }
  }

  private def constructorFamilyParams(header: InductiveHeader): Vector[Binder] =
    header.params.map(_.copy(isImplicit = true))

  private def constructorBinders(header: InductiveHeader, ctor: ConstructorDecl): Vector[Binder] =
    constructorFamilyParams(header) ++ ctor.binders

  /** Precise transitive preceding-field dependencies of each stored field type. */
  private def constructorFieldDependencies(ctor: ConstructorDecl): Vector[BitSet] = {
    val fieldIndex = ctor.binders.zipWithIndex.map { case (binder, idx) => binder.localRef -> idx }.toMap
    val result = Array.fill(ctor.binders.length)(BitSet.empty)
    var idx = 0
    while (idx < ctor.binders.length) {
      val direct =
        BitSet.fromSpecific(CoreAst.mentionedRefs(ctor.binders(idx).ty).flatMap(fieldIndex.get).filter(_ < idx))
      result(idx) = direct.foldLeft(direct) { case (dependencies, dependency) =>
        dependencies ++ result(dependency)
      }
      idx += 1
    }
    result.toVector
  }

  /** A constructor's declared type: its family's parameters, implicit, then its fields. */
  private[raccoonlang] def constructorTypeTerm(header: InductiveHeader, ctor: ConstructorDecl): Term = {
    val allBinders = constructorBinders(header, ctor)
    if (allBinders.isEmpty) ctor.resultTy
    else Term.Pi(allBinders, ctor.resultTy, ctor.span, NodeId.fresh())
  }

  private def installConstructors(family: PreparedFamily, baseEnv: Env): Env = {
    val decl = family.decl
    val familyParams = decl.header.params.length
    decl.ctors.foldLeft(baseEnv) { case (curEnv, ctor) =>
      val fullType = TypeChecker.getConstructorType(constructorTypeTerm(decl.header, ctor), curEnv, familyParams)
      val installed = curEnv.putGlobal(
        ctor.canonicalName,
        ConstructorHead(ctor.canonicalName, familyParams, familyParams + ctor.binders.length, fullType)
      )
      installed
    }
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
      if (!ValueEquivalence.defEq(outputArg, paramValue))
        at(ctor.resultTy.span) {
          fail(NonUniformInductiveParam(header.name, ctor.canonicalName, param.name, outputArg))
        }
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
      hasRecursiveField: Boolean,
      proofFieldPlan: Option[(Vector[ProofFieldSource], Boolean)]
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
          val scan = new OccurrenceScan(target, Some(currentBlock))
          forbiddenValues.forall(scan.absent) && positiveValues.forall(scan.positive)
        case _ => false
      }
  }

  private final case class PreparedFamily(
      decl: Decl.InductiveDecl,
      head: VConst,
      completeConstructorLink: Env => Unit
  )

  private def validateBlockLayout(block: Decl.InductiveBlock, env: Env): Unit = {
    if (block.families.isEmpty) fail(InvalidInductiveBlock("a block must contain at least one family"))
    val numParams = block.numParams
    block.families.foreach { decl =>
      if (decl.header.params.length != numParams)
        at(decl.header.span) {
          fail(
            InvalidInductiveBlock(
              s"family ${decl.header.name} has ${decl.header.params.length} common parameters; expected $numParams"
            )
          )
        }
    }
    var seen = Set.empty[String]
    block.families.foreach { decl =>
      val names = (decl.header.name, decl.header.span) +: decl.ctors.map(ctor => (ctor.canonicalName, ctor.span))
      names.foreach { case (name, span) =>
        if (seen(name) || env.globals.contains(name)) at(span) { fail(AlreadyDefined(name)) }
        seen += name
      }
    }
  }

  /** A family's declared type: its parameters, then its indices. */
  private[raccoonlang] def familyTypeTerm(decl: Decl.InductiveDecl): Term =
    if (decl.header.binders.isEmpty) decl.header.resultTy
    else
      Term.Pi(
        decl.header.binders,
        decl.header.resultTy,
        decl.header.span,
        NodeId.fresh()
      )

  /** Counts the value size of a family argument, descending elementwise through data function types. */
  private def familyArgumentLevel(tpe: Value): Level = tpe match {
    case LevelTpe    => Level.zero
    case sort: VSort => if (Sorts.isProp(sort)) Level.zero else sort.level
    case pi: VPi if !pi.isPropValued =>
      val freshEnv = BinderOps.freshen(pi.binders, pi.env)
      val domains = pi.binders.map { binder =>
        freshEnv(binder.localRef).tpe match {
          case LevelTpe => Level.zero
          case domain   => TypeChecker.getUniverse(domain).level
        }
      }
      Level.max(domains :+ familyArgumentLevel(pi.codomain(freshEnv)))
    case other => TypeChecker.getUniverse(other).level
  }

  private def checkFamilySignatures(block: Decl.InductiveBlock, env: Env): Vector[FamilySignature] = {
    val typedFamilies = block.families.map(decl => (decl, TypeChecker.checkDeclType(familyTypeTerm(decl), env).value))
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
            at(typedFamilies.head._1.header.span) {
              fail(
                InvalidInductiveBlock(
                  s"family ${typedFamilies.head._1.header.name} does not expose its declared parameter telescope"
                )
              )
            }
        }
    typedFamilies.map { case (decl, familyType) =>
      val (familyArgs, result) =
        familyType match {
          case pi: VPi if pi.binders.length == decl.header.arity =>
            val actualImplicitness = decl.header.params.map(_.isImplicit)
            if (actualImplicitness != expectedImplicitness)
              at(decl.header.span) {
                fail(InvalidInductiveBlock(s"family ${decl.header.name} has a different common-parameter binder mode"))
              }

            var familyEnv = pi.env
            pi.binders.take(coreParamCount).zip(canonicalParams).zipWithIndex.foreach {
              case ((binder, canonical), index) =>
                val expectedType = Interpreter.evalTerm(binder.ty, familyEnv)
                if (!ValueEquivalence.defEq(canonical.tpe, expectedType))
                  at(decl.header.params(index).span) {
                    fail(
                      InvalidInductiveBlock(
                        s"family ${decl.header.name} has a different type for common parameter $index"
                      )
                    )
                  }
                familyEnv = BinderOps.bindValue(familyEnv, binder, canonical)
            }
            familyEnv = BinderOps.freshen(pi.binders.drop(coreParamCount), familyEnv)
            (pi.binders.map(binder => familyEnv(binder.localRef)), pi.codomain(familyEnv))

          case value if decl.header.arity == 0 => (Vector.empty, value)

          case _ =>
            at(decl.header.span) {
              fail(InvalidInductiveBlock(s"family ${decl.header.name} does not expose its declared telescope"))
            }
        }

      val declaredSort = result match {
        case sort: VSort => sort
        case other       => at(decl.header.resultTy.span) { fail(InductiveTypeNotASort(other)) }
      }
      if (!Sorts.isProp(declaredSort))
        decl.header.binders.zip(familyArgs).foreach { case (binder, argument) =>
          val required = familyArgumentLevel(argument.tpe)
          if (!Level.leq(required, declaredSort.level))
            at(binder.span) { fail(FamilyArgumentTooLarge(decl.header.name, binder.name, required)) }
        }
      FamilySignature(decl, familyType, declaredSort, familyArgs)
    }
  }

  private def initialMeta(
      signature: FamilySignature,
      provisionalBlock: ProvisionalInductiveBlockInfo
  ): InductiveMeta = {
    val decl = signature.decl
    InductiveMeta(
      decl.ctors.map(ctor => ConstructorMeta(ctor.shortName, ctor.canonicalName)),
      decl.header.binders.length,
      provisionalBlock,
      projectionInfo = None,
      proofRecovery = None
    )
  }

  private def checkFamilyConstructors(
      signature: FamilySignature,
      meta: InductiveMeta,
      provisionalEnv: Env,
      block: Decl.InductiveBlock,
      blockNames: Set[String],
      recursiveScan: OccurrenceScan
  ): CheckedFamily = {
    // All direct Value matches in this function and its private helpers rely on EqStore.empty:
    // no Vars are solved while an inductive block is checked.
    val decl = signature.decl

    val header = decl.header
    val name = header.name
    val sourcePrefixCount = block.numParams
    val sourceParams = signature.familyArgs.take(sourcePrefixCount)
    val positivityContexts = Vector.newBuilder[PositiveParamContext]
    positivityContexts += PositiveParamContext(
      sourceParams,
      signature.familyArgs.drop(sourcePrefixCount).map(_.tpe) :+ signature.declaredSort,
      signature.familyArgs.take(sourcePrefixCount).map(_.tpe)
    )
    var hasRecursiveField = false
    // Proof recovery applies only to families declared in Prop, whose instances erase.
    var proofFieldPlan = Option.when(decl.ctors.length == 1 && Sorts.isProp(signature.declaredSort)) {
      (Vector.empty[ProofFieldSource], false)
    }

    decl.ctors.foreach { ctor =>
      val allConstructorBinders = constructorBinders(header, ctor)
      val checkedBinders =
        BinderOps.checkBinders(allConstructorBinders, provisionalEnv, familyParams = header.params.length)
      val binders = checkedBinders.binders
      val envWithBinders = checkedBinders.env
      val binderVars = binders.map(binder => envWithBinders(binder.localRef))
      val commonParamValues = binderVars.take(header.params.length)
      val ownBinderVars = binderVars.drop(header.params.length)
      val trueFieldVars = ownBinderVars
      val outputTpe = TypeChecker.checkTypeTerm(ctor.resultTy, envWithBinders).value

      // 4) Constructor result must be the inductive family head applied to the full family arity.
      def badResult: Nothing =
        at(ctor.span) { fail(InvalidConstructorResult(ctor.canonicalName, name, outputTpe)) }
      val outputArgs = outputTpe match {
        case ConstSpine(head, args) if head.name == name => args
        case _                                           => badResult
      }

      if (outputArgs.length != header.arity) badResult

      checkConstructorParamDiscipline(header, ctor, envWithBinders, outputArgs)
      if (outputArgs.drop(commonParamValues.length).exists(arg => !recursiveScan.absent(arg)))
        at(ctor.resultTy.span) {
          fail(
            NonStrictlyPositive(
              inductive = name,
              ctor = ctor.canonicalName,
              field = "<result index>",
              fieldTy = outputTpe
            )
          )
        }

      // Compile data sources for the one-constructor family's proof-recovery plan. Whether a
      // field is a proof is classified later at the actual family instance, so universe-polymorphic
      // fields that become proofs at u := 0 need no declaration-time special case.
      if (proofFieldPlan.nonEmpty) {
        val sources = ownBinderVars.map { field =>
          val resultIndex = outputArgs.indexWhere(arg => ValueEquivalence.defEq(arg, field))
          if (resultIndex >= 0) ProofFieldSource.ResultArgument(resultIndex)
          else ProofFieldSource.Unavailable
        }
        val definitelyComplete = ownBinderVars.zip(sources).forall { case (field, source) =>
          Sorts.isProposition(field.tpe) || source != ProofFieldSource.Unavailable
        }
        proofFieldPlan = Some((sources, definitelyComplete))
      }

      val constructorUniverse = TypeChecker.getUniverse(outputTpe)
      val constructorArgs = ctor.binders.zip(trueFieldVars)
      val constructorArgTypes = constructorArgs.map(_._2.tpe)
      val fieldDependencies = constructorFieldDependencies(ctor)
      val syntacticallyRecursive = Array.fill(ctor.binders.length)(false)
      val uniformity = new UniformityScan(blockNames, commonParamValues, recursiveScan)
      ctor.binders.indices.foreach { index =>
        syntacticallyRecursive(index) = CoreAst.mentionsGlobal(ctor.binders(index).ty, blockNames) ||
          fieldDependencies(index).exists(syntacticallyRecursive)
      }
      positivityContexts += PositiveParamContext(
        commonParamValues,
        outputArgs.drop(commonParamValues.length),
        constructorArgTypes
      )

      constructorArgs.zipWithIndex.foreach { case ((binder, field), sourceFieldIndex) =>
        def fieldName = s"${ctor.canonicalName}.${binder.name}"
        val fieldSort = TypeChecker.getUniverse(field.tpe)
        // 2) Universe bound: skip for Prop families; enforce for Sort families
        if (!Sorts.isProp(constructorUniverse) && !Level.leq(fieldSort.level, constructorUniverse.level))
          at(binder.span) {
            fail(InductiveUniverseTooSmall(name, fieldName, field.tpe, fieldSort.level, constructorUniverse.level))
          }
        if (syntacticallyRecursive(sourceFieldIndex) && !recursiveScan.absent(field.tpe)) hasRecursiveField = true

        // 3) Every true source field type must be strictly positive in every block family.
        if (
          syntacticallyRecursive(sourceFieldIndex) &&
          (!recursiveScan.positive(field.tpe) || !uniformity.accepts(field.tpe))
        )
          at(binder.span) {
            fail(
              NonStrictlyPositive(inductive = name, ctor = ctor.canonicalName, field = binder.name, fieldTy = field.tpe)
            )
          }
      }

    }

    CheckedFamily(
      signature,
      meta,
      PositiveParamInputs(positivityContexts.result()),
      hasRecursiveField,
      proofFieldPlan
    )
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
    val header = decl.header

    // A one-constructor family gets positional projection metadata regardless of indices or recursion. Structure eta
    // is available only for data families, with zero true source indices and no recursive occurrence.
    //
    // The constructor head is a promise completed after installation: constructor types are checked against the
    // installed family head, so the head cannot exist before installConstructors runs.
    var installedCtorHead: Option[ConstructorHead] = None
    val projectionInfo =
      if (decl.ctors.length == 1) {
        val ctor = decl.ctors.head
        Some(
          new ProjectionInfo(
            ctor.canonicalName,
            constructorFieldDependencies(ctor),
            etaEligible =
              !Sorts.isProp(check.signature.declaredSort) && header.indices.isEmpty && !blockHasRecursiveField,
            () => installedCtorHead
          )
        )
      } else None

    val proofRecovery = for {
      (fields, definitelyComplete) <- check.proofFieldPlan
      info <- projectionInfo
    } yield new ProofRecoveryInfo(fields, info, definitelyComplete)
    val meta = check.initialMeta.copy(
      block = checkedBlock,
      projectionInfo = projectionInfo,
      proofRecovery = proofRecovery
    )

    val inductiveHead = VConst(header.name, Inductive(meta), check.signature.familyType)
    val completeConstructorLink = (finalEnv: Env) =>
      if (decl.ctors.length == 1) {
        val ctorName = decl.ctors.head.canonicalName
        installedCtorHead = Some(
          finalEnv(ctorName) match {
            case h: ConstructorHead => h
            case other              => wtf(s"Constructor $ctorName resolved to non-constructor $other")
          }
        )
        // Complete and validate the circular metadata/head link before publishing the environment.
        projectionInfo.foreach(_.ctorHead)
      }

    PreparedFamily(decl, inductiveHead, completeConstructorLink)
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
    val recursiveScan = new OccurrenceScan(PositivityTarget.InductiveHeads(blockNames), None)
    val checked = provisional.map { case (signature, meta, _) =>
      checkFamilyConstructors(signature, meta, provisionalEnv, block, blockNames, recursiveScan)
    }
    val blockHasRecursiveField = checked.exists(_.hasRecursiveField)
    val positiveParams = computePositiveParams(block, blockKey, checked)
    val checkedBlock = CheckedInductiveBlockSchema(blockKey, positiveParams)
    val prepared = checked.map(check => prepareFamily(check, checkedBlock, blockHasRecursiveField))
    val envWithFinalHeads = prepared.foldLeft(env) { case (curEnv, family) =>
      curEnv.putGlobal(family.decl.header.name, family.head)
    }
    val finalEnv = prepared.foldLeft(envWithFinalHeads) { case (curEnv, family) =>
      installConstructors(family, curEnv)
    }
    prepared.foreach(_.completeConstructorLink(finalEnv))
    finalEnv
  }
}
