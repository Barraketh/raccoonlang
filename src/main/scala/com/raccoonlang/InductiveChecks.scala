package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.collection.immutable.BitSet

object InductiveChecks {
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
  //   structurally, such as neutral computations and axiom applications.
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

        // A proof's interior is erased; its type is all that can carry an occurrence.
        case p: VProof => doesNotOccur(target, p.tpe)

        case p: VPacked => doesNotOccur(target, p.tpe)

        case _: ConstructorHead => !target.mayOccurIn(value)

        case _: Level | _: Kind | _: Lifetime | _: ParameterTpe | SortParameter | Large | _: VLam | _: VSort | _: Var |
            _: VConst =>
          !target.mayOccurIn(value)

        case deferred: DeferredEvidence => deferred.escaped
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
          bodyEnv.locals.values.exists(value => !doesNotOccur(target, value)) || CoreAst.mentionsGlobal(term, names)
        case _: LamBody.Native => true
        case LamBody.ProofEta  => false
      })
    }
  }

  private def thunkMayContain(names: Set[String], thunk: NeutralThunk): Boolean = {
    scanClosure(thunk) {
      val target = PositivityTarget.InductiveHeads(names)
      !doesNotOccur(target, thunk.tpe) || thunk.id.captures.exists(value => !doesNotOccur(target, value)) ||
      thunk.env.locals.values.exists(value => !doesNotOccur(target, value)) ||
      CoreAst.mentionsGlobal(thunk.term, names)
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

        // Strict: a proof value embedded in a type (e.g. an index) must not mention the target in
        // its proposition at all — positivity through an erased interior is unjustifiable.
        case p: VProof => doesNotOccur(target, p.tpe)

        case p: VPacked => doesNotOccur(target, p.tpe)

        case lam: VLam =>
          inspectLambda(lam) { (freshArgs, result) =>
            freshArgs.forall(arg => doesNotOccur(target, arg.tpe)) &&
            occursPositively(target, result, currentBlock)
          }

        case _: ConstructorHead => true

        case _: Level | _: Kind | _: Lifetime | _: ParameterTpe | SortParameter | Large | _: VSort | _: Var |
            _: VConst =>
          true

        case deferred: DeferredEvidence => deferred.escaped
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

      case p: VProof => blockFamilyApplicationsAreUniform(blockNames, target, expectedParams, p.tpe)

      case p: VPacked => blockFamilyApplicationsAreUniform(blockNames, target, expectedParams, p.tpe)

      case lam: VLam =>
        inspectLambda(lam) { (freshArgs, result) =>
          freshArgs.forall(arg =>
            blockFamilyApplicationsAreUniform(blockNames, target, expectedParams, arg.tpe)
          ) && blockFamilyApplicationsAreUniform(blockNames, target, expectedParams, result)
        }

      case VConst(name, Inductive(_), _) if blockNames(name) => false

      case _: ConstructorHead | _: Level | _: Kind | _: Lifetime | _: ParameterTpe | SortParameter | Large | _: VSort |
          _: Var | _: VConst =>
        true

      case deferred: DeferredEvidence => deferred.escaped
    }

  private def constructorFamilyParams(header: InductiveHeader): Vector[Binder] =
    header.params.map(_.copy(mode = BinderMode.Implicit))

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

  /** A constructor's declared type: its family's parameters, implicit, then its fields. */
  private[raccoonlang] def constructorTypeTerm(header: InductiveHeader, ctor: ConstructorDecl): Term = {
    val allBinders = constructorBinders(header, ctor)
    if (allBinders.isEmpty) ctor.resultTy
    else Term.Pi(allBinders, ctor.resultTy, Closure.unrestricted(ctor.span), ctor.span, NodeId.fresh())
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
      family.seal.fold(installed)(installed.sealMember(ctor.canonicalName, _))
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
      constructorSources: Vector[Option[Vector[ProofFieldSource]]],
      proofFieldPlan: Option[(Vector[ProofFieldSource], Boolean)],
      evidenceEligible: Boolean
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
      seal: Option[Sealing.Seal],
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
        Closure.unrestricted(decl.header.span),
        decl.header.span,
        NodeId.fresh()
      )

  private def checkFamilySignatures(block: Decl.InductiveBlock, env: Env): Vector[FamilySignature] = {
    // A family's parameters and indices are explicit or implicit: the parser refuses an evidence binder among them.
    block.families.foreach { decl =>
      decl.header.binders.find(_.mode == BinderMode.Evidence).foreach { binder =>
        wtf(s"Family ${decl.header.name} binds the evidence parameter ${binder.name}")
      }
    }
    val typedFamilies = block.families.map(decl => (decl, TypeChecker.checkDeclType(familyTypeTerm(decl), env).value))
    val coreParamCount = block.families.head.header.params.length
    val expectedModes = block.families.head.header.params.map(_.mode)
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
            if (decl.header.params.map(_.mode) != expectedModes)
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
      // spec §5.1: the declared scope may mention only the family's parameters, and it names each lifetime parameter,
      // so it is exactly their union.
      Sorts.requireNamesLifetimeParameters(
        s"Family ${decl.header.name}",
        declaredSort.scope,
        decl.header.binders.zip(familyArgs)
      )
      FamilySignature(decl, familyType, declaredSort, familyArgs)
    }
  }

  private def initialMeta(
      signature: FamilySignature,
      provisionalBlock: ProvisionalInductiveBlockInfo
  ): InductiveMeta = {
    val decl = signature.decl
    InductiveMeta(
      decl.ctors.map(ctor => ConstructorMeta(ctor.shortName, ctor.canonicalName, fieldSources = None)),
      decl.header.binders.length,
      provisionalBlock,
      projectionInfo = None,
      proofRecovery = None,
      seal = decl.seal,
      evidenceEligible = false
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
    positivityContexts += PositiveParamContext(
      sourceParams,
      signature.familyArgs.drop(sourcePrefixCount).map(_.tpe) :+ signature.declaredSort,
      signature.familyArgs.take(sourcePrefixCount).map(_.tpe)
    )
    var hasRecursiveField = false
    // A family whose declared universe is positive under every level assignment can never have a
    // Prop instance, so proof representation metadata would be dead weight. Retain it only
    // for Prop and universe-polymorphic families whose result level may reduce to zero.
    val mayBeProp = !Level.isNeverZero(signature.declaredSort.level)
    val constructorSources = Vector.newBuilder[Option[Vector[ProofFieldSource]]]
    var proofFieldPlan = Option.empty[(Vector[ProofFieldSource], Boolean)]

    decl.ctors.foreach { ctor =>
      val allConstructorBinders = constructorBinders(header, ctor)
      val checkedBinders =
        BinderOps.checkBinders(allConstructorBinders, provisionalEnv, familyParams = header.params.length, ctor.span)
      val binders = checkedBinders.binders
      val envWithBinders = checkedBinders.env
      val binderVars = binders.map(binder => envWithBinders(binder.localRef))
      val commonParamValues = binderVars.take(header.params.length)
      val ownBinderVars = binderVars.drop(header.params.length)
      val sourceParamValues = commonParamValues
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
      if (
        outputArgs.take(sourceParamValues.length).zip(sourceParamValues).exists { case (actual, expected) =>
          !ValueEquivalence.defEq(actual, expected)
        }
      )
        at(ctor.resultTy.span) {
          fail(
            InvalidInductiveBlock(
              s"constructor ${ctor.canonicalName} does not preserve the complete source parameter prefix"
            )
          )
        }
      if (outputArgs.drop(sourceParamValues.length).exists(arg => !doesNotOccur(recursiveTarget, arg)))
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

      // Compile where each field occurs among the result's arguments, for proof reconstruction and evidence discharge.
      // Whether a field is a proof is classified later at the actual family instance, so universe-polymorphic fields
      // that become proofs at u := 0 need no declaration-time special case.
      val sources = Option.when(mayBeProp) {
        ownBinderVars.map { field =>
          val resultIndex = outputArgs.indexWhere(arg => ValueEquivalence.defEq(arg, field))
          if (resultIndex >= 0) ProofFieldSource.ResultArgument(resultIndex)
          else ProofFieldSource.Unavailable
        }
      }
      constructorSources += sources
      // A one-constructor family's proof-recovery plan.
      if (decl.ctors.length == 1) proofFieldPlan = sources.map { sources =>
        val definitelyComplete = ownBinderVars.zip(sources).forall { case (field, source) =>
          Sorts.isProposition(field.tpe) || source != ProofFieldSource.Unavailable
        }
        (sources, definitelyComplete)
      }

      val constructorUniverse = TypeChecker.getUniverse(outputTpe)
      val constructorArgs = ctor.binders.zip(trueFieldVars)
      val constructorArgTypes = constructorArgs.map(_._2.tpe)
      val fieldDependencies = constructorFieldDependencies(ctor)
      val syntacticallyRecursive = Array.fill(ctor.binders.length)(false)
      ctor.binders.indices.foreach { index =>
        syntacticallyRecursive(index) = CoreAst.mentionsGlobal(ctor.binders(index).ty, blockNames) ||
          fieldDependencies(index).exists(syntacticallyRecursive)
      }
      positivityContexts += PositiveParamContext(
        sourceParamValues,
        outputArgs.drop(sourceParamValues.length),
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
        // Kind bound (spec §5.1), Prop families included: the declared kind, never derived, contains each field's. A
        // sibling's field is read by its declared sort, so no fixed point is needed. The field's scope lies within the
        // declared scope by construction (see checkFamilySignatures).
        Sorts.requireContains(
          Sorts.KindField,
          s"Family $name",
          constructorUniverse.kind,
          ContainedPart.Field(fieldName, field.tpe),
          fieldSort.kind,
          binder.span
        )

        if (!doesNotOccur(recursiveTarget, field.tpe)) hasRecursiveField = true

        // 3) Every true source field type must be strictly positive in every block family.
        if (
          syntacticallyRecursive(sourceFieldIndex) &&
          (!occursPositively(recursiveTarget, field.tpe) ||
            !blockFamilyApplicationsAreUniform(blockNames, recursiveTarget, sourceParamValues, field.tpe))
        )
          at(binder.span) {
            fail(
              NonStrictlyPositive(inductive = name, ctor = ctor.canonicalName, field = binder.name, fieldTy = field.tpe)
            )
          }
      }

    }

    // PROOF_BY_EVALUATION §1.9: declared in Prop itself, one constructor, no indices, every field evidence, and no field
    // type that mentions a family of the block, so each field's type mentions only symbols declared before the family.
    val evidenceEligible = decl.ctors match {
      case Vector(ctor) =>
        Sorts.isProp(signature.declaredSort) && header.indices.isEmpty &&
        ctor.binders.forall(field => field.mode == BinderMode.Evidence && !CoreAst.mentionsGlobal(field.ty, blockNames))
      case _ => false
    }

    CheckedFamily(
      signature,
      meta,
      PositiveParamInputs(positivityContexts.result()),
      hasRecursiveField,
      constructorSources.result(),
      proofFieldPlan,
      evidenceEligible
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
    // is the narrower Lean gate: zero true source indices and no recursive occurrence. Prop instances are filtered
    // dynamically by StructEta.eligibleInstance and follow their declaration-compiled recovery plan.
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
            etaEligible = header.indices.isEmpty && !blockHasRecursiveField,
            () => installedCtorHead
          )
        )
      } else None

    val proofRecovery = for {
      (fields, definitelyComplete) <- check.proofFieldPlan
      info <- projectionInfo
    } yield new ProofRecoveryInfo(fields, info, definitelyComplete)
    val meta = check.initialMeta.copy(
      constructors = check.initialMeta.constructors.zip(check.constructorSources).map { case (ctor, sources) =>
        ctor.copy(fieldSources = sources)
      },
      block = checkedBlock,
      projectionInfo = projectionInfo,
      proofRecovery = proofRecovery,
      evidenceEligible = check.evidenceEligible
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

    PreparedFamily(decl, inductiveHead, meta.seal, completeConstructorLink)
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
