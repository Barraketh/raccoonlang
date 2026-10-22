package com.raccoonlang

import com.raccoonlang.CoreAst._
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.collection.immutable.BitSet

object InductiveChecks {
  // ------------ Occurrence and Positivity ------------

  private sealed trait PositivityTarget {
    def isDirect(value: Value): Boolean
  }

  private object PositivityTarget {
    final case class InductiveBlock(key: InductiveBlockKey) extends PositivityTarget {
      override def isDirect(value: Value): Boolean =
        value match {
          case VConst(name, Inductive(_), _) => key.members.contains(name)
          case _                             => false
        }

    }

    final case class LocalVar(id: VarId) extends PositivityTarget {
      override def isDirect(value: Value): Boolean =
        value match {
          case Var(_, valueId, _) => valueId == id
          case _                  => false
        }

    }
  }

  private final class RelationMemo {
    private val completed = new java.util.IdentityHashMap[Value, java.lang.Boolean]()
    private val active = new java.util.IdentityHashMap[Value, java.lang.Boolean]()

    def apply(value: Value)(compute: => Boolean): Boolean = {
      val known = completed.get(value)
      if (known ne null) known.booleanValue
      else if (active.containsKey(value)) false
      else {
        active.put(value, java.lang.Boolean.TRUE)
        try {
          val result = compute
          completed.put(value, java.lang.Boolean.valueOf(result))
          result
        } finally active.remove(value)
      }
    }
  }

  private def rigidArguments(pi: VPi): (Vector[Value], Env) = {
    val fresh = BinderOps.freshen(pi)
    (pi.binders.map(binder => fresh(binder.localRef)), fresh)
  }

  /** The scans share no state: each relation memo is valid for one declaration-time target and override. */
  private final class BlockScan(key: InductiveBlockKey) {
    private val target: PositivityTarget = PositivityTarget.InductiveBlock(key)
    private val blockNames: Set[String] = key.members.toSet
    private val absentMemo = new RelationMemo
    private val positiveMemo = new RelationMemo

    def absent(value: Value): Boolean = absentMemo(value) {
      if (target.isDirect(value)) false
      else
        value match {
          case thunk: NeutralThunk =>
            absent(thunk.tpe) && thunk.id.captures.forall(absent) && thunk.env.localValuesIterator.forall(absent) &&
            !CoreAst.mentionsGlobal(thunk.term, blockNames)

          case InductiveFamilyValue(instance) =>
            !target.isDirect(instance.head) && instance.args.forall(absent)

          case app: VApp => absent(app.head) && app.args.forall(absent) && absent(app.tpe)

          case pi: VPi =>
            val (args, fresh) = rigidArguments(pi)
            args.forall(arg => absent(arg.tpe)) && absent(pi.codomain(fresh))

          case proof: VProof => absent(proof.tpe)

          case packed: VPacked => absent(packed.tpe)

          case prefix: VNatPrefix => absent(prefix.base) && absent(prefix.tpe)

          case lam: VLam =>
            val captures = lam.id match {
              case ValueId.Const(_)           => Vector.empty
              case ValueId.LocalId(_, values) => values
            }
            absent(lam.tpe) && captures.forall(absent) &&
            (lam.body match {
              case LamBody.Core(term, env) =>
                env.localValuesIterator.forall(absent) && !CoreAst.mentionsGlobal(term, blockNames)
              case LamBody.Native(_, env, _, _, _) => env.localValuesIterator.forall(absent)
              case LamBody.ProofEta                => true
            })

          case _: ConstructorHead | _: Level | _: Kind | _: ParameterTpe | SortParameter | Large | _: VSort | _: Var |
              _: VConst =>
            true

          case deferred: DeferredEvidence => deferred.escaped
        }
    }

    def positive(value: Value): Boolean = positiveMemo(value) {
      if (absent(value)) true
      else if (target.isDirect(value)) true
      else
        value match {
          case _: NeutralThunk => false

          case InductiveFamilyValue(instance) =>
            target.isDirect(instance.head) || instance.args.zipWithIndex.forall { case (arg, index) =>
              if (instance.meta.block.isPositiveCoreArgument(index)) positive(arg) else absent(arg)
            }

          case app: VApp =>
            (target.isDirect(app.head) || absent(app.head)) && app.args.forall(absent) && positive(app.tpe)

          case pi: VPi =>
            val (args, fresh) = rigidArguments(pi)
            args.forall(arg => absent(arg.tpe)) && positive(pi.codomain(fresh))

          case proof: VProof => absent(proof.tpe)

          case packed: VPacked => absent(packed.tpe)

          case prefix: VNatPrefix => absent(prefix.base) && positive(prefix.tpe)

          case lam: VLam =>
            lam.body match {
              case _: LamBody.Native => false
              case LamBody.Core(_, _) | LamBody.ProofEta =>
                val (args, _) = rigidArguments(lam.tpe)
                args.forall(arg => absent(arg.tpe)) && positive(Interpreter.evalApply(lam, args))
            }

          case _: ConstructorHead | _: Level | _: Kind | _: ParameterTpe | SortParameter | Large | _: VSort | _: Var |
              _: VConst =>
            true

          case deferred: DeferredEvidence => deferred.escaped
        }
    }
  }

  private final class LocalScan(id: VarId, overrideInfo: PositiveParamOverride) {
    private val target: PositivityTarget = PositivityTarget.LocalVar(id)
    private val absentMemo = new RelationMemo
    private val positiveMemo = new RelationMemo

    def absent(value: Value): Boolean = absentMemo(value) {
      if (!value.synDeps.contains(id)) true
      else if (target.isDirect(value)) false
      else
        value match {
          case _: NeutralThunk | _: VLam => !value.synDeps.contains(id)

          case InductiveFamilyValue(instance) =>
            !target.isDirect(instance.head) && instance.args.forall(absent)

          case app: VApp => absent(app.head) && app.args.forall(absent) && absent(app.tpe)

          case pi: VPi =>
            val (args, fresh) = rigidArguments(pi)
            args.forall(arg => absent(arg.tpe)) && absent(pi.codomain(fresh))

          case proof: VProof => absent(proof.tpe)

          case packed: VPacked => absent(packed.tpe)

          case prefix: VNatPrefix => absent(prefix.base) && absent(prefix.tpe)

          case _: ConstructorHead | _: Level | _: Kind | _: ParameterTpe | SortParameter | Large | _: VSort | _: Var |
              _: VConst =>
            !value.synDeps.contains(id)

          case deferred: DeferredEvidence => deferred.escaped
        }
    }

    def positive(value: Value): Boolean = positiveMemo(value) {
      if (absent(value)) true
      else if (target.isDirect(value)) true
      else
        value match {
          case _: NeutralThunk => false

          case InductiveFamilyValue(instance) =>
            !target.isDirect(instance.head) && instance.args.zipWithIndex.forall { case (arg, index) =>
              if (overrideInfo.isPositiveArgument(instance.meta, index)) positive(arg) else absent(arg)
            }

          case app: VApp =>
            (target.isDirect(app.head) || absent(app.head)) && app.args.forall(absent) && positive(app.tpe)

          case pi: VPi =>
            val (args, fresh) = rigidArguments(pi)
            args.forall(arg => absent(arg.tpe)) && positive(pi.codomain(fresh))

          case proof: VProof => absent(proof.tpe)

          case packed: VPacked => absent(packed.tpe)

          case prefix: VNatPrefix => absent(prefix.base) && positive(prefix.tpe)

          case lam: VLam =>
            lam.body match {
              case _: LamBody.Native => false
              case LamBody.Core(_, _) | LamBody.ProofEta =>
                val (args, _) = rigidArguments(lam.tpe)
                args.forall(arg => absent(arg.tpe)) && positive(Interpreter.evalApply(lam, args))
            }

          case _: ConstructorHead | _: Level | _: Kind | _: ParameterTpe | SortParameter | Large | _: VSort | _: Var |
              _: VConst =>
            true

          case deferred: DeferredEvidence => deferred.escaped
        }
    }
  }

  private final class UniformScan(
      blockScan: BlockScan,
      blockNames: Set[String],
      expectedParams: Vector[Value]
  ) {
    private val memo = new RelationMemo

    def uniform(value: Value): Boolean = memo(value) {
      if (blockScan.absent(value)) true
      else
        value match {
          case _: NeutralThunk => false

          case InductiveFamilyValue(instance) =>
            if (blockNames(instance.head.name))
              instance.args.length >= expectedParams.length &&
              instance.args.take(expectedParams.length).zip(expectedParams).forall { case (actual, expected) =>
                ValueEquivalence.defEq(actual, expected)
              } && instance.args.drop(expectedParams.length).forall(blockScan.absent)
            else instance.args.forall(uniform)

          case app: VApp =>
            blockScan.absent(app.head) && app.args.forall(uniform) && uniform(app.tpe)

          case pi: VPi =>
            val (args, fresh) = rigidArguments(pi)
            args.forall(arg => uniform(arg.tpe)) && uniform(pi.codomain(fresh))

          case proof: VProof => uniform(proof.tpe)

          case packed: VPacked => uniform(packed.tpe)

          case prefix: VNatPrefix => uniform(prefix.base) && uniform(prefix.tpe)

          case lam: VLam =>
            lam.body match {
              case _: LamBody.Native => false
              case LamBody.Core(_, _) | LamBody.ProofEta =>
                val (args, _) = rigidArguments(lam.tpe)
                args.forall(arg => uniform(arg.tpe)) && uniform(Interpreter.evalApply(lam, args))
            }

          case VConst(name, Inductive(_), _) if blockNames(name) => false

          case _: ConstructorHead | _: Level | _: Kind | _: ParameterTpe | SortParameter | Large | _: VSort | _: Var |
              _: VConst =>
            true

          case deferred: DeferredEvidence => deferred.escaped
        }
    }
  }

  private final case class PositiveParamOverride(key: InductiveBlockKey, positiveParams: DepSet) {
    def isPositiveArgument(meta: InductiveMeta, index: Int): Boolean =
      if (meta.block.key == key) positiveParams.contains(index)
      else meta.block.isPositiveCoreArgument(index)
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
    def accepts(sourceIndex: Int, overrideInfo: PositiveParamOverride): Boolean =
      contexts.forall(_.accepts(sourceIndex, overrideInfo))
  }

  private final case class PositiveParamContext(
      sourceParams: Vector[Value],
      forbiddenValues: Vector[Value],
      positiveValues: Vector[Value]
  ) {
    def accepts(sourceIndex: Int, overrideInfo: PositiveParamOverride): Boolean =
      sourceParams(sourceIndex) match {
        case Var(_, id, _) =>
          val scan = new LocalScan(id, overrideInfo)
          forbiddenValues.forall(scan.absent) && positiveValues.forall(scan.positive)
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

  /** The code stores one argument value; Pi domains still store a whole function graph. */
  private def familyArgumentLevel(tpe: Value): Level = tpe match {
    case _: ParameterTpe => Level.zero
    case sort: VSort     => if (sort.isProp) Level.zero else sort.level
    case pi: VPi if !pi.isPropValued =>
      val fresh = BinderOps.freshen(pi.binders, pi.env)
      val domains = pi.binders.map { binder =>
        fresh(binder.localRef).tpe match {
          case _: ParameterTpe => Level.zero
          case domain          => TypeChecker.getUniverse(domain).level
        }
      }
      Level.max(domains :+ familyArgumentLevel(pi.codomain(fresh)))
    case other => TypeChecker.getUniverse(other).level
  }

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
      if (!declaredSort.isProp)
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
      blockNames: Set[String],
      blockScan: BlockScan
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
    // Proof recovery is needed only for families declared in Prop.
    val isPropFamily = Sorts.isProp(signature.declaredSort)
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
      if (outputArgs.drop(sourceParamValues.length).exists(arg => !blockScan.absent(arg)))
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
      // Whether a field is a proof is classified later at the actual family instance, including fields whose type
      // is supplied by a proposition parameter.
      val sources = Option.when(isPropFamily) {
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
      val uniformScan = new UniformScan(blockScan, blockNames, sourceParamValues)

      constructorArgs.zipWithIndex.foreach { case ((binder, field), sourceFieldIndex) =>
        def fieldName = s"${ctor.canonicalName}.${binder.name}"
        val fieldSort = TypeChecker.getUniverse(field.tpe)
        // 2) Universe bound: skip for Prop families; enforce for Sort families
        if (
          !Sorts.isProp(constructorUniverse) && !Sorts
            .isProp(fieldSort) && !Level.leq(fieldSort.level, constructorUniverse.level)
        )
          at(binder.span) {
            fail(InductiveUniverseTooSmall(name, fieldName, field.tpe, fieldSort.level, constructorUniverse.level))
          }
        // Kind bound (spec §5.1), Prop families included: the declared kind, never derived, contains each field's. A
        // sibling's field is read by its declared sort, so no fixed point is needed.
        Sorts.requireContains(
          Sorts.KindField,
          s"Family $name",
          constructorUniverse.kind,
          ContainedPart.Field(fieldName, field.tpe),
          fieldSort.kind,
          binder.span
        )

        if (syntacticallyRecursive(sourceFieldIndex) && !blockScan.absent(field.tpe)) hasRecursiveField = true

        // 3) Every true source field type must be strictly positive in every block family.
        if (
          syntacticallyRecursive(sourceFieldIndex) &&
          (!blockScan.positive(field.tpe) || !uniformScan.uniform(field.tpe))
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
      val overrideInfo = PositiveParamOverride(blockKey, current)
      val next = DepSet.newBuilder
      current.foreach { sourceIndex =>
        if (checked.forall(_.positivityInputs.accepts(sourceIndex, overrideInfo))) next.add(sourceIndex)
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
    // is the narrower gate: Type family, zero true source indices and no recursive occurrence.
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
    val blockScan = new BlockScan(blockKey)
    val checked = provisional.map { case (signature, meta, _) =>
      checkFamilyConstructors(signature, meta, provisionalEnv, block, blockNames, blockScan)
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
