package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/** Kernel-owned, target-independent occurrence and strict-positivity metadata for Values. */
private[raccoonlang] object ValueAnalysis {
  private sealed trait GlobalTargets {
    def contains(name: String): Boolean
    def union(other: GlobalTargets): GlobalTargets
    def without(name: String): GlobalTargets
    def without(block: InductiveBlockKey): GlobalTargets
    def intersects(block: InductiveBlockKey): Boolean = block.members.exists(contains)
  }

  private final case class FiniteGlobals(names: Set[String]) extends GlobalTargets {
    override def contains(name: String): Boolean = names(name)

    override def union(other: GlobalTargets): GlobalTargets = other match {
      case FiniteGlobals(otherNames) => finite(names union otherNames)
      case CofiniteGlobals(excluded) => cofinite(excluded -- names)
    }

    override def without(name: String): GlobalTargets = finite(names - name)

    override def without(block: InductiveBlockKey): GlobalTargets = finite(names -- block.members)
  }

  private final case class CofiniteGlobals(excluded: Set[String]) extends GlobalTargets {
    override def contains(name: String): Boolean = !excluded(name)

    override def union(other: GlobalTargets): GlobalTargets = other match {
      case FiniteGlobals(names)       => cofinite(excluded -- names)
      case CofiniteGlobals(otherExcl) => cofinite(excluded intersect otherExcl)
    }

    override def without(name: String): GlobalTargets = cofinite(excluded + name)

    override def without(block: InductiveBlockKey): GlobalTargets = cofinite(excluded ++ block.members)
  }

  private def finite(names: Set[String]): GlobalTargets = FiniteGlobals(names)
  private def cofinite(excluded: Set[String]): GlobalTargets = CofiniteGlobals(excluded)

  private sealed trait LocalTargets {
    def contains(id: VarId): Boolean
    def union(other: LocalTargets): LocalTargets
    def without(id: VarId): LocalTargets
  }

  private final case class FiniteLocals(ids: DepSet) extends LocalTargets {
    override def contains(id: VarId): Boolean = ids.contains(id)

    override def union(other: LocalTargets): LocalTargets = other match {
      case FiniteLocals(otherIds)   => finiteLocals(ids ++ otherIds)
      case CofiniteLocals(excluded) => cofiniteLocals(excluded -- ids)
    }

    override def without(id: VarId): LocalTargets = finiteLocals(ids -- DepSet(id))
  }

  private final case class CofiniteLocals(excluded: DepSet) extends LocalTargets {
    override def contains(id: VarId): Boolean = !excluded.contains(id)

    override def union(other: LocalTargets): LocalTargets = other match {
      case FiniteLocals(ids)         => cofiniteLocals(excluded -- ids)
      case CofiniteLocals(otherExcl) => cofiniteLocals(excluded & otherExcl)
    }

    override def without(id: VarId): LocalTargets = cofiniteLocals(excluded + id)
  }

  private def finiteLocals(ids: DepSet): LocalTargets = FiniteLocals(ids)
  private def cofiniteLocals(excluded: DepSet): LocalTargets = CofiniteLocals(excluded)

  private[raccoonlang] final class TargetSet private[ValueAnalysis] (
      private val globals: GlobalTargets,
      private val locals: LocalTargets
  ) {
    def union(other: TargetSet): TargetSet =
      new TargetSet(globals.union(other.globals), locals.union(other.locals))

    def containsLocal(id: VarId): Boolean = locals.contains(id)

    def containsBlock(key: InductiveBlockKey): Boolean = globals.intersects(key)

    private[ValueAnalysis] def globalOnly: TargetSet = new TargetSet(globals, finiteLocals(DepSet.empty))

    private[ValueAnalysis] def withoutBlock(key: InductiveBlockKey): TargetSet =
      new TargetSet(globals.without(key), locals)

    private[ValueAnalysis] def withoutDirect(value: Value): TargetSet =
      value match {
        case Var(_, id, _)                 => new TargetSet(globals, locals.without(id))
        case VConst(name, Inductive(_), _) => new TargetSet(globals.without(name), locals)
        case _                             => this
      }
  }

  private val emptyTargets = new TargetSet(finite(Set.empty), finiteLocals(DepSet.empty))
  private val unknownGlobals = new TargetSet(cofinite(Set.empty), finiteLocals(DepSet.empty))
  private val unknownTargets = new TargetSet(cofinite(Set.empty), cofiniteLocals(DepSet.empty))

  private[raccoonlang] final class OccurrenceSummary private[ValueAnalysis] (
      private[ValueAnalysis] val targets: TargetSet
  ) {
    def containsLocal(id: VarId): Boolean = targets.containsLocal(id)

    /** The only global-family query: a complete canonical block key. */
    def containsBlock(key: InductiveBlockKey): Boolean = targets.containsBlock(key)
  }

  private val emptyOccurrences = new OccurrenceSummary(emptyTargets)
  private val unknownOccurrences = new OccurrenceSummary(unknownTargets)

  private[raccoonlang] final class RigidTelescope private[ValueAnalysis] (
      val domains: Vector[Value],
      private val result: Option[Value],
      val isUnknown: Boolean
  ) {
    require(isUnknown == result.isEmpty, "Rigid telescope result must match its inspection state")

    def knownResult: Value = result.getOrElse(wtf("Unknown rigid telescope result was inspected"))
  }

  private[raccoonlang] object RigidTelescope {
    val unknown: RigidTelescope = new RigidTelescope(Vector.empty, None, isUnknown = true)
  }

  private[raccoonlang] sealed abstract class ForbiddenExpr private[ValueAnalysis] (
      private[ValueAnalysis] val dependencies: Set[InductiveBlockKey],
      private[ValueAnalysis] val constant: Option[TargetSet]
  ) {
    final def resolve(context: ResolutionContext): TargetSet = context.resolve(this)

    final def forbidsLocal(id: VarId, context: ResolutionContext): Boolean = resolve(context).containsLocal(id)

    final def forbidsBlock(key: InductiveBlockKey, context: ResolutionContext): Boolean =
      resolve(context).containsBlock(key)
  }

  private final class ConstantExpr(targets: TargetSet) extends ForbiddenExpr(Set.empty, Some(targets)) {}

  private final class UnionExpr(left: ForbiddenExpr, right: ForbiddenExpr)
    extends ForbiddenExpr(left.dependencies union right.dependencies, None) {
    private[ValueAnalysis] def resolveChildren(context: ResolutionContext): TargetSet =
      left.resolve(context).union(right.resolve(context))
  }

  private final class ExcludeBlockExpr(expr: ForbiddenExpr, block: InductiveBlockKey)
    extends ForbiddenExpr(expr.dependencies, None) {
    private[ValueAnalysis] def resolveChild(context: ResolutionContext): TargetSet =
      expr.resolve(context).withoutBlock(block)
  }

  private final class ConditionalArgumentExpr(
      block: InductiveBlockDescriptor,
      index: Int,
      positive: ForbiddenExpr,
      occurrence: TargetSet
  ) extends ForbiddenExpr(positive.dependencies + block.key, None) {
    private[ValueAnalysis] def resolveChoice(context: ResolutionContext): TargetSet =
      if (context.isPositive(block, index)) positive.resolve(context) else occurrence
  }

  private val emptyForbidden = new ConstantExpr(emptyTargets)
  private val unknownForbidden = new ConstantExpr(unknownTargets)

  private def constant(targets: TargetSet): ForbiddenExpr =
    if (targets eq emptyTargets) emptyForbidden
    else if (targets eq unknownTargets) unknownForbidden
    else new ConstantExpr(targets)

  private def union(left: ForbiddenExpr, right: ForbiddenExpr): ForbiddenExpr =
    (left.constant, right.constant) match {
      case (Some(leftTargets), Some(rightTargets)) => constant(leftTargets.union(rightTargets))
      case _                                       => new UnionExpr(left, right)
    }

  private def unionAll(expressions: IterableOnce[ForbiddenExpr]): ForbiddenExpr =
    expressions.iterator.foldLeft[ForbiddenExpr](emptyForbidden)(union)

  private def excludeBlock(expr: ForbiddenExpr, block: InductiveBlockKey): ForbiddenExpr =
    expr.constant match {
      case Some(targets) => constant(targets.withoutBlock(block))
      case None          => new ExcludeBlockExpr(expr, block)
    }

  private def conditionalArgument(
      block: InductiveBlockDescriptor,
      index: Int,
      positive: ForbiddenExpr,
      occurrence: TargetSet
  ): ForbiddenExpr =
    positive.constant match {
      case Some(targets) if targets eq occurrence => constant(targets)
      case _                                      => new ConditionalArgumentExpr(block, index, positive, occurrence)
    }

  private[raccoonlang] final class ResolutionContext private[ValueAnalysis] (
      overrideKey: Option[InductiveBlockKey],
      overridePositive: DepSet
  ) {
    private val resolved = new java.util.IdentityHashMap[ForbiddenExpr, TargetSet]()

    private[ValueAnalysis] def resolve(expr: ForbiddenExpr): TargetSet = {
      val cached = resolved.get(expr)
      if (cached ne null) return cached
      val result = expr match {
        case constant: ConstantExpr            => constant.constant.get
        case union: UnionExpr                  => union.resolveChildren(this)
        case excluded: ExcludeBlockExpr        => excluded.resolveChild(this)
        case argument: ConditionalArgumentExpr => argument.resolveChoice(this)
      }
      resolved.put(expr, result)
      result
    }

    private[ValueAnalysis] def isPositive(block: InductiveBlockDescriptor, index: Int): Boolean =
      if (overrideKey.contains(block.key)) overridePositive.contains(index)
      else block.isPositiveCoreArgument(index)
  }

  private[raccoonlang] def resolutionContext(
      overrideKey: Option[InductiveBlockKey],
      overridePositive: DepSet
  ): ResolutionContext = new ResolutionContext(overrideKey, overridePositive)

  private[raccoonlang] def defaultResolutionContext: ResolutionContext = resolutionContext(None, DepSet.empty)

  private val activeOccurrences = new ThreadLocal[java.util.IdentityHashMap[Value, java.lang.Boolean]] {
    override def initialValue(): java.util.IdentityHashMap[Value, java.lang.Boolean] =
      new java.util.IdentityHashMap[Value, java.lang.Boolean]()
  }

  private val activePositivity = new ThreadLocal[java.util.IdentityHashMap[Value, java.lang.Boolean]] {
    override def initialValue(): java.util.IdentityHashMap[Value, java.lang.Boolean] =
      new java.util.IdentityHashMap[Value, java.lang.Boolean]()
  }

  private val activeInspections = new ThreadLocal[java.util.IdentityHashMap[Value, java.lang.Boolean]] {
    override def initialValue(): java.util.IdentityHashMap[Value, java.lang.Boolean] =
      new java.util.IdentityHashMap[Value, java.lang.Boolean]()
  }

  private def guarded[A](
      active: ThreadLocal[java.util.IdentityHashMap[Value, java.lang.Boolean]],
      value: Value,
      unknown: => A
  )(body: => A): A = {
    val values = active.get()
    if (values.containsKey(value)) unknown
    else {
      values.put(value, java.lang.Boolean.TRUE)
      try body
      finally {
        values.remove(value)
        if (values.isEmpty) active.remove()
      }
    }
  }

  private[raccoonlang] def withOccurrenceGuard(value: Value)(body: => OccurrenceSummary): OccurrenceSummary =
    guarded(activeOccurrences, value, unknownOccurrences)(body)

  private[raccoonlang] def withPositivityGuard(value: Value)(body: => ForbiddenExpr): ForbiddenExpr =
    guarded[ForbiddenExpr](activePositivity, value, unknownForbidden)(body)

  private[raccoonlang] def withInspectionGuard(value: Value, unknown: RigidTelescope)(
      body: => RigidTelescope
  ): RigidTelescope = guarded(activeInspections, value, unknown)(body)

  private def occurrence(targets: TargetSet): OccurrenceSummary =
    if (targets eq emptyTargets) emptyOccurrences
    else if (targets eq unknownTargets) unknownOccurrences
    else new OccurrenceSummary(targets)

  private def fromLocals(ids: DepSet): TargetSet = new TargetSet(finite(Set.empty), finiteLocals(ids))

  private def globals(names: Set[String]): TargetSet = new TargetSet(finite(names), finiteLocals(DepSet.empty))

  private def withGlobal(targets: TargetSet, name: String): TargetSet = targets.union(globals(Set(name)))

  private def unionOccurrences(values: IterableOnce[Value]): TargetSet =
    values.iterator.foldLeft(emptyTargets)((acc, value) => acc.union(value.occurrences.targets))

  private def lambdaCaptures(lambda: VLam): Vector[Value] =
    lambda.id match {
      case ValueId.Const(_)             => Vector.empty
      case ValueId.LocalId(_, captures) => captures
    }

  private def closureGlobals(
      tpe: Value,
      captures: Vector[Value],
      environment: Iterator[Value],
      codeNames: Set[String]
  ): TargetSet = {
    var result = tpe.occurrences.targets.globalOnly
    result = result.union(unionOccurrences(captures).globalOnly)
    result = result.union(unionOccurrences(environment).globalOnly)
    result.union(globals(codeNames))
  }

  private def closureOccurrence(value: Value, globalTargets: TargetSet): OccurrenceSummary =
    occurrence(globalTargets.union(fromLocals(value.synDeps)))

  private[raccoonlang] def buildPiTelescope(pi: VPi): RigidTelescope = {
    val freshEnv = BinderOps.freshen(pi)
    val freshArgs = pi.binders.map(binder => freshEnv(binder.localRef))
    new RigidTelescope(freshArgs.map(_.tpe), Some(pi.codomain(freshEnv)), isUnknown = false)
  }

  private[raccoonlang] def buildLambdaResult(lambda: VLam): RigidTelescope =
    if (lambda.body.isInstanceOf[LamBody.Native]) RigidTelescope.unknown
    else {
      val freshEnv = BinderOps.freshen(lambda.tpe)
      val freshArgs = lambda.tpe.binders.map(binder => freshEnv(binder.localRef))
      new RigidTelescope(freshArgs.map(_.tpe), Some(Interpreter.evalApply(lambda, freshArgs)), isUnknown = false)
    }

  private[raccoonlang] def buildOccurrences(value: Value): OccurrenceSummary =
    value match {
      case InductiveFamilyValue(instance) =>
        val familyName = globals(Set(instance.head.name))
        occurrence(familyName.union(unionOccurrences(instance.args)))

      case app: VApp =>
        occurrence(app.head.occurrences.targets.union(unionOccurrences(app.args)).union(app.tpe.occurrences.targets))

      case pi: VPi =>
        val telescope = pi.analysisTelescope
        if (telescope.isUnknown) unknownOccurrences
        else occurrence(unionOccurrences(telescope.domains :+ telescope.knownResult))

      case thunk: NeutralThunk =>
        val captures = thunk.id.captures
        val globalTargets = closureGlobals(
          thunk.tpe,
          captures,
          thunk.env.localValuesIterator,
          CoreAst.globalNames(thunk.term)
        )
        closureOccurrence(thunk, globalTargets)

      case lambda: VLam =>
        val body = lambda.body match {
          case LamBody.Core(term, env) =>
            closureGlobals(lambda.tpe, lambdaCaptures(lambda), env.localValuesIterator, CoreAst.globalNames(term))
          case _: LamBody.Native => unknownGlobals.union(fromLocals(lambda.synDeps))
          case LamBody.ProofEta  => closureGlobals(lambda.tpe, lambdaCaptures(lambda), Iterator.empty, Set.empty)
        }
        if (lambda.body.isInstanceOf[LamBody.Native]) occurrence(body)
        else closureOccurrence(lambda, body)

      case proof: VProof => proof.tpe.occurrences

      case packed: VPacked => packed.tpe.occurrences

      case _: ConstructorHead => occurrence(fromLocals(value.synDeps))

      case Var(_, _, _) => occurrence(fromLocals(value.synDeps))

      case VConst(name, Inductive(_), _) => occurrence(withGlobal(fromLocals(value.synDeps), name))

      case _: DeferredEvidence => value.asInstanceOf[DeferredEvidence].escaped

      case _: Level | _: Kind | _: Lifetime | _: ParameterTpe | SortParameter | Large | _: VSort =>
        occurrence(fromLocals(value.synDeps))

      case constant: VConst => occurrence(fromLocals(constant.synDeps))
    }

  private def forbiddenFromOccurrence(value: Value): ForbiddenExpr = constant(value.occurrences.targets)

  private def familyArgumentForbidden(instance: InductiveFamilyInstance, index: Int, arg: Value): ForbiddenExpr = {
    val block = instance.meta.block
    val argument = block match {
      case provisional: ProvisionalInductiveBlockInfo if index < provisional.key.numParams =>
        conditionalArgument(provisional, index, arg.positivity, arg.occurrences.targets)
      case checked: CheckedInductiveBlockSchema if checked.isPositiveCoreArgument(index) => arg.positivity
      case _                                                                             => forbiddenFromOccurrence(arg)
    }
    excludeBlock(argument, block.key)
  }

  private[raccoonlang] def buildPositivity(value: Value): ForbiddenExpr =
    value match {
      case _: NeutralThunk => forbiddenFromOccurrence(value)

      case InductiveFamilyValue(instance) =>
        unionAll(instance.args.zipWithIndex.map { case (arg, index) => familyArgumentForbidden(instance, index, arg) })

      case app: VApp =>
        val head = app.head.occurrences.targets.withoutDirect(app.head)
        unionAll(
          Iterator(constant(head)) ++
            app.args.iterator.map(forbiddenFromOccurrence) ++
            Iterator(app.tpe.positivity)
        )

      case pi: VPi =>
        val telescope = pi.analysisTelescope
        if (telescope.isUnknown) unknownForbidden
        else
          unionAll(
            telescope.domains.iterator.map(forbiddenFromOccurrence) ++ Iterator(telescope.knownResult.positivity)
          )

      case lambda: VLam =>
        if (lambda.body.isInstanceOf[LamBody.Native]) unknownForbidden
        else {
          val inspection = lambda.analysisResult
          if (inspection.isUnknown) unknownForbidden
          else
            unionAll(
              inspection.domains.iterator.map(forbiddenFromOccurrence) ++ Iterator(inspection.knownResult.positivity)
            )
        }

      case proof: VProof => forbiddenFromOccurrence(proof.tpe)

      case packed: VPacked => forbiddenFromOccurrence(packed.tpe)

      case _: ConstructorHead => emptyForbidden

      case _: Level | _: Kind | _: Lifetime | _: ParameterTpe | SortParameter | Large | _: Var | _: VConst | _: VSort =>
        emptyForbidden

      case _: DeferredEvidence => value.asInstanceOf[DeferredEvidence].escaped
    }
}
