package com.raccoonlang

import com.raccoonlang.CoreAst.{Binder, LocalRef}
import com.raccoonlang.CoreAst.Term
import com.raccoonlang.LeanExportIr._
import com.raccoonlang.Value.{LevelTpe, VPi}
import com.raccoonlang.telescope.{BinderOps, Projection}

private[raccoonlang] object LeanTermLowerer {
  def freshLocal(name: String): LocalRef = SyntheticLocalRef.fresh(name)
  final case class LoweredDeclarationType(
      term: Term,
      pi: Option[Term.Pi],
      universeBinders: Int,
      sourceBinders: Int,
      levelRefs: Map[NameId, LocalRef],
      sourceInfos: Vector[BinderInfo],
      convention: Option[ImportedCallingConvention]
  )
  final case class Context(locals: Vector[LocalRef], levels: Map[NameId, LocalRef], env: Env, depth: Int = 0)
  final case class CheckedSourceArgs(core: Vector[Term], explicitCore: Vector[Term])
}

private[raccoonlang] final class LeanTermLowerer(
    tables: ExportTables,
    kernelEnv: Env,
    registry: LeanGlobalRegistry,
    declaration: String
) {
  import LeanTermLowerer.{CheckedSourceArgs, Context, LoweredDeclarationType}

  private val sourceId = SourceId.fresh()
  private var nextSpan = 0
  private val MaxLoweringDepth = 512

  private val BootstrapNames = Set(
    "Sort",
    "Level.succ",
    "Level.max",
    "Level.imax",
    "Type",
    "Level",
    "Level.zero",
    "Level.one",
    "Prop"
  )

  def lowerDeclarationType(levelParams: Vector[NameId], expr: ExprId): LoweredDeclarationType = {
    if (levelParams.distinct.length != levelParams.length)
      throw UnknownLevelParameter(
        atExpr(expr),
        s"declaration $declaration has duplicate universe parameters",
        Some(declaration)
      )

    var context = Context(Vector.empty, Map.empty, kernelEnv)
    val binders = Vector.newBuilder[Binder]
    val sourceDescriptors = Vector.newBuilder[ImportedSourceBinder]
    val levelPairs = levelParams.map { id =>
      val binder = Binder(
        LeanTermLowerer.freshLocal(displayName(id, "u")),
        Term.GlobalRef("Level", span()),
        span(),
        isImplicit = true
      )
      binders += binder
      sourceDescriptors += SourceUniverseParameter
      context = bindFresh(context.copy(levels = context.levels + (id -> binder.localRef)), binder)
      id -> binder.localRef
    }

    var current = stripMData(expr)
    val sourceInfos = Vector.newBuilder[BinderInfo]
    var continue = true
    while (continue) {
      tables.exprNode(current) match {
        case ForallE(name, binderType, body, info) =>
          val binder = Binder(
            LeanTermLowerer.freshLocal(displayName(name, "x")),
            lowerTerm(binderType, context),
            span(),
            requestedImplicit(info)
          )
          binders += binder
          sourceDescriptors += SourceTermBinder(info)
          sourceInfos += info
          context = bindFresh(context.copy(locals = binder.localRef +: context.locals), binder)
          current = stripMData(body)
        case _ => continue = false
      }
    }
    val out = lowerTerm(current, context)
    val requestedBinders = binders.result()
    if (requestedBinders.isEmpty)
      LoweredDeclarationType(out, None, 0, 0, Map.empty, Vector.empty, None)
    else {
      val checked = BinderOps.checkImportedBinders(requestedBinders, kernelEnv)
      val finalBinders = requestedBinders.zip(checked.binders).map { case (core, result) =>
        core.copy(isImplicit = result.isImplicit)
      }
      val pi = Term.Pi(finalBinders, out, span())
      val descriptors = sourceDescriptors.result()
      val infos = sourceInfos.result()
      val importedBinders = finalBinders.indices.map { idx =>
        ImportedBinder(
          idx,
          descriptors(idx),
          finalBinders(idx).localRef,
          requestedBinders(idx).isImplicit,
          finalBinders(idx).isImplicit
        )
      }.toVector
      val convention = ImportedCallingConvention(levelParams.length, Vector(ImportedTelescope(importedBinders, pi)))
      LoweredDeclarationType(pi, Some(pi), levelParams.length, infos.length, levelPairs.toMap, infos, Some(convention))
    }
  }

  def lowerDeclarationBody(expr: ExprId, declared: LoweredDeclarationType, name: String): Term = {
    declared.pi match {
      case Some(pi) if declared.universeBinders > 0 =>
        val universeBinders = pi.binders.take(declared.universeBinders)
        val termBinders = pi.binders.drop(declared.universeBinders)
        val bodyType =
          if (termBinders.isEmpty) pi.out
          else Term.Pi(termBinders, pi.out, span())
        val universeContext = universeBinders.foldLeft(Context(Vector.empty, declared.levelRefs, kernelEnv)) {
          case (context, binder) => bindFresh(context, binder)
        }
        val expected = TypeChecker.checkTerm(bodyType, universeContext.env).value
        val lowered = lowerExpected(expr, expected, universeContext, declared.sourceInfos)
        val body =
          if (termBinders.isEmpty) lowered
          else {
            val explicit = termBinders.collect {
              case binder if !binder.isImplicit => Term.LocalRef(binder.localRef, span())
            }
            Term.App(lowered, explicit, span())
          }
        val lambda = Term.Lam(pi, body, span(), Some(name), recursion = None)
        TypeChecker.checkTerm(lambda, kernelEnv)
        lambda
      case Some(pi) =>
        val expected = TypeChecker.checkTerm(pi, kernelEnv).value
        lowerExpected(
          expr,
          expected,
          Context(Vector.empty, declared.levelRefs, kernelEnv),
          declared.sourceInfos,
          Some(name)
        )
      case None =>
        val expected = TypeChecker.checkTerm(declared.term, kernelEnv).value
        lowerExpected(expr, expected, Context(Vector.empty, declared.levelRefs, kernelEnv), Vector.empty, Some(name))
    }
  }

  def lowerTerm(expr: ExprId): Term = lowerTerm(expr, Context(Vector.empty, Map.empty, kernelEnv))

  private def lowerTerm(expr: ExprId, context: Context): Term = {
    val nested = enter(expr, context)
    lowerTermAt(stripMData(expr), nested)
  }

  private def enter(expr: ExprId, context: Context): Context = {
    if (context.depth >= MaxLoweringDepth)
      throw BodyLowering(
        atExpr(expr),
        s"expression nesting exceeds the $MaxLoweringDepth-node lowering limit",
        Some(declaration)
      )
    context.copy(depth = context.depth + 1)
  }

  private def lowerTermAt(expr: ExprId, context: Context): Term = tables.exprNode(expr) match {
    case BVar(index) =>
      if (index >= context.locals.length)
        throw BadBVar(
          atExpr(expr),
          s"bound-variable index $index is outside ${context.locals.length} local binders",
          Some(declaration)
        )
      Term.LocalRef(context.locals(index), span())
    case Sort(level)         => builtinApp("Sort", Vector(lowerLevel(level, context)))
    case _: Const            => lowerApplication(expr, context)
    case ForallE(_, _, _, _) => lowerPi(expr, context)
    case Lam(_, _, _, _) =>
      throw BodyLowering(atExpr(expr), "a lambda requires an expected function type", Some(declaration))
    case App(_, _)           => lowerApplication(expr, context)
    case LetE(_, _, _, _, _) => lowerLets(expr, context, None)
    case Proj(typeName, fieldIndex, struct) =>
      val coreName = requireInstalled(typeName, expr)
      Term.Proj(coreName, fieldIndex, lowerTerm(struct, context), span())
    case NatVal(value) =>
      if (context.env.nativeLiterals.natLayout.isEmpty)
        throw MissingKernelGate(atExpr(expr), "Nat literal requires a validated Nat layout", Some(declaration))
      Term.NatLit(value, span())
    case StrVal(scalars) =>
      if (context.env.nativeLiterals.stringLayout.isEmpty)
        throw MissingKernelGate(atExpr(expr), "String literal requires a validated String layout", Some(declaration))
      Term.StrLit(scalars, span())
    case MData(_) => throw new IllegalStateException("stripMData returned metadata")
  }

  private def lowerExpected(
      expr: ExprId,
      expected: Value,
      context: Context,
      expectedInfos: Vector[BinderInfo] = Vector.empty,
      lambdaName: Option[String] = None
  ): Term = {
    val current = stripMData(expr)
    tables.exprNode(current) match {
      case _: Lam =>
        expected match {
          case pi: VPi => lowerLambda(current, pi, enter(current, context), expectedInfos, lambdaName)
          case _ => throw BodyLowering(atExpr(expr), "lambda is checked against a non-function type", Some(declaration))
        }
      case LetE(_, _, _, _, _) =>
        lowerLets(current, enter(current, context), Some((expected, expectedInfos, lambdaName)))
      case _ =>
        val term = lowerTerm(current, context)
        TypeChecker.checkTerm(term, expected, context.env)
        term
    }
  }

  private def lowerLambda(
      start: ExprId,
      expected: VPi,
      context: Context,
      expectedInfos: Vector[BinderInfo],
      lambdaName: Option[String]
  ): Term = {
    val pi = quoteFreshPi(expected, context)
    var current = stripMData(start)
    var nextContext = context
    var idx = 0
    var continue = true
    while (continue && idx < pi.binders.length) {
      tables.exprNode(current) match {
        case Lam(_, annotation, body, info) =>
          val binder = pi.binders(idx)
          if (expectedInfos.lift(idx).exists(_ != info))
            throw InvalidBinderMetadata(
              atExpr(current),
              s"lambda binder $idx metadata disagrees with its expected Pi binder",
              Some(declaration)
            )
          val annotationValue = TypeChecker.getType(lowerTerm(annotation, nextContext), nextContext.env)
          val expectedValue = TypeChecker.checkTerm(binder.ty, nextContext.env).value
          if (!ValueEquivalence.defEq(annotationValue, expectedValue))
            throw InvalidBinderMetadata(atExpr(current), s"lambda binder $idx has the wrong type", Some(declaration))
          nextContext = bindFresh(nextContext.copy(locals = binder.localRef +: nextContext.locals), binder)
          current = stripMData(body)
          idx += 1
        case _ => continue = false
      }
    }
    if (idx == 0)
      throw BodyLowering(atExpr(current), "expected a lambda while checking a function", Some(declaration))
    if (idx == pi.binders.length) {
      val bodyExpected = TypeChecker.checkTerm(pi.out, nextContext.env).value
      Term.Lam(
        pi,
        lowerExpected(current, bodyExpected, nextContext, expectedInfos.drop(idx)),
        span(),
        name = lambdaName,
        recursion = None
      )
    } else {
      val missing = pi.binders.drop(idx)
      val remainingType = Term.Pi(missing, pi.out, span())
      val remainingExpected = TypeChecker.checkTerm(remainingType, nextContext.env).value
      val function = lowerExpected(current, remainingExpected, nextContext, expectedInfos.drop(idx))
      val bodyContext = missing.foldLeft(nextContext) { case (currentContext, binder) =>
        bindFresh(currentContext.copy(locals = binder.localRef +: currentContext.locals), binder)
      }
      val explicit = missing.collect {
        case binder if !binder.isImplicit => Term.LocalRef(binder.localRef, span())
      }
      val body = Term.App(function, explicit, span())
      TypeChecker.checkTerm(body, TypeChecker.checkTerm(pi.out, bodyContext.env).value, bodyContext.env)
      Term.Lam(pi, body, span(), name = lambdaName, recursion = None)
    }
  }

  private def lowerLets(
      start: ExprId,
      initial: Context,
      expectedResult: Option[(Value, Vector[BinderInfo], Option[String])]
  ): Term.Body = {
    val lets = Vector.newBuilder[CoreAst.Let]
    var context = initial
    var current = stripMData(start)
    var continue = true
    while (continue) tables.exprNode(current) match {
      case LetE(name, binderType, value, body, nonDependent) =>
        if (nonDependent && mentionsBound(body, 0))
          throw InvalidBinderMetadata(
            atExpr(current),
            "let is marked nondependent but its body uses the bound value",
            Some(declaration)
          )
        val tpe = lowerTerm(binderType, context)
        val expected = TypeChecker.getType(tpe, context.env)
        val loweredValue = lowerExpected(value, expected, context, sourceBinderInfos(binderType))
        val checkedValue = TypeChecker.checkTerm(loweredValue, expected, context.env).value
        val ref = LeanTermLowerer.freshLocal(displayName(name, "let"))
        lets += CoreAst.Let(ref, Some(tpe), loweredValue, span())
        context = context.copy(
          locals = ref +: context.locals,
          env = context.env.putLocal(ref, Value.ascribe(checkedValue, expected))
        )
        current = stripMData(body)
      case _ => continue = false
    }
    val result = expectedResult match {
      case Some((expected, infos, name)) => lowerExpected(current, expected, context, infos, name)
      case None                          => lowerTerm(current, context)
    }
    Term.Body(lets.result(), result, span())
  }

  private def sourceBinderInfos(start: ExprId): Vector[BinderInfo] = {
    val result = Vector.newBuilder[BinderInfo]
    var current = start
    var continue = true
    while (continue) tables.exprNode(current) match {
      case ForallE(_, _, body, info) => result += info; current = body
      case MData(child)              => current = child
      case _                         => continue = false
    }
    result.result()
  }

  private def mentionsBound(start: ExprId, initialDepth: Int): Boolean = {
    val pending = scala.collection.mutable.ArrayDeque((start, initialDepth))
    val seen = scala.collection.mutable.HashSet.empty[(ExprId, Int)]
    while (pending.nonEmpty) {
      val (id, depth) = pending.removeLast()
      if (seen.add((id, depth))) tables.exprNode(id) match {
        case BVar(index) if index == depth => return true
        case App(fn, arg)                  => pending.append((fn, depth)); pending.append((arg, depth))
        case Lam(_, tpe, body, _)          => pending.append((tpe, depth)); pending.append((body, depth + 1))
        case ForallE(_, tpe, body, _)      => pending.append((tpe, depth)); pending.append((body, depth + 1))
        case LetE(_, tpe, value, body, _) =>
          pending.append((tpe, depth)); pending.append((value, depth)); pending.append((body, depth + 1))
        case Proj(_, _, struct) => pending.append((struct, depth))
        case MData(child)       => pending.append((child, depth))
        case _                  =>
      }
    }
    false
  }

  private def coreType(term: ElabAst.Term): Term = term match {
    case ElabAst.Term.GlobalRef(name, at)           => Term.GlobalRef(name, at)
    case ElabAst.Term.LocalRef(ref, at)             => Term.LocalRef(ref, at)
    case ElabAst.Term.NatLit(value, at)             => Term.NatLit(value, at)
    case ElabAst.Term.StrLit(scalars, at)           => Term.StrLit(scalars, at)
    case ElabAst.Term.Proj(family, index, base, at) => Term.Proj(family, index, coreType(base), at)
    case ElabAst.Term.App(fn, args, at)             => Term.App(coreType(fn), args.map(coreType), at)
    case ElabAst.Term.Pi(binders, out, at, _) =>
      Term.Pi(binders.map(b => Binder(b.localRef, coreType(b.ty), b.span, b.isImplicit)), coreType(out), at)
    case ElabAst.Term.Body(lets, res, at) =>
      Term.Body(
        lets.map(l => CoreAst.Let(l.localRef, l.ty.map(coreType), coreType(l.value), l.span)),
        coreType(res),
        at
      )
    case other =>
      throw BodyLowering(atExpr(ExprId(0)), s"cannot use quoted term $other as a Core type", Some(declaration))
  }

  private def quoteFreshPi(value: VPi, context: Context): Term.Pi = {
    val quoted = ValueQuote.quotePi(value, ValueQuote.quoteContext(context.env), span())
    freshenPi(coreType(quoted).asInstanceOf[Term.Pi])
  }

  private def freshenPi(pi: Term.Pi): Term.Pi = {
    var replacements = Map.empty[LocalRef, Term]
    val binders = pi.binders.map { binder =>
      val fresh = LeanTermLowerer.freshLocal(binder.name)
      val next = binder.copy(localRef = fresh, ty = CoreSubstitution.substitute(binder.ty, replacements))
      replacements += binder.localRef -> Term.LocalRef(fresh, span())
      next
    }
    Term.Pi(binders, CoreSubstitution.substitute(pi.out, replacements), span())
  }

  private def stripMData(start: ExprId): ExprId = {
    var current = start
    var continue = true
    while (continue) tables.exprNode(current) match {
      case MData(child) => current = child
      case _            => continue = false
    }
    current
  }

  private def lowerPi(start: ExprId, initial: Context): Term.Pi = {
    val binders = Vector.newBuilder[Binder]
    var context = initial
    var current = stripMData(start)
    var continue = true
    while (continue) {
      tables.exprNode(current) match {
        case ForallE(name, binderType, body, info) =>
          val binder = Binder(
            LeanTermLowerer.freshLocal(displayName(name, "x")),
            lowerTerm(binderType, context),
            span(),
            requestedImplicit(info)
          )
          binders += binder
          context = bindFresh(context.copy(locals = binder.localRef +: context.locals), binder)
          current = stripMData(body)
        case _ => continue = false
      }
    }
    val requested = binders.result()
    val checked = BinderOps.checkImportedBinders(requested, initial.env)
    val finalBinders =
      requested.zip(checked.binders).map { case (core, result) => core.copy(isImplicit = result.isImplicit) }
    Term.Pi(finalBinders, lowerTerm(current, context), span())
  }

  private def lowerApplication(start: ExprId, context: Context): Term = {
    val termArgsReversed = Vector.newBuilder[ExprId]
    var headId = start
    var flatten = true
    while (flatten) tables.exprNode(headId) match {
      case App(fn, arg) => termArgsReversed += arg; headId = fn
      case MData(child) => headId = child
      case _            => flatten = false
    }
    val termArgs = termArgsReversed.result().reverse

    val (headCore, universeArgs) = tables.exprNode(headId) match {
      case Const(name, levels) =>
        val coreName = LeanExportNames.encode(name, tables)
        val global = registry.get(name, tables)
        val expectedUniverses = global match {
          case Some(value) if value.status == Installed => value.levelParameters.length
          case Some(_) =>
            throw UnsafeDependency(atExpr(headId), s"$coreName was skipped and cannot be referenced", Some(declaration))
          case None if BootstrapNames(coreName) => 0
          case None =>
            throw ForwardGlobal(atExpr(headId), s"global $coreName has not been installed", Some(declaration))
        }
        if (levels.length != expectedUniverses)
          throw ApplicationConventionMismatch(
            atExpr(headId),
            s"constant $coreName supplies ${levels.length} universe arguments; expected $expectedUniverses",
            Some(declaration)
          )
        (Term.GlobalRef(coreName, span()), levels.map(level => lowerLevel(level, context)))
      case _ => (lowerTerm(headId, context), Vector.empty[Term])
    }

    var coreHead = headCore
    var checkedHead = TypeChecker.checkTerm(coreHead, context.env)
    var remaining: Vector[Either[Term, ExprId]] = universeArgs.map(Left(_)) ++ termArgs.map(Right(_))

    while (remaining.nonEmpty || checkedHead.value.tpe.isInstanceOf[VPi]) {
      val pi = checkedHead.value.tpe match {
        case value: VPi => value
        case _ =>
          if (remaining.nonEmpty)
            throw ApplicationConventionMismatch(
              atExpr(start),
              s"application has ${remaining.length} extra source arguments",
              Some(declaration)
            )
          return coreHead
      }
      val consume = math.min(remaining.length, pi.binders.length)
      if (consume < pi.binders.length) {
        return etaExpand(coreHead, pi, quoteFreshPi(pi, context), remaining.take(consume), context, start)
      }

      val lowered = checkSourceArguments(pi, remaining.take(consume), context, start, requireAllProjections = true)
      val app = Term.App(coreHead, lowered.explicitCore, span())
      checkedHead = TypeChecker.checkTerm(app, context.env)
      coreHead = app
      remaining = remaining.drop(consume)
      if (remaining.isEmpty) return coreHead
    }
    coreHead
  }

  private[raccoonlang] def checkSourceArguments(
      pi: VPi,
      args: Vector[Either[Term, ExprId]],
      context: Context,
      expr: ExprId,
      requireAllProjections: Boolean
  ): CheckedSourceArgs = {
    var calleeEnv = pi.env
    val core = Vector.newBuilder[Term]
    val explicitCore = Vector.newBuilder[Term]
    var explicitValues = Vector.empty[Value]
    val suppliedValues = Array.ofDim[Value](args.length)

    args.indices.foreach { idx =>
      val binder = pi.binders(idx)
      val expected = Interpreter.evalTerm(binder.ty, calleeEnv)
      val term = args(idx).fold(identity, id => lowerExpected(id, expected, context))
      val checked = TypeChecker.checkTerm(term, expected, context.env)
      core += term; suppliedValues(idx) = checked.value
      calleeEnv = BinderOps.bindValueAndCheck(calleeEnv, binder, checked.value)
      if (!binder.isImplicit) { explicitCore += term; explicitValues :+= checked.value }
    }

    args.indices.foreach { idx =>
      val binder = pi.binders(idx)
      if (binder.isImplicit) {
        val spec = binder.projection.getOrElse(
          throw UnsaturatedCoreApplication(
            atExpr(expr),
            s"checked implicit binder ${binder.name} has no projection",
            Some(declaration)
          )
        )
        if (spec.rootArgIdx < explicitValues.length) {
          Projection.project(spec, explicitValues) match {
            case Right(projected) if ValueEquivalence.defEq(projected, suppliedValues(idx)) =>
            case Right(projected) =>
              throw SuppliedImplicitMismatch(
                atExpr(expr),
                s"supplied implicit ${binder.name} does not match its reconstructed value",
                Some(declaration)
              )
            case Left(reason) => throw ApplicationConventionMismatch(atExpr(expr), reason, Some(declaration))
          }
        } else if (requireAllProjections)
          throw ApplicationConventionMismatch(
            atExpr(expr),
            s"implicit ${binder.name} projects from missing explicit argument ${spec.rootArgIdx}",
            Some(declaration)
          )
      }
    }
    CheckedSourceArgs(core.result(), explicitCore.result())
  }

  private def etaExpand(
      head: Term,
      pi: VPi,
      sourcePi: Term.Pi,
      supplied: Vector[Either[Term, ExprId]],
      context: Context,
      expr: ExprId
  ): Term = {
    val checkedSupplied = checkSourceArguments(pi, supplied, context, expr, requireAllProjections = false)
    val suppliedMap = sourcePi.binders.take(supplied.length).map(_.localRef).zip(checkedSupplied.core).toMap
    val missingRequested = sourcePi.binders.drop(supplied.length).map { binder =>
      binder.copy(ty = CoreSubstitution.substitute(binder.ty, suppliedMap))
    }
    val classified = BinderOps.checkImportedBinders(missingRequested, context.env)
    val missing = missingRequested.zip(classified.binders).map { case (core, checked) =>
      core.copy(isImplicit = checked.isImplicit)
    }
    val allCore = checkedSupplied.core ++ missing.map(b => Term.LocalRef(b.localRef, span()))
    val resultType = CoreSubstitution.substitute(
      sourcePi.out,
      sourcePi.binders.map(_.localRef).zip(allCore).toMap
    )
    val wrapper = Term.Pi(missing, resultType, span())
    val explicitArgs = allCore.zip(pi.binders).collect { case (term, binder) if !binder.isImplicit => term }
    val body = Term.App(head, explicitArgs, span())
    val lambda = Term.Lam(wrapper, body, span(), name = None, recursion = None)
    TypeChecker.checkTerm(lambda, context.env)
    lambda
  }

  private def lowerLevel(id: LevelId, context: Context): Term = {
    val lowered = scala.collection.mutable.HashMap.empty[LevelId, Term]
    val pending = scala.collection.mutable.ArrayDeque((id, false))
    while (pending.nonEmpty) {
      val (current, expanded) = pending.removeLast()
      if (!lowered.contains(current)) {
        tables.levelNode(current) match {
          case LevelZero => lowered += current -> Term.GlobalRef("Level.zero", span())
          case LevelParam(name) =>
            val term = context.levels.get(name) match {
              case Some(ref) => Term.LocalRef(ref, span())
              case None =>
                throw UnknownLevelParameter(
                  tables.levelProvenance(current),
                  s"universe parameter ${tables.dottedName(name)} is not declared by $declaration",
                  Some(declaration)
                )
            }
            lowered += current -> term
          case LevelSucc(of) if expanded =>
            lowered += current -> builtinApp("Level.succ", Vector(lowered(of)))
          case LevelMax(left, right) if expanded =>
            lowered += current -> builtinApp("Level.max", Vector(lowered(left), lowered(right)))
          case LevelIMax(left, right) if expanded =>
            lowered += current -> builtinApp("Level.imax", Vector(lowered(left), lowered(right)))
          case LevelSucc(of) =>
            pending.append((current, true)); pending.append((of, false))
          case LevelMax(left, right) =>
            pending.append((current, true)); pending.append((right, false)); pending.append((left, false))
          case LevelIMax(left, right) =>
            pending.append((current, true)); pending.append((right, false)); pending.append((left, false))
        }
      }
    }
    lowered(id)
  }

  private def bindFresh(context: Context, binder: Binder): Context = {
    val tpe = TypeChecker.getType(binder.ty, context.env)
    val fresh = StructEta.freshStructWitness(tpe).getOrElse {
      val (_, value) = FreshVar.freshValue(binder.name, tpe)
      Value.canonicalizeRigidBinder(tpe, value)
    }
    context.copy(env = context.env.putLocal(binder.localRef, fresh))
  }

  private def builtinApp(name: String, args: Vector[Term]): Term =
    if (args.isEmpty) Term.GlobalRef(name, span()) else Term.App(Term.GlobalRef(name, span()), args, span())

  private def requireInstalled(name: NameId, expr: ExprId): String = {
    val coreName = LeanExportNames.encode(name, tables)
    registry.get(name, tables) match {
      case Some(value) if value.status == Installed => coreName
      case Some(_) =>
        throw UnsafeDependency(atExpr(expr), s"$coreName was skipped and cannot be referenced", Some(declaration))
      case None => throw ForwardGlobal(atExpr(expr), s"global $coreName has not been installed", Some(declaration))
    }
  }

  private def requestedImplicit(info: BinderInfo): Boolean = info != Default
  private def span(): Span = { val result = Span(nextSpan, nextSpan + 1, Some(sourceId)); nextSpan += 1; result }
  private def atExpr(id: ExprId): ExportProvenance = tables.exprProvenance(id)
  private def displayName(id: NameId, fallback: String): String = {
    val name = tables.dottedName(id)
    if (name.isEmpty) fallback else name.replace('.', '_')
  }
}
