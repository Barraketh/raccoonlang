package com.raccoonlang

import com.raccoonlang.CoreAst.{Binder, LocalRef}
import com.raccoonlang.CoreAst.Term
import com.raccoonlang.LeanExportIr._

private[raccoonlang] object LeanTermLowerer {
  final case class LoweredDeclarationType(
      term: Term,
      pi: Option[Term.Pi],
      universeBinders: Int,
      sourceBinders: Int,
      levelRefs: Map[NameId, LocalRef]
  )
  final case class Context(locals: Vector[LocalRef], levels: Map[NameId, LocalRef])
}

private[raccoonlang] final class LeanTermLowerer(
    tables: ExportTables,
    kernelEnv: Env,
    registry: LeanGlobalRegistry,
    declaration: String
) {
  import LeanTermLowerer.{Context, LoweredDeclarationType}

  private val sourceId = SourceId.fresh()
  private var nextLocal = 0
  private var nextSpan = 0

  private val BootstrapNames = Set("Sort", "Level.succ", "Level.max", "Level.imax", "Type", "Level", "Level.zero", "Level.one", "Prop")

  def lowerDeclarationType(levelParams: Vector[NameId], expr: ExprId): LoweredDeclarationType = {
    if (levelParams.distinct.length != levelParams.length)
      throw UnknownLevelParameter(atExpr(expr), s"declaration $declaration has duplicate universe parameters", Some(declaration))

    val levelBinders = levelParams.map { id =>
      val ref = freshLocal(displayName(id, "u"))
      id -> Binder(ref, Term.GlobalRef("Level", span()), span(), isImplicit = true)
    }
    var context = Context(Vector.empty, levelBinders.iterator.map { case (id, binder) => id -> binder.localRef }.toMap)
    val binders = Vector.newBuilder[Binder]
    levelBinders.foreach(pair => binders += pair._2)

    var current = expr
    var sourceCount = 0
    var continue = true
    while (continue) {
      tables.exprNode(current) match {
        case ForallE(name, binderType, body, info) =>
          val ref = freshLocal(displayName(name, "x"))
          binders += Binder(ref, lowerTerm(binderType, context), span(), requestedImplicit(info))
          context = context.copy(locals = ref +: context.locals)
          sourceCount += 1
          current = body
        case _ => continue = false
      }
    }
    val out = lowerTerm(current, context)
    val allBinders = binders.result()
    val term = if (allBinders.nonEmpty) Term.Pi(allBinders, out, span()) else out
    LoweredDeclarationType(term, term match { case pi: Term.Pi => Some(pi); case _ => None },
      levelBinders.length, sourceCount, context.levels)
  }

  def lowerDeclarationBody(expr: ExprId, declared: LoweredDeclarationType, name: String): Term = {
    declared.pi match {
      case Some(pi) =>
        var current = expr
        var consumed = 0
        var context = Context(Vector.empty, declared.levelRefs)
        val sourceRefs = pi.binders.drop(declared.universeBinders).map(_.localRef)
        val checkedBinderEnv = com.raccoonlang.telescope.BinderOps.checkBinders(pi.binders, kernelEnv).env
        while (consumed < sourceRefs.length) {
          tables.exprNode(current) match {
            case Lam(_, binderType, body, info) =>
              val expectedBinder = pi.binders(declared.universeBinders + consumed)
              if (requestedImplicit(info) != expectedBinder.isImplicit)
                throw InvalidBinderMetadata(atExpr(current),
                  s"lambda binder $consumed implicitness disagrees with its declared Pi binder", Some(declaration))
              val annotation = lowerTerm(binderType, context)
              val annotationValue = TypeChecker.getType(annotation, checkedBinderEnv)
              val expectedValue = Interpreter.evalTerm(
                TypeChecker.checkTerm(expectedBinder.ty, checkedBinderEnv).residual,
                checkedBinderEnv
              )
              if (!ValueEquivalence.defEq(annotationValue, expectedValue))
                throw InvalidBinderMetadata(atExpr(current),
                  s"lambda binder $consumed type disagrees with its declared Pi binder", Some(declaration))
              context = context.copy(locals = sourceRefs(consumed) +: context.locals)
              current = body
              consumed += 1
            case _ =>
              throw BodyLowering(atExpr(current),
                s"function body for $declaration has $consumed lambdas; expected ${sourceRefs.length}", Some(declaration))
          }
        }
        tables.exprNode(current) match {
          case _: Lam => throw BodyLowering(atExpr(current), s"function body for $declaration has extra lambdas", Some(declaration))
          case _ =>
        }
        val body = lowerTerm(current, context)
        Term.Lam(pi, body, span(), Some(name), recursion = None)
      case None => lowerTerm(expr, Context(Vector.empty, declared.levelRefs))
    }
  }

  def lowerTerm(expr: ExprId): Term = lowerTerm(expr, Context(Vector.empty, Map.empty))

  private def lowerTerm(expr: ExprId, context: Context): Term = tables.exprNode(expr) match {
    case BVar(index) =>
      if (index >= context.locals.length)
        throw BadBVar(atExpr(expr), s"bound-variable index $index is outside ${context.locals.length} local binders",
          Some(declaration))
      Term.LocalRef(context.locals(index), span())
    case Sort(level) => builtinApp("Sort", Vector(lowerLevel(level, context)))
    case Const(name, levels) =>
      val coreName = LeanExportNames.encode(name, tables)
      val expectedUniverses =
        if (BootstrapNames(coreName)) 0
        else registry.get(name, tables) match {
          case Some(global) if global.status == Installed => global.levelParameters.length
          case Some(_) => throw UnknownGlobal(atExpr(expr), s"$coreName was skipped and cannot be referenced", Some(declaration))
          case None => throw UnknownGlobal(atExpr(expr), s"global $coreName has not been installed", Some(declaration))
        }
      if (levels.length != expectedUniverses)
        throw TypeLowering(atExpr(expr),
          s"constant $coreName supplies ${levels.length} universe arguments; expected $expectedUniverses", Some(declaration))
      if (levels.nonEmpty)
        throw UnsupportedFeature(atExpr(expr), s"polymorphic constant application for $coreName requires T1.3", Some(declaration))
      Term.GlobalRef(coreName, span())
    case ForallE(_, _, _, _) => lowerPi(expr, context)
    case Lam(_, _, _, _) =>
      throw UnsupportedFeature(atExpr(expr), "a lambda outside a declaration's expected Pi requires T1.3", Some(declaration))
    case App(_, _) => throw UnsupportedFeature(atExpr(expr), "application lowering requires T1.3", Some(declaration))
    case LetE(_, _, _, _, _) | Proj(_, _, _) | NatVal(_) | StrVal(_) | MData(_) =>
      throw UnsupportedFeature(atExpr(expr), "expression form requires T1.4", Some(declaration))
  }

  private def lowerPi(start: ExprId, initial: Context): Term.Pi = {
    val binders = Vector.newBuilder[Binder]
    var context = initial
    var current = start
    var continue = true
    while (continue) {
      tables.exprNode(current) match {
        case ForallE(name, binderType, body, info) =>
          val ref = freshLocal(displayName(name, "x"))
          binders += Binder(ref, lowerTerm(binderType, context), span(), requestedImplicit(info))
          context = context.copy(locals = ref +: context.locals)
          current = body
        case _ => continue = false
      }
    }
    Term.Pi(binders.result(), lowerTerm(current, context), span())
  }

  private def lowerLevel(id: LevelId, context: Context): Term = tables.levelNode(id) match {
    case LevelZero => Term.GlobalRef("Level.zero", span())
    case LevelSucc(of) => builtinApp("Level.succ", Vector(lowerLevel(of, context)))
    case LevelMax(left, right) => builtinApp("Level.max", Vector(lowerLevel(left, context), lowerLevel(right, context)))
    case LevelIMax(left, right) => builtinApp("Level.imax", Vector(lowerLevel(left, context), lowerLevel(right, context)))
    case LevelParam(name) => context.levels.get(name) match {
      case Some(ref) => Term.LocalRef(ref, span())
      case None => throw UnknownLevelParameter(tables.levelProvenance(id),
        s"universe parameter ${tables.dottedName(name)} is not declared by $declaration", Some(declaration))
    }
  }

  private def builtinApp(name: String, args: Vector[Term]): Term =
    if (args.isEmpty) Term.GlobalRef(name, span()) else Term.App(Term.GlobalRef(name, span()), args, span())

  private def requestedImplicit(info: BinderInfo): Boolean = info != Default
  private def freshLocal(name: String): LocalRef = { val ref = LocalRef(nextLocal, name); nextLocal += 1; ref }
  private def span(): Span = { val result = Span(nextSpan, nextSpan + 1, Some(sourceId)); nextSpan += 1; result }
  private def atExpr(id: ExprId): ExportProvenance = tables.exprProvenance(id)
  private def displayName(id: NameId, fallback: String): String = {
    val name = tables.dottedName(id)
    if (name.isEmpty) fallback else name.replace('.', '_')
  }
}
