package com.raccoonlang

import com.raccoonlang.SurfaceAst.{Command, Term => STerm}
import com.raccoonlang.{CoreAst => C}

/** Name resolution and surface-to-core translation for the deliberately unchecked evaluator. */
object Elaborator {
  private final case class Scope(locals: Map[String, C.LocalRef], next: Int) {
    def fresh(name: String): (Scope, C.LocalRef) = {
      val ref = C.LocalRef(next, name)
      (copy(locals = locals.updated(name, ref), next = next + 1), ref)
    }
    def restore(nested: Scope): Scope = copy(next = nested.next)
  }

  private def refTerm(name: String, span: Span, scope: Scope): C.Term =
    scope.locals.get(name).map(C.Term.LocalRef(_, span)).getOrElse(C.Term.GlobalRef(name, span))

  private def binders(bs: Vector[SurfaceAst.Binder], scope: Scope): (Scope, Vector[C.Binder]) =
    bs.foldLeft((scope, Vector.empty[C.Binder])) { case ((current, out), b) =>
      val (typed, ty) = elabTerm(b.ty, current)
      val (bound, ref) = typed.fresh(b.name)
      (bound, out :+ C.Binder(ref, ty, b.span, b.isImplicit))
    }

  private def elabTerm(term: STerm, scope: Scope): (Scope, C.Term) = term match {
    case STerm.Ident(name, span) => (scope, refTerm(name, span, scope))
    case STerm.NatLit(_, span)   => throw WTF(s"Natural literals are not available in the C04 core at $span")
    case STerm.StrLit(_, span)   => throw WTF(s"String literals are not available in the C04 core at $span")
    case STerm.Select(base, field, span) =>
      dottedName(base)
        .map(name => (scope, C.Term.GlobalRef(s"$name.$field", span)))
        .getOrElse(
          throw WTF(s"Projections are not available in the C04 core at $span")
        )
    case STerm.App(fn, args, span) =>
      val (afterFn, coreFn) = elabTerm(fn, scope)
      val (afterArgs, coreArgs) = args.foldLeft((scope.restore(afterFn), Vector.empty[C.Term])) {
        case ((current, out), arg) =>
          val (nested, core) = elabTerm(arg, current)
          (current.restore(nested), out :+ core)
      }
      (afterArgs, C.Term.App(coreFn, coreArgs, span))
    case STerm.Pi(bs, body, span) =>
      val (bound, coreBs) = binders(bs, scope)
      val (nested, coreBody) = elabTerm(body, bound)
      (scope.restore(nested), C.Term.Pi(coreBs, coreBody, span))
    case STerm.Lam(header, body, span) =>
      val (bound, coreBs) = binders(header.params, scope)
      val (typed, resultTy) = elabTerm(header.ty, bound)
      val (nested, coreBody) = elabTerm(body, bound.copy(next = typed.next))
      val pi = C.Term.Pi(coreBs, resultTy, header.span)
      (scope.restore(nested), C.Term.Lam(pi, coreBody, span, None, None))
    case STerm.Body(statements, result, span) =>
      val (afterLets, lets) = statements.foldLeft((scope, Vector.empty[C.Let])) {
        case ((current, out), STerm.LetStmt(let)) =>
          val (typed, ty) =
            let.ty.map(elabTerm(_, current)).map { case (s, t) => (s, Some(t)) }.getOrElse((current, None))
          val (valued, value) = elabTerm(let.value, current.restore(typed))
          val (bound, ref) = valued.fresh(let.name)
          (bound, out :+ C.Let(ref, ty, value, let.span))
        case (_, STerm.OpenStmt(open)) => throw WTF(s"Namespaces are not available in the C04 core at ${open.span}")
      }
      val (nested, coreResult) = elabTerm(result, afterLets)
      (scope.restore(nested), C.Term.Body(lets, coreResult, span))
    case STerm.Match(scrut, motive, cases, span) =>
      val (scrutScope, coreScrut) = elabTerm(scrut, scope)
      val (motiveScope, coreMotive) = motive
        .map(elabTerm(_, scope.restore(scrutScope)))
        .map { case (s, t) => (s, Some(t)) }
        .getOrElse((scrutScope, None))
      var nextScope = scope.restore(motiveScope)
      val coreCases = cases.map { c =>
        val branchStart = nextScope
        val (branchScope, refs) = c.argNames.foldLeft((branchStart, Vector.empty[Option[C.LocalRef]])) {
          case ((s, rs), "_")  => (s, rs :+ None)
          case ((s, rs), name) => val (n, ref) = s.fresh(name); (n, rs :+ Some(ref))
        }
        val (afterBody, body) = elabTerm(c.body, branchScope)
        nextScope = branchStart.copy(next = afterBody.next)
        C.Case(if (c.useShortName) c.ctorPath.last else c.ctorPath.mkString("."), !c.useShortName, refs, body, c.span)
      }
      (nextScope, C.Term.Match(coreScrut, coreMotive, coreCases, span))
  }

  private def dottedName(term: STerm): Option[String] = term match {
    case STerm.Ident(name, _)         => Some(name)
    case STerm.Select(base, field, _) => dottedName(base).map(name => s"$name.$field")
    case _                            => None
  }

  private def elabDecl(decl: Command.Decl.ConstDecl, scope: Scope): (Scope, C.Decl) = {
    val (paramScope, params) = binders(decl.header.funcHeader.params, scope)
    val (typed, resultTy) = elabTerm(decl.header.funcHeader.ty, paramScope)
    val bodyScope = paramScope.copy(next = typed.next)
    val fullType = if (params.nonEmpty) C.Term.Pi(params, resultTy, decl.header.funcHeader.span) else resultTy
    val (measureScope, decreaseSpec): (Scope, Option[C.DecreaseSpec]) = decl.decreases match {
      case None => (bodyScope, None)
      case Some(SurfaceAst.DecreaseSpec.Structural(arg, sp)) =>
        (bodyScope, Some(C.DecreaseSpec.Lexicographic(Vector(paramRef(arg, params)), sp)))
      case Some(SurfaceAst.DecreaseSpec.Lexicographic(args, sp)) =>
        (bodyScope, Some(C.DecreaseSpec.Lexicographic(args.map(paramRef(_, params)), sp)))
      case Some(SurfaceAst.DecreaseSpec.Measure(measure, sp)) =>
        val (afterMeasure, coreMeasure) = elabTerm(measure, bodyScope)
        (afterMeasure, Some(C.DecreaseSpec.Measure(coreMeasure, sp)))
    }
    val (bodyScopeForElab, selfRef): (Scope, Option[C.LocalRef]) = decreaseSpec match {
      case Some(_) => val (next, ref) = measureScope.fresh(decl.header.name); (next, Some(ref))
      case None    => (measureScope, None)
    }
    val (afterBody, bodyTerm) = decl.body match {
      case SurfaceAst.ConstBody.TermBody(t) => elabTerm(t, bodyScopeForElab)
      case SurfaceAst.ConstBody.Builtin(s)  => throw WTF(s"Builtin bodies are not available in the C04 core at $s")
    }
    val body =
      if (params.nonEmpty) {
        val recursion = decreaseSpec.map { decreases =>
          C.Recursion(selfRef.getOrElse(throw WTF(s"Missing recursive self ref at $decl.span")), decreases)
        }
        C.Term.Lam(fullType.asInstanceOf[C.Term.Pi], bodyTerm, decl.span, Some(decl.header.name), recursion)
      } else {
        if (decl.decreases.nonEmpty) throw WTF(s"Recursive definitions require parameters at ${decl.span}")
        bodyTerm
      }
    (
      scope.restore(afterBody),
      C.Decl.ConstDecl(decl.isOpaque, decl.header.name, fullType, C.ConstBody.TermBody(body), decl.span)
    )
  }

  private def paramRef(name: String, params: Vector[C.Binder]): C.LocalRef =
    params.find(_.name == name).map(_.localRef).getOrElse(throw WTF(s"Unknown recursive parameter $name"))

  private def elabAxiom(decl: Command.Decl.AxiomDecl, scope: Scope): (Scope, C.Decl) = {
    val (typed, params) = binders(decl.header.funcHeader.params, scope)
    val (afterType, resultTy) = elabTerm(decl.header.funcHeader.ty, typed)
    val fullType = if (params.nonEmpty) C.Term.Pi(params, resultTy, decl.header.funcHeader.span) else resultTy
    (scope.restore(afterType), C.Decl.AxiomDecl(decl.header.name, fullType, decl.span))
  }

  private def elabInductive(decl: Command.Decl.InductiveDecl, scope: Scope): (Scope, C.Decl) = {
    val (paramScope, params) = binders(decl.header.params, scope)
    val (indexScope, indices) = binders(decl.header.indices, paramScope)
    val (typedHeader, resultTy) = elabTerm(decl.header.resultTy, indexScope)
    val header = C.InductiveHeader(decl.header.name, params, indices, resultTy, decl.header.span)
    var next = scope.restore(typedHeader)
    var ctorNext = paramScope.copy(next = typedHeader.next)
    val ctors = decl.ctors.map { c =>
      val (ctorScope, binders) = Elaborator.binders(c.binders, ctorNext)
      val (afterResult, result) = elabTerm(c.resultTy, ctorScope)
      ctorNext = paramScope.copy(next = afterResult.next)
      next = next.copy(next = afterResult.next)
      C.ConstructorDecl(s"${decl.header.name}.${c.name}", c.name, binders, result, c.span)
    }
    (next, C.Decl.InductiveDecl(header, ctors, decl.span))
  }

  private def elabCommands(commands: Vector[Command], scope: Scope): (Scope, Vector[C.Decl]) =
    commands.foldLeft((scope, Vector.empty[C.Decl])) {
      case ((s, out), d: Command.Decl.ConstDecl) =>
        val (n, c) = elabDecl(d, s)
        (n, out :+ c)
      case ((s, out), d: Command.Decl.AxiomDecl) =>
        val (n, c) = elabAxiom(d, s)
        (n, out :+ c)
      case ((s, out), d: Command.Decl.InductiveDecl) =>
        val (n, c) = elabInductive(d, s)
        (n, out :+ c)
      case ((s, out), Command.Block(body, _)) =>
        val (n, nested) = elabCommands(body, s)
        (n, out ++ nested)
      case (_, other) => throw WTF(s"Unsupported declaration in the C04 core: $other")
    }

  def elab(program: SurfaceAst.Program): C.Program = {
    val (scope, decls) = elabCommands(program.decls, Scope(Map.empty, 0))
    val body = program.body.map(t => elabTerm(t, scope)._2)
    C.Program(decls, body)
  }
}
