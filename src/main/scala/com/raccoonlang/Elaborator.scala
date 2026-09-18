package com.raccoonlang

import com.raccoonlang.SurfaceAst.{Command, Term => STerm}
import com.raccoonlang.{CoreAst => C}

/** Name resolution and surface-to-core translation for the deliberately unchecked evaluator. */
object Elaborator {
  private final case class Scope(locals: Map[String, C.LocalRef], next: Int, globals: Set[String] = Set.empty) {
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
      dottedName(base, scope)
        .filter(name => scope.globals.contains(s"$name.$field"))
        .map(name => (scope, C.Term.GlobalRef(s"$name.$field", span)))
        .getOrElse {
          val (nested, coreBase) = elabTerm(base, scope)
          (nested, C.Term.Select(coreBase, field, span))
        }
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

  private def dottedName(term: STerm, scope: Scope): Option[String] = term match {
    case STerm.Ident(name, _) if !scope.locals.contains(name) => Some(name)
    case STerm.Select(base, field, _)                         => dottedName(base, scope).map(name => s"$name.$field")
    case _                                                    => None
  }

  private def elabDecl(decl: Command.Decl.ConstDecl, scope: Scope): (Scope, C.Decl) = {
    val (paramScope, params) = binders(decl.header.funcHeader.params, scope)
    val (typed, resultTy) = elabTerm(decl.header.funcHeader.ty, paramScope)
    val bodyScope = paramScope.copy(next = typed.next)
    val fullType = if (params.nonEmpty) C.Term.Pi(params, resultTy, decl.header.funcHeader.span) else resultTy
    val (measureScope, decreaseSpec): (Scope, Option[C.DecreaseSpec]) = decl.decreases match {
      case None => (bodyScope, None)
      case Some(SurfaceAst.DecreaseSpec.Structural(arg, sp)) =>
        (bodyScope, Some(C.DecreaseSpec.Lexicographic(Vector(paramRef(arg, params, sp)), sp)))
      case Some(SurfaceAst.DecreaseSpec.Lexicographic(args, sp)) =>
        (bodyScope, Some(C.DecreaseSpec.Lexicographic(args.map(paramRef(_, params, sp)), sp)))
      case Some(SurfaceAst.DecreaseSpec.Measure(measure, sp)) =>
        val (afterMeasure, coreMeasure) = elabTerm(measure, bodyScope)
        (afterMeasure, Some(C.DecreaseSpec.Measure(coreMeasure, sp)))
    }
    val (bodyScopeForElab, selfRef): (Scope, Option[C.LocalRef]) = decreaseSpec match {
      case Some(_) => val (next, ref) = measureScope.fresh(decl.header.name); (next, Some(ref))
      case None    => (measureScope, None)
    }
    val (afterBody, coreBody) = decl.body match {
      case SurfaceAst.ConstBody.Builtin(s) => (bodyScope, C.ConstBody.Builtin(s): C.ConstBody)
      case SurfaceAst.ConstBody.TermBody(t) =>
        val (after, bodyTerm) = elabTerm(t, bodyScopeForElab)
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
        (after, C.ConstBody.TermBody(body): C.ConstBody)
    }
    (
      scope.restore(afterBody),
      C.Decl.ConstDecl(decl.isOpaque, decl.header.name, fullType, coreBody, decl.span)
    )
  }

  private def paramRef(name: String, params: Vector[C.Binder], span: Span): C.LocalRef =
    params.find(_.name == name).map(_.localRef).getOrElse {
      throw InvalidDecreaseSpec(s"$name is not a function parameter", Some(span))
    }

  private def elabAxiom(decl: Command.Decl.AxiomDecl, scope: Scope): (Scope, C.Decl) = {
    val (typed, params) = binders(decl.header.funcHeader.params, scope)
    val (afterType, resultTy) = elabTerm(decl.header.funcHeader.ty, typed)
    val fullType = if (params.nonEmpty) C.Term.Pi(params, resultTy, decl.header.funcHeader.span) else resultTy
    (scope.restore(afterType), C.Decl.AxiomDecl(decl.header.name, fullType, decl.span))
  }

  private def elabInductive(decl: Command.Decl.InductiveDecl, scope: Scope): (Scope, Vector[C.Decl]) = {
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
    val inductive = C.Decl.InductiveDecl(header, ctors, decl.span)
    val (withFreshSelf, selfRef) = next.fresh("__self")
    val generated =
      if (decl.generateSelectors) ctors match {
        case Vector(ctor) => generatedSelectors(header, ctor, selfRef)
        case _            => Vector.empty
      }
      else Vector.empty
    (next.copy(next = withFreshSelf.next), inductive +: generated)
  }

  /**
   * Build ordinary definitions for structure fields. Their bodies are matches on the self argument; projection
   * checking/evaluation therefore uses exactly the same checked definition path as user code.
   */
  private def generatedSelectors(
      header: C.InductiveHeader,
      ctor: C.ConstructorDecl,
      selfRef: C.LocalRef
  ): Vector[C.Decl] = {
    val selfTy =
      if (header.binders.isEmpty) C.Term.GlobalRef(header.name, header.span)
      else
        C.Term.App(
          C.Term.GlobalRef(header.name, header.span),
          header.binders.collect { case b if !b.isImplicit => C.Term.LocalRef(b.localRef, b.span) },
          header.span
        )
    val selectors = ctor.binders.zipWithIndex.collect { case (field, idx) if field.name != "_" => (field, idx) }
    val selectorNames = selectors.map { case (field, _) => field.localRef -> s"${header.name}.${field.name}" }.toMap

    def rewrite(term: C.Term, self: C.LocalRef, previous: Map[C.LocalRef, String]): C.Term = term match {
      case C.Term.LocalRef(ref, span) if previous.contains(ref) =>
        val call = C.Term.GlobalRef(previous(ref), span)
        val args = Vector(C.Term.LocalRef(self, span))
        C.Term.App(call, args, span)
      case C.Term.App(fn, args, span) =>
        C.Term.App(rewrite(fn, self, previous), args.map(rewrite(_, self, previous)), span)
      case C.Term.Select(base, field, span) => C.Term.Select(rewrite(base, self, previous), field, span)
      case C.Term.Pi(bs, out, span, prop) =>
        C.Term.Pi(bs.map(b => b.copy(ty = rewrite(b.ty, self, previous))), rewrite(out, self, previous), span, prop)
      case C.Term.Lam(pi, body, span, name, rec, peers) =>
        C.Term.Lam(
          rewrite(pi, self, previous).asInstanceOf[C.Term.Pi],
          rewrite(body, self, previous),
          span,
          name,
          rec,
          peers
        )
      case C.Term.Body(lets, res, span) =>
        C.Term.Body(
          lets.map(l => l.copy(ty = l.ty.map(rewrite(_, self, previous)), value = rewrite(l.value, self, previous))),
          rewrite(res, self, previous),
          span
        )
      case C.Term.Match(scrut, motive, cases, span) =>
        C.Term.Match(
          rewrite(scrut, self, previous),
          motive.map(rewrite(_, self, previous)),
          cases.map(c => c.copy(body = rewrite(c.body, self, previous))),
          span
        )
      case other => other
    }

    selectors.map { case (field, _) =>
      val previous = selectorNames.filter { case (ref, _) =>
        ctor.binders.indexWhere(_.localRef == ref) < ctor.binders.indexWhere(_.localRef == field.localRef)
      }
      val fieldTy = rewrite(field.ty, selfRef, previous)
      val selfBinder = C.Binder(selfRef, selfTy, field.span)
      // Selector parameters include indices as well as family parameters.  All are reconstructed
      // from the structure value at a selector call; keep the exact telescope grouping here.
      val allBinders = header.binders.map(_.copy(isImplicit = true)) ++ Vector(selfBinder)
      val resultTy = fieldTy
      val pi = C.Term.Pi(allBinders, resultTy, field.span)
      val argRefs = ctor.binders.map(b => Some(b.localRef))
      val body = C.Term.Match(
        C.Term.LocalRef(selfRef, field.span),
        // A neutral structure's type is the family application, not the selected field type. Without
        // this motive the residual match cannot retain a function-valued field's Pi type.
        Some(fieldTy),
        Vector(
          C.Case(
            ctor.canonicalName,
            isFullyQualified = true,
            argRefs,
            C.Term.LocalRef(field.localRef, field.span),
            field.span
          )
        ),
        field.span
      )
      C.Decl.ConstDecl(
        isOpaque = false,
        name = s"${header.name}.${field.name}",
        ty = pi,
        body = C.ConstBody.TermBody(C.Term.Lam(pi, body, field.span, Some(s"${header.name}.${field.name}"), None)),
        span = field.span
      )
    }
  }

  private def elabCommands(commands: Vector[Command], scope: Scope): (Scope, Vector[C.Decl]) =
    commands.foldLeft((scope, Vector.empty[C.Decl])) {
      case ((s, out), d: Command.Decl.ConstDecl) =>
        val (n, c) = elabDecl(d, s)
        (n.copy(globals = n.globals + d.header.name), out :+ c)
      case ((s, out), d: Command.Decl.AxiomDecl) =>
        val (n, c) = elabAxiom(d, s)
        (n.copy(globals = n.globals + d.header.name), out :+ c)
      case ((s, out), d: Command.Decl.InductiveDecl) =>
        val (n, cs) = elabInductive(d, s)
        (
          n.copy(
            globals = n.globals ++
              cs.collect { case C.Decl.ConstDecl(_, name, _, _, _) => name } ++
              Vector(d.header.name) ++
              d.ctors.map(c => s"${d.header.name}.${c.name}")
          ),
          out ++ cs
        )
      case ((s, out), Command.Block(body, _)) =>
        val (n, nested) = elabCommands(body, s)
        (n, out ++ nested)
      case (_, other) => throw WTF(s"Unsupported declaration in the C04 core: $other")
    }

  def elab(program: SurfaceAst.Program): C.Program = {
    val builtins = Set(
      "Type",
      "Prop",
      "Level",
      "Level.zero",
      "Level.one",
      "Level.succ",
      "Level.max",
      "Level.imax",
      "Sort",
      "Quot.mk",
      "Quot.lift",
      "Quot.ind"
    )
    val (scope, decls) = elabCommands(program.decls, Scope(Map.empty, 0, builtins))
    val body = program.body.map(t => elabTerm(t, scope)._2)
    C.Program(decls, body)
  }
}
