package com.raccoonlang

import com.raccoonlang.CoreAst.UnfoldStrategy

object Elaborator {
  val SA = SurfaceAst
  val CA = CoreAst

  private val BuiltinGlobals: Set[String] =
    Set(
      "Type",
      "Normalizer",
      "Level",
      "Level::zero",
      "Level::one",
      "Prop",
      "Sort",
      "add_normalizer",
      "Level::succ",
      "Level::max"
    )

  private final case class ResolveEnv(
      scopes: List[Map[String, CA.LocalRef]],
      nextLocal: Int,
      globals: Set[String]
  ) {
    def enterScope: ResolveEnv = copy(scopes = Map.empty[String, CA.LocalRef] :: scopes)

    def resolve(name: String): Option[CA.LocalRef] = scopes.collectFirst(Function.unlift(_.get(name)))

    def resolveIdent(i: SA.Term.Ident): CA.Term.Ref =
      resolve(i.name) match {
        case Some(ref) => CA.Term.LocalRef(ref, i.span)
        case None      => CA.Term.GlobalRef(i.name, i.span)
      }

    def addGlobal(name: String): ResolveEnv =
      if (globals.contains(name)) throw AlreadyDefined(name)
      else copy(globals = globals + name)

    private def allocate(name: String): (CA.LocalRef, ResolveEnv) = {
      val ref = CA.LocalRef(nextLocal, name)
      (ref, copy(nextLocal = nextLocal + 1))
    }

    def bind(name: String, allowShadow: Boolean = false): (Option[CA.LocalRef], ResolveEnv) =
      if (name == "_") (None, this)
      else if (!allowShadow && scopes.head.contains(name)) throw AlreadyDefined(name)
      else {
        val (ref, nextEnv) = allocate(name)
        (Some(ref), nextEnv.copy(scopes = (scopes.head + (name -> ref)) :: scopes.tail))
      }

    def bindBinder(name: String, allowShadow: Boolean = false): (CA.LocalRef, ResolveEnv) =
      if (name == "_") allocate(name)
      else if (!allowShadow && scopes.head.contains(name)) throw AlreadyDefined(name)
      else {
        val (ref, nextEnv) = allocate(name)
        (ref, nextEnv.copy(scopes = (scopes.head + (name -> ref)) :: scopes.tail))
      }

    def bindRequired(name: String, span: Span, allowShadow: Boolean = false): (CA.LocalRef, ResolveEnv) =
      bind(name, allowShadow) match {
        case (Some(ref), nextEnv) => (ref, nextEnv)
        case (None, _)            => throw WTF("Anonymous binding is not supported here", Some(span))
      }
  }

  private object ResolveEnv {
    def empty: ResolveEnv = ResolveEnv(List(Map.empty), 0, BuiltinGlobals)
  }

  private def elabPi(pi: SA.Term.Pi, env: ResolveEnv): CA.Term.Pi = {
    val piEnv = env.enterScope
    val (binder, binderEnv) = elabBinder(pi.binder, piEnv)
    val body = elabType(pi.body, binderEnv)
    val span = Span(binder.span.start, body.span.end)
    body match {
      case pi: CA.Term.Pi => CA.Term.Pi(binder +: pi.binders, pi.out, span)
      case other          => CA.Term.Pi(Vector(binder), other, span)
    }
  }

  private def elabType(ty: SA.TypeTerm, env: ResolveEnv): CA.TypeTerm = ty match {
    case i: SA.Term.Ident                 => env.resolveIdent(i)
    case SA.Term.TApp(fn, args, sp)       => CA.Term.TApp(env.resolveIdent(fn), args.map(elabType(_, env)), sp)
    case pi: SA.Term.Pi                   => elabPi(pi, env)
    case SA.Term.TSelect(base, field, sp) => CA.Term.TSelect(elabType(base, env), field, sp)
    case SA.Term.Capture(name, sp)        => throw new RuntimeException(s"$$ cannot be used here: $name")
  }

  private def elabPattern(ty: SA.TypeTerm, env: ResolveEnv): (CA.TypePattern, ResolveEnv) = ty match {
    case i: SA.Term.Ident => (CA.TypePattern.Type(env.resolveIdent(i)), env)
    case SA.Term.TSelect(base, field, sp) =>
      val (basePattern, nextEnv) = elabPattern(base, env)
      basePattern match {
        case CA.TypePattern.Type(baseType) => (CA.TypePattern.Type(CA.Term.TSelect(baseType, field, sp)), nextEnv)
        case other                         => throw WTF(s"Expected type term in selection pattern, got $other")
      }
    case SA.Term.TApp(fn, args, sp) =>
      val (nextArgs, nextEnv) = args.foldLeft((Vector.empty[CA.TypePattern], env)) { case ((curArgs, curEnv), arg) =>
        val (nextArg, argEnv) = elabPattern(arg, curEnv)
        (curArgs :+ nextArg, argEnv)
      }
      (CA.TypePattern.App(env.resolveIdent(fn), nextArgs, sp), nextEnv)
    case pi: SA.Term.Pi =>
      (CA.TypePattern.Type(elabPi(pi, env)), env)
    case SA.Term.Capture(name, sp) =>
      val (ref, nextEnv) = env.bindRequired(name, sp)
      (CA.TypePattern.Capture(ref, sp), nextEnv)
  }

  private def elabBinder(b: SA.Binder, env: ResolveEnv): (CA.Binder, ResolveEnv) = {
    val (ty, envWithCaptures) = elabPattern(b.ty, env)
    val (ref, nextEnv) = envWithCaptures.bindBinder(b.name)
    (CA.Binder(ref, ty, b.span, b.isInstance), nextEnv)
  }

  private def elabBinders(binders: Vector[SA.Binder], env: ResolveEnv): (Vector[CA.Binder], ResolveEnv) =
    binders.foldLeft((Vector.empty[CA.Binder], env)) { case ((curBinders, curEnv), binder) =>
      val (nextBinder, nextEnv) = elabBinder(binder, curEnv)
      (curBinders :+ nextBinder, nextEnv)
    }

  private final case class HeaderResult(ty: CA.TypeTerm, bodyEnv: ResolveEnv)

  private def elabHeader(header: SA.FuncHeader, env: ResolveEnv): HeaderResult = {
    val headerEnv = env.enterScope
    val (params, bodyEnv) = elabBinders(header.params, headerEnv)
    val outTy = elabType(header.ty, bodyEnv)
    val ty =
      if (params.isEmpty) outTy
      else CA.Term.Pi(params, outTy, header.span)
    HeaderResult(ty, bodyEnv)
  }

  def getType(header: SA.FuncHeader): CA.TypeTerm = elabHeader(header, ResolveEnv.empty).ty

  private def elab(use: SA.Use, env: ResolveEnv): CA.Use = CA.Use(elabTerm(use.normalizer, env), use.span)

  private def elabBody(body: SA.Term.Body, env: ResolveEnv): CA.Term.Body = {
    if (body.uses.nonEmpty) throw new RuntimeException("Use statements only allowed at top of fn declaration")

    val (lets, bodyEnv) = body.lets.foldLeft((Vector.empty[CA.Let], env)) { case ((curLets, curEnv), l) =>
      val ty = l.ty.map(elabType(_, curEnv))
      val value = elabTerm(l.value, curEnv)
      val (ref, nextEnv) = curEnv.bindRequired(l.name, l.span, allowShadow = true)
      (curLets :+ CA.Let(ref, ty, value, l.span, l.isInstance), nextEnv)
    }
    CA.Term.Body(lets, elabTerm(body.out, bodyEnv), body.span)
  }

  private def elabLam(
      pi: CA.Term.Pi,
      bodyEnv: ResolveEnv,
      body: SA.Term,
      name: Option[String],
      isStable: Boolean,
      span: Span,
      outerEnv: ResolveEnv
  ): CA.Term.Lam = {
    val (uses, newBody) = body match {
      case b: SA.Term.Body => (b.uses, b.copy(uses = Vector.empty))
      case _               => (Vector.empty, body)
    }
    CA.Term.Lam(pi, uses.map(elab(_, outerEnv)), elabTerm(newBody, bodyEnv), span, name, isStable)
  }

  private def elab(l: SA.Term.Lam, env: ResolveEnv): CA.Term.Lam = {
    val header = elabHeader(l.header, env)
    header.ty match {
      case pi: CA.Term.Pi =>
        elabLam(pi, header.bodyEnv, l.body, None, isStable = false, l.span, env)
      case _ => throw new RuntimeException("WTF")
    }
  }

  private def elabTerm(term: SurfaceAst.Term, env: ResolveEnv): CA.Term = term match {
    case i: SA.Term.Ident                => env.resolveIdent(i)
    case SA.Term.App(fn, args, sp)       => CA.Term.App(elabTerm(fn, env), args.map(elabTerm(_, env)), sp)
    case SA.Term.Select(base, field, sp) => CA.Term.Select(elabTerm(base, env), field, sp)
    case SA.Term.Derive(goal, sp)        => CA.Term.Derive(elabType(goal, env), sp)
    case pi: SA.Term.Pi                  => elabPi(pi, env)
    case l: SA.Term.Lam                  => elab(l, env)
    case b: SA.Term.Body                 => elabBody(b, env)
    case SA.Term.Match(scrut, motive, cases, sp) =>
      CA.Term.Match(
        elabTerm(scrut, env),
        motive.map(elabType(_, env)),
        cases.map(elabCase(_, env)),
        sp
      )
  }

  private def elabCase(c: SA.Case, env: ResolveEnv): CA.Case = {
    val caseEnv = env.enterScope
    val (argRefs, bodyEnv) = c.argNames.foldLeft((Vector.empty[Option[CA.LocalRef]], caseEnv)) {
      case ((curRefs, curEnv), argName) =>
        val (ref, nextEnv) = curEnv.bind(argName)
        (curRefs :+ ref, nextEnv)
    }
    CA.Case(c.ctorName, argRefs, elabTerm(c.body, bodyEnv), c.span)
  }

  private def elabConstDecl(c: SurfaceAst.Decl.ConstDecl, env: ResolveEnv): (CoreAst.Decl, ResolveEnv) = {
    val header = elabHeader(c.header.funcHeader, env)
    val body = header.ty match {
      case pi: CA.Term.Pi =>
        elabLam(
          pi,
          header.bodyEnv,
          c.body,
          Some(c.header.name),
          c.unfoldStrategy.contains(UnfoldStrategy.Stable),
          c.span,
          env
        )
      case _ => elabTerm(c.body, env)
    }
    (
      CA.Decl.ConstDecl(c.unfoldStrategy, c.header.name, header.ty, body, c.span, c.isInstance),
      env.addGlobal(c.header.name)
    )
  }

  private def elabInductiveDecl(c: SurfaceAst.Decl.InductiveDecl, env: ResolveEnv): (CoreAst.Decl, ResolveEnv) = {
    val headerEnv = env.enterScope
    val (params, envWithParams) = elabBinders(c.header.params, headerEnv)
    val (indices, envWithIndices) = elabBinders(c.header.indices, envWithParams)
    val resultTy = elabType(c.header.resultTy, envWithIndices)
    val header = CA.InductiveHeader(c.header.name, params, indices, resultTy, c.span)

    val ctorBaseEnv = envWithParams.addGlobal(c.header.name)
    val ctors =
      c.ctors.map { ctor =>
        val (fields, envWithFields) = elabBinders(ctor.fields, ctorBaseEnv.enterScope)
        CA.ConstructorDecl(
          name = c.header.name + "::" + ctor.name,
          fields = fields,
          resultTy = elabType(ctor.resultTy, envWithFields),
          span = ctor.span
        )
      }
    val nextEnv = ctors.foldLeft(env.addGlobal(c.header.name))((cur, ctor) => cur.addGlobal(ctor.name))
    (CA.Decl.InductiveDecl(header, ctors, c.isStruct, c.span), nextEnv)
  }

  private def elabDecl(surface: SurfaceAst.Decl, env: ResolveEnv): (CoreAst.Decl, ResolveEnv) =
    surface match {
      case c: SurfaceAst.Decl.ConstDecl     => elabConstDecl(c, env)
      case c: SurfaceAst.Decl.InductiveDecl => elabInductiveDecl(c, env)
    }

  def elab(surface: SurfaceAst.Decl): CoreAst.Decl = elabDecl(surface, ResolveEnv.empty)._1

  def elab(p: SA.Program): CA.Program = {
    val (decls, env) = p.decls.foldLeft((Vector.empty[CA.Decl], ResolveEnv.empty)) { case ((curDecls, curEnv), decl) =>
      val (nextDecl, nextEnv) = elabDecl(decl, curEnv)
      (curDecls :+ nextDecl, nextEnv)
    }
    CA.Program(decls, p.body.map(elabTerm(_, env)))
  }
}
