package com.raccoonlang

import com.raccoonlang.CoreAst.UnfoldStrategy

import scala.annotation.tailrec

object Elaborator {
  val SA = SurfaceAst
  val CA = CoreAst

  private type GlobalName = Vector[String]

  private val RootName = "_root_"

  private def globalName(parts: GlobalName): String = parts.mkString(".")

  /**
   * Immutable global-name trie.
   *
   * A node may be both a global binding and a namespace object. For example, the inductive head `Nat` is a binding, and
   * it also has constructor children such as `Nat.zero`.
   *
   * Namespace-ness is derived from children. Empty namespace blocks are only lexical scopes; they do not create
   * openable namespace objects until a declaration exists under them.
   */
  private final case class NameNode(
      binding: Option[GlobalName] = None,
      children: Map[String, NameNode] = Map.empty
  ) {
    def lookup(parts: GlobalName): Option[NameNode] =
      if (parts.isEmpty) Some(this)
      else children.get(parts.head).flatMap(_.lookup(parts.tail))

    def insertGlobal(parts: GlobalName, fullName: GlobalName): NameNode =
      if (parts.isEmpty) {
        binding match {
          case Some(_) => throw AlreadyDefined(globalName(fullName))
          case None    => copy(binding = Some(fullName))
        }
      } else {
        val child = children.getOrElse(parts.head, NameNode())
        val nextChild = child.insertGlobal(parts.tail, fullName)
        copy(children = children + (parts.head -> nextChild))
      }
  }

  private final case class ResolvedObject(path: GlobalName, node: NameNode)
  private type OpenScope = Map[String, ResolvedObject]

  /**
   * Source-name resolution state.
   *
   * Locals are resolved outside the global trie and always win on the first path segment. Global names and namespace
   * objects live in `root`. Open scopes are snapshots of resolved objects, so later declarations do not affect an
   * earlier `open`.
   */
  private final case class ResolveEnv(
      scopes: List[Map[String, CA.LocalRef]],
      nextLocal: Int,
      root: NameNode,
      namespace: GlobalName,
      opens: List[OpenScope]
  ) {
    def enterLocalScope: ResolveEnv = copy(scopes = Map.empty[String, CA.LocalRef] :: scopes)

    def enterOpenScope: ResolveEnv = copy(opens = Map.empty[String, ResolvedObject] :: opens)

    def exitScoped(inner: ResolveEnv): ResolveEnv = copy(root = inner.root)

    private def rootObject(parts: GlobalName): Option[ResolvedObject] =
      root.lookup(parts).map(ResolvedObject(parts, _))

    private def scopedObject(parts: GlobalName): Option[ResolvedObject] =
      namespace.inits
        .map(prefix => prefix ++ parts)
        .collectFirst(Function.unlift(rootObject))

    /**
     * Resolve the first segment, then commit to that object while descending the remaining path.
     *
     * There is intentionally no backtracking across opens after the first segment resolves. If `Tree` resolves to the
     * current namespace's object, `Tree.leaf` means a child of that object, not a later open candidate.
     */
    private def resolveObjectPrefix(path: SurfacePath): Option[(ResolvedObject, GlobalName)] = {
      val startOpt =
        path.parts.headOption
          .flatMap { first =>
            if (path.root) rootObject(Vector(first))
            else scopedObject(Vector(first)).orElse(opens.collectFirst(Function.unlift(_.get(first))))
          }

      @tailrec
      def descend(cur: ResolvedObject, tail: GlobalName): (ResolvedObject, GlobalName) =
        if (tail.isEmpty) (cur, Vector.empty)
        else
          cur.node.children.get(tail.head) match {
            case Some(child) => descend(ResolvedObject(cur.path :+ tail.head, child), tail.tail)
            case None        => (cur, tail)
          }

      startOpt.map(start => descend(start, path.parts.tail))
    }

    def resolvePath[A](path: SurfacePath)(
        global: (String, Span) => A,
        select: (A, String, Span) => A
    ): A = {
      def selectTail(base: A, tail: Vector[String]): A =
        tail.foldLeft(base) { case (cur, field) => select(cur, field, path.span) }

      def globalRef(name: GlobalName): A =
        global(globalName(name), path.span)

      val (obj, tail) = resolveObjectPrefix(path).getOrElse {
        throw NotFound(path.parts.headOption.getOrElse(RootName), Some(path.span))
      }
      if (tail.isEmpty) {
        obj.node.binding match {
          case Some(name) => globalRef(name)
          case None       => throw NotFound(globalName(obj.path), Some(path.span))
        }
      } else {
        obj.node.binding match {
          case Some(name) => selectTail(globalRef(name), tail)
          case None       => throw NotFound(globalName(obj.path :+ tail.head), Some(path.span))
        }
      }
    }

    def resolveGlobalBinding(parts: GlobalName, span: Span): GlobalName = {
      val (obj, tail) = resolveObjectPrefix(SurfacePath(root = false, parts, span)).getOrElse {
        throw NotFound(parts.headOption.getOrElse(RootName), Some(span))
      }
      if (tail.nonEmpty)
        throw NotFound(globalName(obj.path :+ tail.head), Some(span))
      obj.node.binding match {
        case Some(name) => name
        case None       => throw NotFound(globalName(obj.path), Some(span))
      }
    }

    /** Snapshot an open into the current open scope and reject alias conflicts immediately. */
    def addOpen(open: SA.Command.Open): ResolveEnv = {
      def openName: String =
        if (open.root) (RootName +: open.namespace).mkString(".") else globalName(open.namespace)

      val namespace =
        resolveObjectPrefix(SurfacePath(open.root, open.namespace, open.span))
          .collect { case (obj, tail) if tail.isEmpty && obj.node.children.nonEmpty => obj }
          .getOrElse(throw NotFound(openName, Some(open.span)))

      val excludes = open.rules.collect { case SA.Command.AliasRule.Exclude(name) => name }.toSet
      val aliases = Vector.newBuilder[(String, ResolvedObject)]

      if (open.rules.contains(SA.Command.AliasRule.Wildcard)) {
        namespace.node.children.toVector.sortBy(_._1).foreach { case (name, child) =>
          if (!excludes(name))
            aliases += name -> ResolvedObject(namespace.path :+ name, child)
        }
      }

      open.rules.foreach {
        case SA.Command.AliasRule.Include(name, as) =>
          namespace.node.children.get(name) match {
            case Some(child) =>
              aliases += as.getOrElse(name) -> ResolvedObject(namespace.path :+ name, child)
            case None =>
              throw NotFound(globalName(namespace.path :+ name), Some(open.span))
          }
        case SA.Command.AliasRule.Wildcard | SA.Command.AliasRule.Exclude(_) =>
      }

      val nextOpenScope =
        aliases.result().foldLeft(opens.head) { case (scope, (alias, obj)) =>
          scope.get(alias) match {
            case Some(existing) if existing.path == obj.path =>
              scope + (alias -> obj)
            case Some(existing) =>
              throw AmbiguousName(alias, Vector(globalName(existing.path), globalName(obj.path)), Some(open.span))
            case None =>
              scope + (alias -> obj)
          }
        }
      copy(opens = nextOpenScope :: opens.tail)
    }

    def addGlobal(name: GlobalName): ResolveEnv =
      copy(root = root.insertGlobal(name, name))

    def qualify(name: String): GlobalName = namespace :+ name

    def hasLocal(name: String): Boolean =
      scopes.exists(_.contains(name))

    def allocate(name: String): (CA.LocalRef, ResolveEnv) = {
      val ref = CA.LocalRef(nextLocal, name)
      (ref, copy(nextLocal = nextLocal + 1))
    }

    def bindNamed(name: String, allowShadow: Boolean): (CA.LocalRef, ResolveEnv) =
      if (!allowShadow && scopes.head.contains(name)) throw AlreadyDefined(name)
      else {
        val (ref, nextEnv) = allocate(name)
        (ref, nextEnv.copy(scopes = (scopes.head + (name -> ref)) :: scopes.tail))
      }

    def bind(name: String, allowShadow: Boolean = false): (Option[CA.LocalRef], ResolveEnv) =
      if (name == "_") (None, this)
      else {
        val (ref, nextEnv) = bindNamed(name, allowShadow)
        (Some(ref), nextEnv)
      }

    def bindRequired(name: String, span: Span, allowShadow: Boolean = false): (CA.LocalRef, ResolveEnv) =
      bind(name, allowShadow) match {
        case (Some(ref), nextEnv) => (ref, nextEnv)
        case (None, _)            => throw WTF("Anonymous binding is not supported here", Some(span))
      }
  }

  private object ResolveEnv {
    private val BuiltinGlobals: Set[GlobalName] =
      Set(
        Vector("Type"),
        Vector("Normalizer"),
        Vector("Level"),
        Vector("Level", "zero"),
        Vector("Level", "one"),
        Vector("Prop")
      )

    private val builtinRoot: NameNode =
      BuiltinGlobals
        .foldLeft(NameNode()) { case (root, name) => root.insertGlobal(name, name) }

    def empty: ResolveEnv =
      ResolveEnv(List(Map.empty), 0, builtinRoot, Vector.empty, List(Map.empty[String, ResolvedObject]))
  }

  private final case class SurfacePath(root: Boolean, parts: Vector[String], span: Span)

  private def identPath(name: String, span: Span): SurfacePath =
    SurfacePath(root = name == RootName, if (name == RootName) Vector.empty else Vector(name), span)

  private def appendPath(path: SurfacePath, field: String, span: Span): SurfacePath =
    path.copy(parts = path.parts :+ field, span = Span(path.span.start, span.end, path.span.source.orElse(span.source)))

  private def flattenTermPath(term: SA.Term): Option[SurfacePath] =
    term match {
      case SA.Term.Ident(name, span) => Some(identPath(name, span))
      case SA.Term.Select(base, field, span) =>
        flattenTermPath(base).map(appendPath(_, field, span))
      case _ => None
    }

  private def flattenTypePath(term: SA.TypeTerm): Option[SurfacePath] =
    term match {
      case SA.Term.Ident(name, span) => Some(identPath(name, span))
      case SA.Term.TSelect(base, field, span) =>
        flattenTypePath(base).map(appendPath(_, field, span))
      case _ => None
    }

  /**
   * Elaborate a dotted path using the local-first rule.
   *
   * If the first segment is a local, the remaining path is a projection chain. Otherwise the entire path is resolved
   * through the global/namespace/open machinery.
   */
  private def elabPath[A](path: SurfacePath, env: ResolveEnv)(
      local: (CA.LocalRef, Span) => A,
      global: (String, Span) => A,
      select: (A, String, Span) => A
  ): A = {
    def selectTail(base: A, tail: Vector[String]): A =
      tail.foldLeft(base) { case (cur, field) => select(cur, field, path.span) }

    if (!path.root && path.parts.nonEmpty) {
      env.scopes.collectFirst(Function.unlift(_.get(path.parts.head))) match {
        case Some(ref) => selectTail(local(ref, path.span), path.parts.tail)
        case None      => env.resolvePath(path)(global, select)
      }
    } else {
      env.resolvePath(path)(global, select)
    }
  }

  private def elabPathTerm(path: SurfacePath, env: ResolveEnv): CA.Term =
    elabPath[CA.Term](path, env)(
      (ref, span) => CA.Term.LocalRef(ref, span),
      (name, span) => CA.Term.GlobalRef(name, span),
      (base, field, span) => CA.Term.Select(base, field, span)
    )

  private def elabPathType(path: SurfacePath, env: ResolveEnv): CA.TypeTerm =
    elabPath[CA.TypeTerm](path, env)(
      (ref, span) => CA.Term.LocalRef(ref, span),
      (name, span) => CA.Term.GlobalRef(name, span),
      (base, field, span) => CA.Term.TSelect(base, field, span)
    )

  private def elabPi(pi: SA.Term.Pi, env: ResolveEnv): CA.Term.Pi = {
    val piEnv = env.enterLocalScope
    val (binder, binderEnv) = elabBinder(pi.binder, piEnv)
    val body = elabType(pi.body, binderEnv)
    val span = Span(binder.span.start, body.span.end, binder.span.source.orElse(body.span.source))
    body match {
      case pi: CA.Term.Pi => CA.Term.Pi(binder +: pi.binders, pi.out, span)
      case other          => CA.Term.Pi(Vector(binder), other, span)
    }
  }

  private def elabTypeAppHead(fn: SA.TypeTerm, env: ResolveEnv): CA.Term.Ref =
    elabType(fn, env) match {
      case ref: CA.Term.Ref => ref
      case other => throw WTF(s"Type application head must resolve to a reference, got $other", Some(fn.span))
    }

  private def elabType(ty: SA.TypeTerm, env: ResolveEnv): CA.TypeTerm = ty match {
    case i: SA.Term.Ident =>
      elabPathType(identPath(i.name, i.span), env)
    case s: SA.Term.TSelect =>
      flattenTypePath(s) match {
        case Some(path) => elabPathType(path, env)
        case None       => CA.Term.TSelect(elabType(s.base, env), s.field, s.span)
      }
    case SA.Term.TApp(fn, args, sp) => CA.Term.TApp(elabTypeAppHead(fn, env), args.map(elabType(_, env)), sp)
    case pi: SA.Term.Pi             => elabPi(pi, env)
  }

  private def elabPattern(pattern: SA.TypePattern, env: ResolveEnv): (CA.TypePattern, ResolveEnv) =
    pattern match {
      case SA.TypePattern.Type(term) =>
        (CA.TypePattern.Type(elabType(term, env)), env)

      case SA.TypePattern.App(fn, args, sp) =>
        val (nextArgs, nextEnv) = args.foldLeft((Vector.empty[CA.TypePattern], env)) { case ((curArgs, curEnv), arg) =>
          val (nextArg, argEnv) = elabPattern(arg, curEnv)
          (curArgs :+ nextArg, argEnv)
        }
        (CA.TypePattern.App(elabTypeAppHead(fn, env), nextArgs, sp), nextEnv)

      case SA.TypePattern.Capture(name, sp) =>
        val (ref, nextEnv) = env.bindRequired(name, sp)
        (CA.TypePattern.Capture(ref, sp), nextEnv)
    }

  private def elabTopLevelPattern(pattern: SA.TopLevelTP, env: ResolveEnv): (CA.TopLevelTP, ResolveEnv) = {
    val (elab, nextEnv) = elabPattern(pattern, env)
    elab match {
      case topLevel: CA.TopLevelTP => (topLevel, nextEnv)
      case CA.TypePattern.Capture(ref, span) =>
        throw PatternCaptureNeedsExpectedType(ref.name, Some(span))
    }
  }

  private def elabBinderType(ty: SA.BinderType, env: ResolveEnv): (CA.BinderType, ResolveEnv) =
    ty match {
      case SA.BinderType.TypePattern(tp, sp) =>
        val (elab, nextEnv) = elabTopLevelPattern(tp, env)
        (CA.BinderType.TypePattern(elab, sp), nextEnv)

      case SA.BinderType.ConstrainedCapture(name, constraint, sp) =>
        val (elabConstraint, envWithConstraintCaptures) = elabTopLevelPattern(constraint, env)
        val (ref, nextEnv) = envWithConstraintCaptures.bindRequired(name, sp)
        (CA.BinderType.ConstrainedCapture(ref, elabConstraint, sp), nextEnv)
    }

  private def elabBinder(b: SA.Binder, env: ResolveEnv): (CA.Binder, ResolveEnv) = {
    val (ty, envWithCaptures) = elabBinderType(b.ty, env)
    val (ref, nextEnv) =
      if (b.name == "_") envWithCaptures.allocate(b.name)
      else envWithCaptures.bindNamed(b.name, allowShadow = false)
    (CA.Binder(ref, ty, b.span, b.isInstance), nextEnv)
  }

  private def elabBinders(binders: Vector[SA.Binder], env: ResolveEnv): (Vector[CA.Binder], ResolveEnv) =
    binders.foldLeft((Vector.empty[CA.Binder], env)) { case ((curBinders, curEnv), binder) =>
      val (nextBinder, nextEnv) = elabBinder(binder, curEnv)
      (curBinders :+ nextBinder, nextEnv)
    }

  private final case class HeaderResult(ty: CA.TypeTerm, bodyEnv: ResolveEnv)

  private def elabHeader(header: SA.FuncHeader, env: ResolveEnv): HeaderResult = {
    val headerEnv = env.enterLocalScope
    val (params, bodyEnv) = elabBinders(header.params, headerEnv)
    val outTy = elabType(header.ty, bodyEnv)
    val ty =
      if (params.isEmpty) outTy
      else CA.Term.Pi(params, outTy, header.span)
    HeaderResult(ty, bodyEnv)
  }

  def getType(header: SA.FuncHeader): CA.TypeTerm =
    elabHeader(header, ResolveEnv.empty).ty

  private def elabLam(
      pi: CA.Term.Pi,
      bodyEnv: ResolveEnv,
      body: SA.Term,
      name: Option[String],
      isStable: Boolean,
      decreases: Option[CA.DecreaseSpec],
      span: Span,
      outerEnv: ResolveEnv
  ): CA.Term.Lam = {
    val (uses, newBody) = body match {
      case b: SA.Term.Body =>
        val uses = Vector.newBuilder[SA.Use]
        val rest = Vector.newBuilder[SA.Term.BodyStmt]
        var seenBodyStatement = false

        // Top-level use statements attach to the lambda; later use statements are ordinary body errors.
        b.statements.foreach {
          case SA.Term.UseStmt(use) if !seenBodyStatement =>
            uses += use
          case SA.Term.UseStmt(use) =>
            throw WTF("Use statements only allowed before body statements", Some(use.span))
          case other =>
            seenBodyStatement = true
            rest += other
        }

        (uses.result(), b.copy(statements = rest.result()))
      case _ => (Vector.empty[SA.Use], body)
    }
    val checkedUses = uses.map(use => CA.Use(elabTerm(use.normalizer, outerEnv), use.span))
    CA.Term.Lam(pi, checkedUses, elabTerm(newBody, bodyEnv), span, name, isStable, decreases)
  }

  private def elabDecreaseRef(name: String, span: Span, env: ResolveEnv): CA.LocalRef =
    elabTerm(SA.Term.Ident(name, span), env) match {
      case CA.Term.LocalRef(ref, _) => ref
      case _ =>
        throw InvalidDecreaseSpec(s"$name is not a function parameter", Some(span))
    }

  private def elabDecreaseSpec(spec: SA.DecreaseSpec, env: ResolveEnv): CA.DecreaseSpec =
    spec match {
      case SA.DecreaseSpec.Structural(arg, sp) =>
        CA.DecreaseSpec.Lexicographic(Vector(elabDecreaseRef(arg, sp, env)), sp)
      case SA.DecreaseSpec.Lexicographic(args, sp) =>
        CA.DecreaseSpec.Lexicographic(args.map(arg => elabDecreaseRef(arg, sp, env)), sp)
      case SA.DecreaseSpec.Measure(term, sp) =>
        CA.DecreaseSpec.Measure(elabTerm(term, env), sp)
    }

  private def elabTerm(term: SurfaceAst.Term, env: ResolveEnv): CA.Term = term match {
    case i: SA.Term.Ident =>
      elabPathTerm(identPath(i.name, i.span), env)
    case s: SA.Term.Select =>
      flattenTermPath(s) match {
        case Some(path) => elabPathTerm(path, env)
        case None       => CA.Term.Select(elabTerm(s.base, env), s.field, s.span)
      }
    case SA.Term.App(fn, args, sp) => CA.Term.App(elabTerm(fn, env), args.map(elabTerm(_, env)), sp)
    case SA.Term.Derive(goal, sp)  => CA.Term.Derive(elabType(goal, env), sp)
    case pi: SA.Term.Pi            => elabPi(pi, env)
    case l: SA.Term.Lam =>
      val header = elabHeader(l.header, env)
      header.ty match {
        case pi: CA.Term.Pi =>
          elabLam(pi, header.bodyEnv, l.body, None, isStable = false, None, l.span, env)
        case _ => throw new RuntimeException("WTF")
      }
    case b: SA.Term.Body =>
      val checkedLets = Vector.newBuilder[CA.Let]
      val startEnv = env.enterOpenScope
      // Body-local opens and lets are ordered; each statement affects only what follows it.
      val bodyEnv = b.statements.foldLeft(startEnv) { case (curEnv, stmt) =>
        stmt match {
          case SA.Term.UseStmt(use) =>
            throw WTF("Use statements only allowed at top of fn declaration", Some(use.span))
          case SA.Term.OpenStmt(open) =>
            curEnv.addOpen(open)
          case SA.Term.LetStmt(l) =>
            val ty = l.ty.map(elabType(_, curEnv))
            val value = elabTerm(l.value, curEnv)
            val (ref, nextEnv) = curEnv.bindRequired(l.name, l.span, allowShadow = true)
            checkedLets += CA.Let(ref, ty, value, l.span, l.isInstance)
            nextEnv
        }
      }
      CA.Term.Body(checkedLets.result(), elabTerm(b.out, bodyEnv), b.span)
    case SA.Term.Match(scrut, motive, cases, sp) =>
      CA.Term.Match(
        elabTerm(scrut, env),
        motive.map(elabType(_, env)),
        cases.map { c =>
          val caseEnv = env.enterLocalScope
          val (argRefs, bodyEnv) =
            c.argNames.foldLeft((Vector.empty[Option[CA.LocalRef]], caseEnv)) { case ((curRefs, curEnv), argName) =>
              val (ref, nextEnv) = curEnv.bind(argName)
              (curRefs :+ ref, nextEnv)
            }
          val (ctorName, isFullyQualified) =
            if (c.useShortName) (c.ctorPath.head, false)
            else {
              val first = c.ctorPath.head
              if (env.hasLocal(first))
                throw LocalCaseHead(first, Some(c.span))
              (globalName(env.resolveGlobalBinding(c.ctorPath, c.span)), true)
            }
          CA.Case(ctorName, isFullyQualified, argRefs, elabTerm(c.body, bodyEnv), c.span)
        },
        sp
      )
  }

  private def elabDecl(surface: SurfaceAst.Command.Decl, env: ResolveEnv): (CoreAst.Decl, ResolveEnv) =
    surface match {
      case c: SurfaceAst.Command.Decl.ConstDecl =>
        val name = env.qualify(c.header.name)
        val nameText = globalName(name)
        val header = elabHeader(c.header.funcHeader, env)
        val envWithSelf = env.addGlobal(name)
        val body = c.body match {
          case SA.ConstBody.Builtin(sp) =>
            if (c.decreases.nonEmpty)
              throw InvalidDecreaseSpec(
                "builtin definitions cannot have decreases annotations",
                Some(c.decreases.get.span)
              )
            CA.ConstBody.Builtin(sp)
          case SA.ConstBody.TermBody(term) =>
            val bodyHeaderEnv = header.bodyEnv.copy(root = envWithSelf.root)
            header.ty match {
              case pi: CA.Term.Pi =>
                val decreases = c.decreases.map(elabDecreaseSpec(_, header.bodyEnv))
                CA.ConstBody.TermBody(
                  elabLam(
                    pi,
                    bodyHeaderEnv,
                    term,
                    Some(nameText),
                    c.unfoldStrategy.contains(UnfoldStrategy.Stable),
                    decreases,
                    c.span,
                    envWithSelf
                  )
                )
              case _ =>
                if (c.decreases.nonEmpty)
                  throw InvalidDecreaseSpec("decreases requires a function definition", Some(c.decreases.get.span))
                CA.ConstBody.TermBody(elabTerm(term, envWithSelf))
            }
        }
        (
          CA.Decl.ConstDecl(c.unfoldStrategy, nameText, header.ty, body, c.span, c.isInstance),
          envWithSelf
        )
      case c: SurfaceAst.Command.Decl.AxiomDecl =>
        val name = env.qualify(c.header.name)
        val nameText = globalName(name)
        val header = elabHeader(c.header.funcHeader, env)
        (
          CA.Decl.AxiomDecl(nameText, header.ty, c.span, c.isInstance),
          env.addGlobal(name)
        )
      case c: SurfaceAst.Command.Decl.InductiveDecl =>
        val name = env.qualify(c.header.name)
        val nameText = globalName(name)
        val headerEnv = env.enterLocalScope
        val (binders, envWithBinders) = elabBinders(c.header.binders, headerEnv)
        val resultTy = elabType(c.header.resultTy, envWithBinders)
        val header = CA.InductiveHeader(nameText, binders, resultTy, c.span)

        // Constructors may refer to the inductive head, but not to sibling constructors yet.
        val ctorBaseEnv = env.addGlobal(name)
        val ctorNames = c.ctors.map(ctor => name :+ ctor.name)
        val ctors =
          c.ctors.zip(ctorNames).map { case (ctor, ctorName) =>
            val (erasedBinders, envWithErased) = elabBinders(ctor.erasedBinders, ctorBaseEnv.enterLocalScope)
            val (fields, envWithFields) = elabBinders(ctor.fields, envWithErased)
            CA.ConstructorDecl(
              canonicalName = globalName(ctorName),
              shortName = ctor.name,
              erasedBinders = erasedBinders,
              fields = fields,
              resultTy = elabType(ctor.resultTy, envWithFields),
              span = ctor.span
            )
          }
        val nextEnv = ctorNames.foldLeft(env.addGlobal(name)) { case (cur, ctorName) =>
          cur.addGlobal(ctorName)
        }
        (CA.Decl.InductiveDecl(header, ctors, c.isStruct, c.span), nextEnv)
    }

  private def elabCommands(commands: Vector[SA.Command], env: ResolveEnv): (Vector[CA.Decl], ResolveEnv) = {
    val decls = Vector.newBuilder[CA.Decl]
    var curEnv = env

    commands.foreach {
      case decl: SA.Command.Decl =>
        val (nextDecl, nextEnv) = elabDecl(decl, curEnv)
        decls += nextDecl
        curEnv = nextEnv
      case open: SA.Command.Open =>
        curEnv = curEnv.addOpen(open)
      case SA.Command.Namespace(path, body, _) =>
        val namespace = curEnv.namespace ++ path
        val innerStart = curEnv.enterOpenScope.copy(namespace = namespace)
        val (bodyDecls, innerEnd) = elabCommands(body, innerStart)
        decls ++= bodyDecls
        curEnv = curEnv.exitScoped(innerEnd)
      case SA.Command.Block(body, _) =>
        val innerStart = curEnv.enterOpenScope
        val (bodyDecls, innerEnd) = elabCommands(body, innerStart)
        decls ++= bodyDecls
        curEnv = curEnv.exitScoped(innerEnd)
    }
    (decls.result(), curEnv)
  }

  private def preludeEnv(prelude: Prelude.Config): ResolveEnv = {
    val (_, env) = elabCommands(prelude.surface.decls, ResolveEnv.empty)
    ResolveEnv.empty.copy(root = env.root)
  }

  def elab(surface: SurfaceAst.Command.Decl): CoreAst.Decl =
    elab(surface, Prelude.default)

  def elab(surface: SurfaceAst.Command.Decl, prelude: Prelude.Config): CoreAst.Decl =
    elabDecl(surface, preludeEnv(prelude))._1

  private[raccoonlang] def elabWithoutPrelude(p: SA.Program): CA.Program =
    elabProgram(p, ResolveEnv.empty)

  def elab(p: SA.Program): CA.Program =
    elab(p, Prelude.default)

  def elab(p: SA.Program, prelude: Prelude.Config): CA.Program =
    elabProgram(p, preludeEnv(prelude))

  private def elabProgram(p: SA.Program, startEnv: ResolveEnv): CA.Program = {
    p.imports.headOption.foreach { imp =>
      throw UnsupportedImport(imp.path.mkString("."), Some(imp.span))
    }

    val (decls, env) = elabCommands(p.decls, startEnv)
    CA.Program(decls, p.body.map(elabTerm(_, env)))
  }
}
