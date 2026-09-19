package com.raccoonlang

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
   * objects live in `root`. Recursive aliases resolve qualified peer paths to local refs while checking recursive
   * bodies. Open scopes are snapshots of resolved objects, so later declarations do not affect an earlier `open`.
   */
  private final case class ResolveEnv(
      scopes: List[Map[String, CA.LocalRef]],
      nextLocal: Int,
      root: NameNode,
      namespace: GlobalName,
      opens: List[OpenScope],
      reservedLocals: Set[String],
      recursiveAliases: Map[GlobalName, CA.LocalRef]
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

    def resolveQualifiedLocal(path: SurfacePath): Option[CA.LocalRef] =
      if (path.parts.isEmpty) None
      else if (path.root) recursiveAliases.get(path.parts)
      else namespace.inits.collectFirst(Function.unlift(prefix => recursiveAliases.get(prefix ++ path.parts)))

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

    def reserveRecursiveNames(names: Iterable[String]): ResolveEnv =
      copy(reservedLocals = reservedLocals ++ names)

    def allocate(name: String): (CA.LocalRef, ResolveEnv) = {
      val ref = CA.LocalRef(nextLocal, name)
      (ref, copy(nextLocal = nextLocal + 1))
    }

    def bindRecursiveSelf(name: String, fullName: GlobalName): (CA.LocalRef, ResolveEnv) = {
      val (refs, nextEnv) = bindRecursivePeers(Vector(name -> fullName))
      (refs.head, nextEnv)
    }

    /**
     * Bind every member of a recursive group into one body scope. Unlike ordinary locals, these bindings are
     * deliberately allowed despite reservedLocals: the reservation prevents parameters and lets from shadowing the
     * group names.
     */
    def bindRecursivePeers(peers: Vector[(String, GlobalName)]): (Vector[CA.LocalRef], ResolveEnv) = {
      peers.foldLeft((Vector.empty[CA.LocalRef], this)) { case ((refs, cur), (name, fullName)) =>
        if (!cur.reservedLocals.contains(name)) throw WTF(s"$name is not reserved for recursive peer binding")
        if (cur.scopes.head.contains(name)) throw AlreadyDefined(name)
        val (ref, next) = cur.allocate(name)
        val bound = next.copy(
          scopes = (next.scopes.head + (name -> ref)) :: next.scopes.tail,
          recursiveAliases = next.recursiveAliases + (fullName -> ref)
        )
        (refs :+ ref, bound)
      }
    }

    def bindNamed(name: String, allowShadow: Boolean): (CA.LocalRef, ResolveEnv) =
      if (reservedLocals.contains(name)) throw AlreadyDefined(name)
      else if (!allowShadow && scopes.head.contains(name)) throw AlreadyDefined(name)
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
        Vector("Level"),
        Vector("Level", "zero"),
        Vector("Level", "one"),
        Vector("Prop")
      )

    private val builtinRoot: NameNode =
      BuiltinGlobals
        .foldLeft(NameNode()) { case (root, name) => root.insertGlobal(name, name) }

    def empty: ResolveEnv =
      ResolveEnv(
        List(Map.empty),
        0,
        builtinRoot,
        Vector.empty,
        List(Map.empty[String, ResolvedObject]),
        Set.empty,
        Map.empty
      )
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

  private def expandStructSelectors(commands: Vector[SA.Command]): Vector[SA.Command] =
    commands.flatMap {
      case decl: SA.Command.Decl.InductiveDecl =>
        structSelectorNamespace(decl) match {
          case Some(selectors) => Vector(decl, selectors)
          case None            => Vector(decl)
        }

      case SA.Command.Namespace(path, body, span) =>
        Vector(SA.Command.Namespace(path, expandStructSelectors(body), span))

      case SA.Command.Block(body, span) =>
        Vector(SA.Command.Block(expandStructSelectors(body), span))

      case SA.Command.Mutual(body, span) =>
        // A mutual block must remain one homogeneous atomic group. Structs are already ordinary
        // inductive declarations in the surface AST; only their generated selectors are lowered
        // outside the block, after all family heads and constructors have been published.
        val families = body.collect { case family: SA.Command.Decl.InductiveDecl => family }
        val selectors =
          if (families.length == body.length) families.flatMap(structSelectorNamespace)
          else Vector.empty
        Vector(SA.Command.Mutual(body, span)) ++ selectors

      case other => Vector(other)
    }

  private def structSelectorNamespace(decl: SA.Command.Decl.InductiveDecl): Option[SA.Command.Namespace] = {
    if (!decl.generateSelectors || decl.ctors.isEmpty) return None

    val header = decl.header
    val ctor = decl.ctors.head
    val storedBinders = ctor.binders
    val fields = storedBinders.zipWithIndex.filter(_._1.name != "_")
    if (fields.isEmpty) return None

    val usedNames = (header.binders ++ ctor.binders).map(_.name).toSet
    val selfName = freshGeneratedName("__self", usedNames)
    val selfSpan = header.span
    // The generated self type supplies exactly the explicit family binders; implicit ones are
    // reconstructed by projection when the family application is checked.
    val familyArgs = header.binders.collect {
      case binder if !binder.isImplicit =>
        SA.Term.Ident(binder.name, binder.span)
    }
    val implicitFamilyBinders = header.binders.map(binder => binder.copy(isImplicit = true))
    val selfType = {
      val head = SA.Term.Ident(header.name, header.span)
      if (familyArgs.isEmpty) head
      else SA.Term.App(head, familyArgs, header.span)
    }
    val selfBinder =
      SA.Binder(selfName, selfType, selfSpan)
    val selectors =
      fields.map { case (field, fieldIdx) =>
        val previousFields = storedBinders
          .take(fieldIdx)
          .collect {
            case previous if previous.name != "_" => previous.name
          }
          .toSet
        val resultTy =
          rewriteFieldType(header.name, selfName, field.ty, previousFields)
        val selectorHeader =
          SA.Command.DeclHeader(
            field.name,
            SA.FuncHeader(
              implicitFamilyBinders :+ selfBinder,
              resultTy,
              Span(selfSpan.start, resultTy.span.end, selfSpan.source)
            ),
            field.span
          )
        // The selector is an ordinary match on `self` binding every stored field and returning the
        // selected one; no motive clause, since the declared result type supplies the motive syntax.
        val argNames = storedBinders.zipWithIndex.map { case (binder, idx) =>
          if (idx == fieldIdx) field.name else if (binder.name == "_") "_" else binder.name
        }
        val body = SA.Term.Match(
          SA.Term.Ident(selfName, selfSpan),
          motive = None,
          Vector(
            SA.Term.Case(
              Vector(ctor.name),
              useShortName = true,
              argNames,
              SA.Term.Ident(field.name, field.span),
              field.span
            )
          ),
          field.span
        )

        SA.Command.Decl.ConstDecl(
          isOpaque = false,
          selectorHeader,
          decreases = None,
          SA.ConstBody.TermBody(body),
          field.span
        )
      }

    Some(SA.Command.Namespace(Vector(header.name), selectors, header.span))
  }

  @tailrec
  private def freshGeneratedName(base: String, used: Set[String], suffix: Int = 0): String = {
    val candidate = if (suffix == 0) base else s"$base$suffix"
    if (!used.contains(candidate)) candidate else freshGeneratedName(base, used, suffix + 1)
  }

  // Rewrites the shapes the type grammar can produce (Ident/Select/App/Pi); anything else
  // cannot mention fields and passes through.
  private def rewriteFieldType(
      structName: String,
      selfName: String,
      term: SA.Term,
      previousFields: Set[String]
  ): SA.Term =
    term match {
      // An earlier field mentioned in a later field's type becomes an application of that earlier
      // selector to `self`. The unqualified name resolves inside the generated namespace to the
      // sibling selector; it is spelled qualified so it also resolves when the namespace is not open.
      case SA.Term.Ident(name, span) if previousFields.contains(name) =>
        SA.Term.App(
          SA.Term.Select(SA.Term.Ident(structName, span), name, span),
          Vector(SA.Term.Ident(selfName, span)),
          span
        )

      case i: SA.Term.Ident => i

      case SA.Term.Select(base, field, span) =>
        SA.Term.Select(rewriteFieldType(structName, selfName, base, previousFields), field, span)

      case SA.Term.App(fn, args, span) =>
        SA.Term.App(
          rewriteFieldType(structName, selfName, fn, previousFields),
          args.map(arg => rewriteFieldType(structName, selfName, arg, previousFields)),
          span
        )

      case SA.Term.Pi(binders, body, span) =>
        // Binders in one group scope left to right: each one's type sees the names bound before it,
        // and the body sees them all.
        val (rewrittenBinders, bodyFields) =
          binders.foldLeft((Vector.empty[SA.Binder], previousFields)) { case ((acc, fields), binder) =>
            (acc :+ binder.copy(ty = rewriteFieldType(structName, selfName, binder.ty, fields)), fields - binder.name)
          }
        SA.Term.Pi(rewrittenBinders, rewriteFieldType(structName, selfName, body, bodyFields), span)

      case other => other
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

    def resolveNonLocalPath: A =
      env.resolveQualifiedLocal(path) match {
        case Some(ref) => local(ref, path.span)
        case None      => env.resolvePath(path)(global, select)
      }

    if (!path.root && path.parts.nonEmpty) {
      env.scopes.collectFirst(Function.unlift(_.get(path.parts.head))) match {
        case Some(ref) => selectTail(local(ref, path.span), path.parts.tail)
        case None      => resolveNonLocalPath
      }
    } else {
      resolveNonLocalPath
    }
  }

  private def elabPathTerm(path: SurfacePath, env: ResolveEnv): CA.Term =
    elabPath[CA.Term](path, env)(
      (ref, span) => CA.Term.LocalRef(ref, span),
      (name, span) => CA.Term.GlobalRef(name, span),
      (base, field, span) => CA.Term.Select(base, field, span)
    )

  /**
   * A surface Pi's binders are already exactly its group — the parser decided the grouping — so a Pi body is NOT merged
   * into the enclosing group. `(a: A) -> ((b: B) -> C)` stays a 1-ary Pi returning a Pi, which is a different type from
   * the 2-ary `(a: A) -> (b: B) -> C`.
   */
  private def elabPi(pi: SA.Term.Pi, env: ResolveEnv): CA.Term.Pi = {
    val piEnv = env.enterLocalScope
    val (binders, binderEnv) = elabBinders(pi.binders, piEnv)
    val body = elabTerm(pi.body, binderEnv)
    val span = Span(binders.head.span.start, body.span.end, binders.head.span.source.orElse(body.span.source))
    CA.Term.Pi(binders, body, span)
  }

  private def elabBinder(b: SA.Binder, env: ResolveEnv): (CA.Binder, ResolveEnv) = {
    val ty = elabTerm(b.ty, env)
    val (ref, nextEnv) =
      if (b.name == "_") env.allocate(b.name)
      else env.bindNamed(b.name, allowShadow = false)
    (CA.Binder(ref, ty, b.span, b.isImplicit), nextEnv)
  }

  private def elabBinders(binders: Vector[SA.Binder], env: ResolveEnv): (Vector[CA.Binder], ResolveEnv) =
    binders.foldLeft((Vector.empty[CA.Binder], env)) { case ((curBinders, curEnv), binder) =>
      val (nextBinder, nextEnv) = elabBinder(binder, curEnv)
      (curBinders :+ nextBinder, nextEnv)
    }

  private final case class HeaderResult(ty: CA.Term, bodyEnv: ResolveEnv)

  private final case class PreparedRecursiveDefinition(
      surface: SA.Command.Decl.ConstDecl,
      name: GlobalName,
      header: HeaderResult,
      pi: CA.Term.Pi,
      decrease: SA.DecreaseSpec
  )

  private final case class PreparedInductive(
      surface: SA.Command.Decl.InductiveDecl,
      name: GlobalName,
      header: CA.InductiveHeader,
      constructorParamEnv: ResolveEnv
  )

  private final case class ElaboratedInductive(
      declaration: CA.Decl.InductiveDecl,
      constructorNames: Vector[GlobalName]
  )

  private def elabHeader(header: SA.FuncHeader, env: ResolveEnv): HeaderResult = {
    val headerEnv = env.enterLocalScope
    val (params, bodyEnv) = elabBinders(header.params, headerEnv)
    val outTy = elabTerm(header.ty, bodyEnv)
    val ty =
      if (params.isEmpty) outTy
      else CA.Term.Pi(params, outTy, header.span)
    HeaderResult(ty, bodyEnv)
  }

  def getType(header: SA.FuncHeader): CA.Term =
    elabHeader(header, ResolveEnv.empty).ty

  private def elabLam(
      pi: CA.Term.Pi,
      bodyEnv: ResolveEnv,
      body: SA.Term,
      name: Option[String],
      recursion: Option[CA.Recursion],
      span: Span
  ): CA.Term.Lam = {
    CA.Term.Lam(pi, elabTerm(body, bodyEnv), span, name, recursion)
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
    case SA.Term.NatLit(value, span)   => CA.Term.NatLit(value, span)
    case SA.Term.StrLit(scalars, span) => CA.Term.StrLit(scalars, span)
    case i: SA.Term.Ident =>
      elabPathTerm(identPath(i.name, i.span), env)
    case s: SA.Term.Select =>
      flattenTermPath(s) match {
        case Some(path) => elabPathTerm(path, env)
        case None       => CA.Term.Select(elabTerm(s.base, env), s.field, s.span)
      }
    case SA.Term.App(fn, args, sp) => CA.Term.App(elabTerm(fn, env), args.map(elabTerm(_, env)), sp)
    case pi: SA.Term.Pi            => elabPi(pi, env)
    case l: SA.Term.Lam =>
      val header = elabHeader(l.header, env)
      header.ty match {
        case pi: CA.Term.Pi =>
          elabLam(pi, header.bodyEnv, l.body, None, None, l.span)
        case _ => throw WTF("Lambda header must produce a function type", Some(l.span))
      }
    case b: SA.Term.Body =>
      val checkedLets = Vector.newBuilder[CA.Let]
      val startEnv = env.enterOpenScope
      // Body-local opens and lets are ordered; each statement affects only what follows it.
      val bodyEnv = b.statements.foldLeft(startEnv) { case (curEnv, stmt) =>
        stmt match {
          case SA.Term.OpenStmt(open) =>
            curEnv.addOpen(open)
          case SA.Term.LetStmt(l) =>
            val ty = l.ty.map(elabTerm(_, curEnv))
            val value = elabTerm(l.value, curEnv)
            val (ref, nextEnv) = curEnv.bindRequired(l.name, l.span, allowShadow = true)
            checkedLets += CA.Let(ref, ty, value, l.span)
            nextEnv
        }
      }
      CA.Term.Body(checkedLets.result(), elabTerm(b.out, bodyEnv), b.span)
    case SA.Term.Match(scrut, motive, cases, sp) =>
      CA.Term.Match(
        elabTerm(scrut, env),
        motive.map(elabTerm(_, env)),
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

  /**
   * Elaborate a mutually recursive definition group. All peer names are installed in the resolver before any body is
   * elaborated, but the resulting Core declaration is published atomically by the interpreter.
   */
  private def elabMutualDefs(
      defs: Vector[SA.Command.Decl.ConstDecl],
      env: ResolveEnv,
      span: Span
  ): (CA.Decl, ResolveEnv) = {
    val names = defs.map(defn => env.qualify(defn.header.name))
    val groupEnv = names.foldLeft(env)((cur, name) => cur.addGlobal(name))
    val reserved = env.reserveRecursiveNames(defs.map(_.header.name))

    // Allocate the header binders in a shared allocator so peer refs cannot collide with one
    // another or with a different member's parameter refs.
    var allocator = reserved
    val headers = defs.zip(names).map { case (defn, name) =>
      if (defn.isOpaque)
        throw InvalidRecursiveGroup("mutual definitions cannot be opaque", Some(defn.span))
      defn.body match {
        case SA.ConstBody.TermBody(_) =>
        case SA.ConstBody.Builtin(_) =>
          throw InvalidRecursiveGroup("mutual definitions cannot have builtin bodies", Some(defn.span))
      }
      val decrease = defn.decreases.getOrElse {
        throw InvalidDecreaseSpec("every mutual definition requires a decreases annotation", Some(defn.span))
      }
      val header = elabHeader(defn.header.funcHeader, allocator)
      allocator = allocator.copy(nextLocal = header.bodyEnv.nextLocal)
      header.ty match {
        case pi: CA.Term.Pi => PreparedRecursiveDefinition(defn, name, header, pi, decrease)
        case _ =>
          throw InvalidDecreaseSpec("decreases requires a function definition", Some(defn.span))
      }
    }

    val peerInfo = headers.map(definition => definition.surface.header.name -> definition.name)
    val (peerRefs, peerEnv) = allocator.bindRecursivePeers(peerInfo)
    val aliases = peerInfo.zip(peerRefs).map { case ((_, name), ref) => name -> ref }.toMap
    val peerBindings = peerInfo.zip(peerRefs).map { case ((localName, _), ref) => localName -> ref }.toMap

    val definitions = headers.zip(peerRefs).map { case (definition, ownPeerRef) =>
      val bodyEnv = definition.header.bodyEnv
      val bodyBase = bodyEnv.copy(
        nextLocal = peerEnv.nextLocal,
        scopes = (bodyEnv.scopes.head ++ peerBindings) :: bodyEnv.scopes.tail,
        recursiveAliases = aliases
      )
      val decrease = elabDecreaseSpec(definition.decrease, bodyEnv)
      val body = definition.surface.body match {
        case SA.ConstBody.TermBody(term) => elabTerm(term, bodyBase)
        case SA.ConstBody.Builtin(_) =>
          throw WTF("builtin body reached mutual elaboration", Some(definition.surface.span))
      }
      CA.RecursiveDef(
        globalName(definition.name),
        ownPeerRef,
        definition.pi,
        body,
        decrease,
        definition.surface.span
      )
    }
    (CA.Decl.RecursiveDefBlock(definitions, span), groupEnv)
  }

  /**
   * Elaborate one or more inductive families. Family signatures see only the incoming environment; constructors see
   * every family head, but no constructors, matching the Core block checker's provisional environment.
   */
  private def elabInductiveFamilies(
      families: Vector[SA.Command.Decl.InductiveDecl],
      env: ResolveEnv
  ): (Vector[CA.Decl.InductiveDecl], ResolveEnv) = {
    val names = families.map(family => env.qualify(family.header.name))
    val familyEnv = names.foldLeft(env)((cur, name) => cur.addGlobal(name))
    var nextLocal = env.nextLocal

    val prepared = families.zip(names).map { case (family, name) =>
      val headerEnv = env.copy(nextLocal = nextLocal).enterLocalScope
      val (params, envWithParams) = elabBinders(family.header.params, headerEnv)
      val (indices, envWithIndices) = elabBinders(family.header.indices, envWithParams)
      val resultTy = elabTerm(family.header.resultTy, envWithIndices)
      nextLocal = envWithIndices.nextLocal
      PreparedInductive(
        family,
        name,
        CA.InductiveHeader(globalName(name), params, indices, resultTy, family.span),
        envWithParams
      )
    }

    val elaborated = prepared.map { family =>
      val constructorNames = family.surface.ctors.map(ctor => family.name :+ ctor.name)
      val constructors = family.surface.ctors.zip(constructorNames).map { case (constructor, name) =>
        val constructorEnv = family.constructorParamEnv.copy(root = familyEnv.root, nextLocal = nextLocal)
        val (binders, envWithBinders) = elabBinders(constructor.binders, constructorEnv)
        nextLocal = envWithBinders.nextLocal
        CA.ConstructorDecl(
          canonicalName = globalName(name),
          shortName = constructor.name,
          binders = binders,
          resultTy = elabTerm(constructor.resultTy, envWithBinders),
          span = constructor.span
        )
      }
      ElaboratedInductive(
        CA.Decl.InductiveDecl(family.header, constructors, family.surface.span),
        constructorNames
      )
    }

    val finalEnv = elaborated.flatMap(_.constructorNames).foldLeft(familyEnv)((cur, name) => cur.addGlobal(name))
    (elaborated.map(_.declaration), finalEnv)
  }

  private def elabMutualInductives(
      families: Vector[SA.Command.Decl.InductiveDecl],
      env: ResolveEnv,
      span: Span
  ): (CA.Decl, ResolveEnv) = {
    val (declarations, finalEnv) = elabInductiveFamilies(families, env)
    (CA.Decl.InductiveBlock(declarations, span), finalEnv)
  }

  private def elabMutual(mutual: SA.Command.Mutual, env: ResolveEnv): (CA.Decl, ResolveEnv) = {
    if (mutual.body.isEmpty)
      throw InvalidRecursiveGroup("the group must not be empty", Some(mutual.span))

    val definitions = mutual.body.collect { case definition: SA.Command.Decl.ConstDecl => definition }
    val families = mutual.body.collect { case family: SA.Command.Decl.InductiveDecl => family }
    if (definitions.length == mutual.body.length)
      elabMutualDefs(definitions, env, mutual.span)
    else if (families.length == mutual.body.length)
      elabMutualInductives(families, env, mutual.span)
    else
      throw InvalidRecursiveGroup(
        "a mutual group must contain only definitions or only inductive declarations",
        Some(mutual.span)
      )
  }

  private def elabDecl(surface: SurfaceAst.Command.Decl, env: ResolveEnv): (CoreAst.Decl, ResolveEnv) =
    surface match {
      case c: SurfaceAst.Command.Decl.ConstDecl =>
        val name = env.qualify(c.header.name)
        val nameText = globalName(name)
        val headerEnv = c.decreases match {
          case Some(_) => env.reserveRecursiveNames(Vector(c.header.name))
          case None    => env
        }
        val header = elabHeader(c.header.funcHeader, headerEnv)
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
            // Only defs with header params become lambdas; a bare-body def (even one whose
            // declared type is a Pi, e.g. `def alias : Nat -> Nat := myFn`) checks its body
            // against the full declared type instead.
            header.ty match {
              case pi: CA.Term.Pi if c.header.funcHeader.params.nonEmpty =>
                val (recursion, bodyHeaderEnv) = c.decreases match {
                  case Some(decreases) =>
                    val (selfRef, nextEnv) = header.bodyEnv.bindRecursiveSelf(c.header.name, name)
                    (Some(CA.Recursion(selfRef, elabDecreaseSpec(decreases, header.bodyEnv))), nextEnv)
                  case None => (None, header.bodyEnv.copy(root = envWithSelf.root))
                }
                CA.ConstBody.TermBody(
                  elabLam(
                    pi,
                    bodyHeaderEnv,
                    term,
                    Some(nameText),
                    recursion,
                    c.span
                  )
                )
              case _ =>
                if (c.decreases.nonEmpty)
                  throw InvalidDecreaseSpec("decreases requires a function definition", Some(c.decreases.get.span))
                CA.ConstBody.TermBody(elabTerm(term, envWithSelf))
            }
        }
        (
          CA.Decl.ConstDecl(c.isOpaque, nameText, header.ty, body, c.span),
          envWithSelf
        )
      case c: SurfaceAst.Command.Decl.AxiomDecl =>
        val name = env.qualify(c.header.name)
        val nameText = globalName(name)
        val header = elabHeader(c.header.funcHeader, env)
        (
          CA.Decl.AxiomDecl(nameText, header.ty, c.span),
          env.addGlobal(name)
        )
      case c: SurfaceAst.Command.Decl.InductiveDecl =>
        val (declarations, nextEnv) = elabInductiveFamilies(Vector(c), env)
        (declarations.head, nextEnv)
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
      case mutual: SA.Command.Mutual =>
        val (mutualDecl, nextEnv) = elabMutual(mutual, curEnv)
        decls += mutualDecl
        curEnv = nextEnv
    }
    (decls.result(), curEnv)
  }

  /** Resolved prelude name trie, built once per Prelude.Config (cached on Config.names). */
  final class PreludeNames private[Elaborator] (private[Elaborator] val root: NameNode)

  def preludeNames(prelude: Prelude.Config): PreludeNames = {
    val (_, env) = elabCommands(expandStructSelectors(prelude.surface.decls), ResolveEnv.empty)
    new PreludeNames(env.root)
  }

  private[raccoonlang] def elabWithoutPrelude(p: SA.Program): CA.Program =
    elabProgram(p, ResolveEnv.empty)

  private[raccoonlang] def elab(p: SA.Program): CA.Program =
    elab(p, Prelude.default)

  private[raccoonlang] def elab(p: SA.Program, prelude: Prelude.Config): CA.Program =
    elabProgram(p, ResolveEnv.empty.copy(root = prelude.names.root))

  /** Elaborate a surface program into the opaque input accepted by [[TypeChecker.check]]. */
  def elaborate(p: SA.Program, prelude: Prelude.Config = Prelude.default): Execution.ElaboratedProgram =
    Execution.elaborate(p, prelude)

  private def elabProgram(p: SA.Program, startEnv: ResolveEnv): CA.Program = {
    p.imports.headOption.foreach { imp =>
      throw UnsupportedImport(imp.path.mkString("."), Some(imp.span))
    }

    val (decls, env) = elabCommands(expandStructSelectors(p.decls), startEnv)
    CA.Program(decls, p.body.map(elabTerm(_, env)))
  }
}
