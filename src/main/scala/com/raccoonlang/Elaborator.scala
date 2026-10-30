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

    /** This trie with `fullName` bound at `parts`; a name bound already is `AlreadyDefined` at `span`. */
    def insertGlobal(parts: GlobalName, fullName: GlobalName, span: Option[Span]): NameNode =
      if (parts.isEmpty) {
        binding match {
          case Some(_) => throw AlreadyDefined(globalName(fullName), span)
          case None    => copy(binding = Some(fullName))
        }
      } else {
        val child = children.getOrElse(parts.head, NameNode())
        val nextChild = child.insertGlobal(parts.tail, fullName, span)
        copy(children = children + (parts.head -> nextChild))
      }
  }

  private final case class ResolvedObject(path: GlobalName, node: NameNode)

  /**
   * An open's alias: the object it names, and whether an `open` named it explicitly, as `open X.{a}` or
   * `open X.{a as b}` do, rather than by a wildcard. A selective alias resolves before the enclosing namespaces.
   */
  private final case class OpenAlias(obj: ResolvedObject, selective: Boolean)
  private type OpenScope = Map[String, OpenAlias]

  /**
   * Source-name resolution state.
   *
   * Locals are resolved outside the global trie and always win on the first path segment. Global names and namespace
   * objects live in `root`. The recursive-self alias resolves qualified paths to a local ref while checking recursive
   * bodies. Open scopes are snapshots of resolved objects, so later declarations do not affect an earlier `open`. A
   * first segment resolves to a selective open's alias, then to a member of the enclosing namespaces, then to a
   * wildcard open's alias, each in the innermost scope that has one (docs/namespaces.md).
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

    def enterOpenScope: ResolveEnv = copy(opens = Map.empty[String, OpenAlias] :: opens)

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
     * The object an open aliases as `name`, in the innermost open scope that has it; with `selectiveOnly`, a selective
     * one.
     */
    private def openAlias(name: String, selectiveOnly: Boolean): Option[ResolvedObject] =
      opens.collectFirst(Function.unlift(_.get(name).filter(alias => alias.selective || !selectiveOnly).map(_.obj)))

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
            else
              openAlias(first, selectiveOnly = true)
                .orElse(scopedObject(Vector(first)))
                .orElse(openAlias(first, selectiveOnly = false))
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
      val aliases = Vector.newBuilder[(String, OpenAlias)]

      if (open.rules.contains(SA.Command.AliasRule.Wildcard)) {
        namespace.node.children.toVector.sortBy(_._1).foreach { case (name, child) =>
          if (!excludes(name))
            aliases += name -> OpenAlias(ResolvedObject(namespace.path :+ name, child), selective = false)
        }
      }

      open.rules.foreach {
        case SA.Command.AliasRule.Include(name, as) =>
          namespace.node.children.get(name) match {
            case Some(child) =>
              aliases += as.getOrElse(name) -> OpenAlias(
                ResolvedObject(namespace.path :+ name, child),
                selective = true
              )
            case None =>
              throw NotFound(globalName(namespace.path :+ name), Some(open.span))
          }
        case SA.Command.AliasRule.Wildcard | SA.Command.AliasRule.Exclude(_) =>
      }

      // An alias opened twice for one object is selective when either open names it explicitly.
      val nextOpenScope =
        aliases.result().foldLeft(opens.head) { case (scope, (name, alias)) =>
          scope.get(name) match {
            case Some(existing) if existing.obj.path == alias.obj.path =>
              scope + (name -> alias.copy(selective = alias.selective || existing.selective))
            case Some(existing) =>
              throw AmbiguousName(
                name,
                Vector(globalName(existing.obj.path), globalName(alias.obj.path)),
                Some(open.span)
              )
            case None =>
              scope + (name -> alias)
          }
        }
      copy(opens = nextOpenScope :: opens.tail)
    }

    /** Declares the global `name`, written at `span`, where a redeclaration is reported. */
    def addGlobal(name: GlobalName, span: Span): ResolveEnv =
      copy(root = root.insertGlobal(name, name, Some(span)))

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
     * Bind each member of a recursive group, by its short name and its full name, to the next slots, in order. The
     * names are reserved, so no parameter shadows them; these bindings are the only ones a reserved name may have.
     */
    def bindRecursivePeers(peers: Vector[(String, GlobalName)]): (Vector[CA.LocalRef], ResolveEnv) =
      peers.foldLeft((Vector.empty[CA.LocalRef], this)) { case ((refs, cur), (name, fullName)) =>
        if (!cur.reservedLocals.contains(name)) throw WTF(s"$name is not reserved for recursive binding")
        val (ref, next) = cur.allocate(name)
        val bound = next.copy(
          scopes = (next.scopes.head + (name -> ref)) :: next.scopes.tail,
          recursiveAliases = next.recursiveAliases + (fullName -> ref)
        )
        (refs :+ ref, bound)
      }

    /**
     * Binds the local `name`, written at `span`. It may not rebind a recursive definition's own name, nor, unless
     * `allowShadow`, a name of the same scope (`AlreadyDefined` at `span`).
     */
    def bindNamed(name: String, allowShadow: Boolean, span: Span): (CA.LocalRef, ResolveEnv) =
      if (reservedLocals.contains(name)) throw AlreadyDefined(name, Some(span))
      else if (!allowShadow && scopes.head.contains(name)) throw AlreadyDefined(name, Some(span))
      else {
        val (ref, nextEnv) = allocate(name)
        (ref, nextEnv.copy(scopes = (scopes.head + (name -> ref)) :: scopes.tail))
      }

    def bind(name: String, span: Span, allowShadow: Boolean = false): (Option[CA.LocalRef], ResolveEnv) =
      if (name == "_") (None, this)
      else {
        val (ref, nextEnv) = bindNamed(name, allowShadow, span)
        (Some(ref), nextEnv)
      }

    def bindRequired(name: String, span: Span, allowShadow: Boolean = false): (CA.LocalRef, ResolveEnv) =
      bind(name, span, allowShadow) match {
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
        Vector("Kind"),
        Vector("Kind", "copy"),
        Vector("Kind", "lin"),
        Vector("Prop")
      )

    private val builtinRoot: NameNode =
      BuiltinGlobals
        .foldLeft(NameNode()) { case (root, name) => root.insertGlobal(name, name, None) }

    private def withRoot(root: NameNode): ResolveEnv =
      ResolveEnv(
        List(Map.empty),
        0,
        root,
        Vector.empty,
        List(Map.empty[String, OpenAlias]),
        Set.empty,
        Map.empty
      )

    /** Primitive names only; the kernel's own declarations elaborate here. */
    def primitive: ResolveEnv = withRoot(builtinRoot)

    /** Primitive and kernel names, visible to every prelude and program. */
    def kernel: ResolveEnv = withRoot(kernelRoot)
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

      // A block's families have their selectors after it, once every family of it is published.
      case mutual @ SA.Command.Mutual(body, _) =>
        mutual +: body.collect { case family: SA.Command.Decl.InductiveDecl => family }.flatMap(structSelectorNamespace)

      case other => Vector(other)
    }

  private def checkConstructorParamDiscipline(
      header: SA.Command.InductiveHeader,
      ctor: SA.Command.ConstructorDecl,
      ctorName: String
  ): Unit = {
    val paramNames = header.params.map(_.name).toSet
    val indexNames = header.indices.map(_.name).toSet

    ctor.erasedBinders.foldLeft(Set.empty[String]) { case (seen, binder) =>
      if (!paramNames.contains(binder.name)) {
        val reason =
          if (indexNames.contains(binder.name)) "indices must be passed through constructor fields or type patterns"
          else if (header.params.isEmpty) "this inductive has no params"
          else s"expected one of ${header.params.map(_.name).mkString(", ")}"
        throw InvalidErasedConstructorBinder(ctorName, binder.name, reason, Some(binder.span))
      }
      if (seen.contains(binder.name))
        throw InvalidErasedConstructorBinder(ctorName, binder.name, "duplicate erased parameter", Some(binder.span))
      seen + binder.name
    }

    ctor.fields.find(field => paramNames.contains(field.name)).foreach { field =>
      throw InvalidErasedConstructorBinder(
        ctorName,
        field.name,
        "constructor fields named like inductive params must be erased",
        Some(field.span)
      )
    }

    val fieldCaptures = ctor.fields.flatMap(field => binderTypeCaptureNames(field.ty))

    header.params.foreach { param =>
      val erasedWitnesses = ctor.erasedBinders.filter(_.name == param.name)
      val captureWitnesses = fieldCaptures.filter(_ == param.name)

      val witnessCount = erasedWitnesses.length + captureWitnesses.length
      if (witnessCount != 1)
        throw InvalidErasedConstructorBinder(
          ctorName,
          param.name,
          "expected exactly one erased binder or type-pattern capture for this inductive parameter",
          Some(ctor.span)
        )
    }
  }

  private def binderTypeCaptureNames(binderType: SA.BinderType): Vector[String] =
    binderType match {
      case SA.BinderType.TypePattern(tp, _) => typePatternCaptureNames(tp)
      case SA.BinderType.ConstrainedCapture(name, constraint, _) =>
        typePatternCaptureNames(constraint) :+ name
    }

  private def typePatternCaptureNames(pattern: SA.TypePattern): Vector[String] =
    pattern match {
      case SA.TypePattern.Type(_) => Vector.empty
      case SA.TypePattern.Capture(name, _, constraint) =>
        constraint.toVector.flatMap(typePatternCaptureNames) :+ name
      case SA.TypePattern.App(_, args, _) => args.flatMap(typePatternCaptureNames)
    }

  /**
   * Field selectors for a family with one constructor, one for each named field (docs/kernel.md, "Structure eta and
   * projections"). Each is a lazy definition whose body is the one-branch match that returns its field, so it is
   * checked where it is first used. A family gets none when a selector's type cannot be written: when a field's type
   * names a capture that is no family parameter, a hidden dependency, or a type capture shadows an earlier field.
   */
  private def structSelectorNamespace(decl: SA.Command.Decl.InductiveDecl): Option[SA.Command.Namespace] =
    if (decl.ctors.length != 1 || hasHiddenDependency(decl)) None
    else
      try selectorNamespace(decl)
      catch { case _: InvalidStruct => None }

  /** Whether a field's type, as a selector would state it, names a capture that is no family parameter. */
  private def hasHiddenDependency(decl: SA.Command.Decl.InductiveDecl): Boolean = {
    val params = decl.header.binders.map(_.name).toSet
    def named(pattern: SA.TypePattern): Vector[String] =
      pattern match {
        case SA.TypePattern.Type(_)             => Vector.empty
        case SA.TypePattern.App(_, args, _)     => args.flatMap(named)
        case SA.TypePattern.Capture(name, _, _) => Vector(name)
      }
    decl.ctors.head.fields.exists { field =>
      val names = field.ty match {
        case SA.BinderType.TypePattern(tp, _)             => named(tp)
        case SA.BinderType.ConstrainedCapture(name, _, _) => Vector(name)
      }
      names.exists(name => !params.contains(name))
    }
  }

  private def selectorNamespace(decl: SA.Command.Decl.InductiveDecl): Option[SA.Command.Namespace] = {

    val header = decl.header
    val ctor = decl.ctors.head
    val fields = ctor.fields.filter(_.name != "_")
    if (fields.isEmpty) return None

    val usedNames = (header.binders ++ ctor.erasedBinders ++ ctor.fields).map(_.name).toSet
    val selfName = freshGeneratedName(StructEta.SelfName, usedNames)
    val selfSpan = header.span
    val selfType = {
      val head = SA.Term.Ident(header.name, header.span)
      val args = header.binders.map(binder => SA.TypePattern.Capture(binder.name, binder.span))
      if (args.isEmpty) SA.TypePattern.Type(head)
      else SA.TypePattern.App(head, args, header.span)
    }
    val selfBinder =
      SA.Binder(selfName, SA.BinderType.TypePattern(selfType, selfSpan), selfSpan)

    val selectors =
      fields.zipWithIndex.map { case (field, fieldIdx) =>
        val previousFields = fields.take(fieldIdx).map(_.name).toSet
        val resultTy = selectorResultType(header.name, selfName, field.ty, previousFields, field.span)
        val selectorHeader =
          SA.Command.DeclHeader(
            field.name,
            SA.FuncHeader(Vector(selfBinder), resultTy, Span(selfSpan.start, resultTy.span.end, selfSpan.source)),
            field.span,
            field.span
          )
        val body =
          SA.Term.Match(
            SA.Term.Ident(selfName, selfSpan),
            Some(resultTy),
            Vector(
              SA.Term.Case(
                Vector(header.name, ctor.name),
                useShortName = false,
                ctor.fields.map(_.name),
                SA.Term.Ident(field.name, field.span),
                field.span
              )
            ),
            wildcard = None,
            equation = None,
            field.span
          )

        SA.Command.Decl.ConstDecl(
          selectorHeader,
          decreases = None,
          SA.ConstBody.TermBody(body),
          field.span,
          lazyGlobal = true
        )
      }

    Some(SA.Command.Namespace(Vector(header.name), selectors, header.span))
  }

  @tailrec
  private def freshGeneratedName(base: String, used: Set[String], suffix: Int = 0): String = {
    val candidate = if (suffix == 0) base else s"$base$suffix"
    if (!used.contains(candidate)) candidate else freshGeneratedName(base, used, suffix + 1)
  }

  private def selectorResultType(
      structName: String,
      selfName: String,
      binderType: SA.BinderType,
      previousFields: Set[String],
      span: Span
  ): SA.TypeTerm =
    binderType match {
      case SA.BinderType.TypePattern(tp, _) =>
        typePatternAsType(structName, selfName, tp, previousFields, span)

      case SA.BinderType.ConstrainedCapture(name, _, captureSpan) =>
        if (previousFields.contains(name))
          throw InvalidStruct(structName, s"type capture $name shadows an earlier field", Some(captureSpan))
        SA.Term.Ident(name, captureSpan)
    }

  private def rewriteTypeTerm(
      structName: String,
      selfName: String,
      term: SA.TypeTerm,
      previousFields: Set[String]
  ): SA.TypeTerm =
    term match {
      case SA.Term.Ident(name, span) if previousFields.contains(name) =>
        selectorCall(structName, name, selfName, span)

      case i: SA.Term.Ident => i

      case lit: SA.Term.NatLit => lit

      case lit: SA.Term.StrLit => lit

      case SA.Term.TSelect(base, field, span) =>
        SA.Term.TSelect(rewriteTypeTerm(structName, selfName, base, previousFields), field, span)

      case SA.Term.TApp(fn, args, span) =>
        SA.Term.TApp(
          rewriteTypeTerm(structName, selfName, fn, previousFields),
          args.map(arg => rewriteTypeTerm(structName, selfName, arg, previousFields)),
          span
        )

      case SA.Term.Derive(goal, span) =>
        SA.Term.Derive(rewriteTypeTerm(structName, selfName, goal, previousFields), span)

      case pi: SA.Term.Pi => rewritePi(structName, selfName, pi, previousFields)

      case lam: SA.Term.Lam => rewriteLam(structName, selfName, lam, previousFields)
    }

  private def rewritePi(
      structName: String,
      selfName: String,
      pi: SA.Term.Pi,
      previousFields: Set[String]
  ): SA.Term.Pi = {
    rejectShadowingCapture(structName, pi.binder, previousFields)
    SA.Term.Pi(
      pi.binder.copy(ty = rewriteBinderType(structName, selfName, pi.binder.ty, previousFields)),
      rewriteTypeTerm(structName, selfName, pi.body, previousFields),
      pi.span
    )
  }

  /**
   * A lambda in a field's type, as a selector's type states it: its binders, codomain and body with each earlier field
   * replaced by its selector's call, where the field is in scope. A parameter, a case's field or a `let` that rebinds a
   * field's name shadows it for the rest of its scope. A type capture that does gives the family no selectors, as a
   * function type's binder does.
   */
  private def rewriteLam(
      structName: String,
      selfName: String,
      lam: SA.Term.Lam,
      previousFields: Set[String]
  ): SA.Term.Lam = {
    var fields = previousFields
    val params = lam.header.params.map { binder =>
      binderTypeCaptureNames(binder.ty).find(fields.contains).foreach { name =>
        throw InvalidStruct(structName, s"type capture $name shadows an earlier field", Some(binder.span))
      }
      val rewritten = binder.copy(ty = rewriteBinderType(structName, selfName, binder.ty, fields))
      fields -= binder.name
      rewritten
    }
    val header = lam.header.copy(params = params, ty = rewriteTypeTerm(structName, selfName, lam.header.ty, fields))
    SA.Term.Lam(header, rewriteTerm(structName, selfName, lam.body, fields), lam.span)
  }

  /** `rewriteTypeTerm` for a lambda's body, a term, where a local that rebinds a field's name shadows it. */
  private def rewriteTerm(
      structName: String,
      selfName: String,
      term: SA.Term,
      previousFields: Set[String]
  ): SA.Term = {
    def rewrite(t: SA.Term): SA.Term = rewriteTerm(structName, selfName, t, previousFields)
    def rewriteType(t: SA.TypeTerm): SA.TypeTerm = rewriteTypeTerm(structName, selfName, t, previousFields)
    def patternNames(pattern: SA.Term.BindingPattern): Vector[String] =
      pattern match {
        case SA.Term.BindingPattern.Bind(name, _)     => Vector(name)
        case _: SA.Term.BindingPattern.Discard        => Vector.empty
        case SA.Term.BindingPattern.Unpack(fields, _) => fields.flatMap(patternNames)
      }
    term match {
      case SA.Term.Ident(name, span) if previousFields.contains(name) =>
        SA.Term.App(
          SA.Term.Select(SA.Term.Ident(structName, span), name, span),
          Vector(SA.Term.Ident(selfName, span)),
          span
        )
      case _: SA.Term.Ident | _: SA.Term.NatLit | _: SA.Term.StrLit => term
      case SA.Term.Select(base, field, span)                        => SA.Term.Select(rewrite(base), field, span)
      case SA.Term.App(fn, args, span)                              => SA.Term.App(rewrite(fn), args.map(rewrite), span)
      case pi: SA.Term.Pi             => rewritePi(structName, selfName, pi, previousFields)
      case SA.Term.Derive(goal, span) => SA.Term.Derive(rewriteType(goal), span)
      case lam: SA.Term.Lam           => rewriteLam(structName, selfName, lam, previousFields)
      // A match's equation is bound in each case, as a case's fields are.
      case SA.Term.Match(scrut, motive, cases, wildcard, equation, span) =>
        val inCases = previousFields -- equation.map(_.name)
        val rewrittenCases =
          cases.map(c => c.copy(body = rewriteTerm(structName, selfName, c.body, inCases -- c.argNames)))
        val rewrittenWildcard = wildcard.map(w => w.copy(body = rewriteTerm(structName, selfName, w.body, inCases)))
        SA.Term.Match(rewrite(scrut), motive.map(rewriteType), rewrittenCases, rewrittenWildcard, equation, span)
      case SA.Term.Body(statements, out, span) =>
        var fields = previousFields
        val rewritten = statements.map { statement =>
          def value(t: SA.Term): SA.Term = rewriteTerm(structName, selfName, t, fields)
          def tpe(t: SA.TypeTerm): SA.TypeTerm = rewriteTypeTerm(structName, selfName, t, fields)
          statement match {
            case SA.Term.UseStmt(use)   => SA.Term.UseStmt(use.copy(normalizer = value(use.normalizer)))
            case open: SA.Term.OpenStmt => open
            case SA.Term.LetStmt(let: SA.Term.Let.Binding) =>
              val next = SA.Term.LetStmt(let.copy(ty = let.ty.map(tpe), value = value(let.value)))
              fields --= patternNames(let.pattern)
              next
            case SA.Term.LetStmt(let: SA.Term.Let.Instance) =>
              val next = SA.Term.LetStmt(let.copy(ty = let.ty.map(tpe), value = value(let.value)))
              fields -= let.name
              next
          }
        }
        SA.Term.Body(rewritten, rewriteTerm(structName, selfName, out, fields), span)
    }
  }

  private def selectorCall(structName: String, fieldName: String, selfName: String, span: Span): SA.TypeTerm =
    SA.Term.TApp(
      SA.Term.TSelect(SA.Term.Ident(structName, span), fieldName, span),
      Vector(SA.Term.Ident(selfName, span)),
      span
    )

  private def rewriteBinderType(
      structName: String,
      selfName: String,
      binderType: SA.BinderType,
      previousFields: Set[String]
  ): SA.BinderType =
    binderType match {
      case SA.BinderType.TypePattern(tp, span) =>
        SA.BinderType.TypePattern(rewriteTopLevelPattern(structName, selfName, tp, previousFields), span)

      case SA.BinderType.ConstrainedCapture(name, constraint, span) =>
        if (previousFields.contains(name))
          throw InvalidStruct(structName, s"type capture $name shadows an earlier field", Some(span))
        SA.BinderType.ConstrainedCapture(
          name,
          rewriteTopLevelPattern(structName, selfName, constraint, previousFields),
          span
        )
    }

  private def rewriteTopLevelPattern(
      structName: String,
      selfName: String,
      pattern: SA.TopLevelTP,
      previousFields: Set[String]
  ): SA.TopLevelTP =
    rewriteTypePattern(structName, selfName, pattern, previousFields) match {
      case topLevel: SA.TopLevelTP => topLevel
      case SA.TypePattern.Capture(name, span, _) =>
        throw InvalidStruct(structName, s"type capture $name needs an expected type", Some(span))
    }

  private def rewriteTypePattern(
      structName: String,
      selfName: String,
      pattern: SA.TypePattern,
      previousFields: Set[String]
  ): SA.TypePattern =
    pattern match {
      case SA.TypePattern.Type(term) =>
        SA.TypePattern.Type(rewriteTypeTerm(structName, selfName, term, previousFields))

      case SA.TypePattern.App(fn, args, span) =>
        SA.TypePattern.App(
          rewriteTypeTerm(structName, selfName, fn, previousFields),
          args.map(arg => rewriteTypePattern(structName, selfName, arg, previousFields)),
          span
        )

      case SA.TypePattern.Capture(name, span, constraint) =>
        if (previousFields.contains(name))
          throw InvalidStruct(structName, s"type capture $name shadows an earlier field", Some(span))
        SA.TypePattern.Capture(
          name,
          span,
          constraint.map(rewriteTopLevelPattern(structName, selfName, _, previousFields))
        )
    }

  private def typePatternAsType(
      structName: String,
      selfName: String,
      pattern: SA.TypePattern,
      previousFields: Set[String],
      span: Span
  ): SA.TypeTerm =
    pattern match {
      case SA.TypePattern.Type(term) =>
        rewriteTypeTerm(structName, selfName, term, previousFields)

      case SA.TypePattern.App(fn, args, appSpan) =>
        SA.Term.TApp(
          rewriteTypeTerm(structName, selfName, fn, previousFields),
          args.map(arg => typePatternAsType(structName, selfName, arg, previousFields, appSpan)),
          appSpan
        )

      case SA.TypePattern.Capture(name, captureSpan, _) =>
        if (previousFields.contains(name))
          throw InvalidStruct(structName, s"type capture $name shadows an earlier field", Some(captureSpan))
        SA.Term.Ident(name, captureSpan)
    }

  private def rejectShadowingCapture(
      structName: String,
      binder: SA.Binder,
      previousFields: Set[String]
  ): Unit = {
    if (previousFields.contains(binder.name))
      throw InvalidStruct(structName, s"Pi binder ${binder.name} shadows an earlier field", Some(binder.span))

    val captured = binderTypeCaptureNames(binder.ty).toSet
    captured.find(previousFields.contains).foreach { name =>
      throw InvalidStruct(structName, s"type capture $name shadows an earlier field", Some(binder.span))
    }
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

  private def elabPathType(path: SurfacePath, env: ResolveEnv): CA.TypeTerm =
    elabPath[CA.TypeTerm](path, env)(
      (ref, span) => CA.Term.LocalRef(ref, span),
      (name, span) => CA.Term.GlobalRef(name, span),
      (base, field, span) => CA.Term.Select(base, field, span)
    )

  private def elabPi(pi: SA.Term.Pi, env: ResolveEnv): CA.Term.Pi = {
    val piEnv = env.enterLocalScope
    val (binder, binderEnv) = elabBinder(pi.binder, piEnv)
    val body = elabType(pi.body, binderEnv)
    val span = Span(binder.span.start, body.span.end, binder.span.source.orElse(body.span.source))
    body match {
      case pi: CA.Term.Pi => CA.Term.Pi(binder +: pi.binders, pi.out, span, NodeId.fresh())
      case other          => CA.Term.Pi(Vector(binder), other, span, NodeId.fresh())
    }
  }

  /** A capture-free pattern as the type it denotes. */
  private def patternAsType(pattern: SA.TypePattern): SA.TypeTerm =
    pattern match {
      case SA.TypePattern.Type(term)          => term
      case SA.TypePattern.App(fn, args, span) => SA.Term.TApp(fn, args.map(patternAsType), span)
      case SA.TypePattern.Capture(name, span, _) =>
        throw WTF(s"A capture-free pattern holds the capture $name", Some(span))
    }

  private def elabType(ty: SA.TypeTerm, env: ResolveEnv): CA.TypeTerm = ty match {
    case i: SA.Term.Ident =>
      elabPathType(identPath(i.name, i.span), env)
    case s: SA.Term.TSelect =>
      flattenTypePath(s) match {
        case Some(path) => elabPathType(path, env)
        case None       => CA.Term.Select(elabType(s.base, env), s.field, s.span)
      }
    case SA.Term.TApp(fn, args, sp) => CA.Term.App(elabType(fn, env), args.map(elabType(_, env)), sp)
    case SA.Term.Derive(goal, sp)   => CA.Term.Derive(elabType(goal, env), sp)
    case pi: SA.Term.Pi             => elabPi(pi, env)
    case SA.Term.NatLit(number, sp) => CA.Term.NatLit(number, sp)
    case SA.Term.StrLit(text, sp)   => CA.Term.StrLit(text, sp)
    case l: SA.Term.Lam             => elabAnonymousLam(l, env)
  }

  /**
   * A lambda written as a term or inside a type. Its header's locals are scoped to it, as a function type's are, so a
   * lambda in a binder type leaves the binder's own slot where the checker puts it.
   */
  private def elabAnonymousLam(l: SA.Term.Lam, env: ResolveEnv): CA.Term.Lam = {
    val header = elabHeader(l.header, env)
    header.ty match {
      case pi: CA.Term.Pi => elabLam(pi, header.bodyEnv, l.body, None, None, l.span, env)
      case _              => throw WTF("A lambda binds a parameter", Some(l.span))
    }
  }

  private def elabPattern(pattern: SA.TypePattern, env: ResolveEnv): (CA.TypePattern, ResolveEnv) =
    pattern match {
      case SA.TypePattern.Type(term) =>
        (CA.TypePattern.Type(elabType(term, env)), env)

      // A pattern's head is a name. A head that is a projection, such as `P.Step(A, B)` for a local `P`, is read as the
      // type it applies, which needs no capture.
      case app @ SA.TypePattern.App(fn, args, sp) =>
        elabType(fn, env) match {
          case head: CA.Term.Ref =>
            val (nextArgs, nextEnv) = args.foldLeft((Vector.empty[CA.TypePattern], env)) {
              case ((curArgs, curEnv), arg) =>
                val (nextArg, argEnv) = elabPattern(arg, curEnv)
                (curArgs :+ nextArg, argEnv)
            }
            (CA.TypePattern.App(head, nextArgs, sp), nextEnv)
          case _ =>
            typePatternCaptureNames(app).headOption.foreach { name =>
              throw InvalidTypePattern(s"the capture $$$name is under a head that is not a name", Some(sp))
            }
            (CA.TypePattern.Type(elabType(patternAsType(app), env)), env)
        }

      // A constraint's captures are bound before the capture itself, as at a binder.
      case SA.TypePattern.Capture(name, sp, constraint) =>
        val (elabConstraint, constraintEnv) = constraint match {
          case Some(tp) =>
            val (elab, next) = elabTopLevelPattern(tp, env)
            (Some(elab), next)
          case None => (None, env)
        }
        val (ref, nextEnv) = constraintEnv.bindRequired(name, sp)
        (CA.TypePattern.Capture(ref, sp, elabConstraint), nextEnv)
    }

  private def elabTopLevelPattern(pattern: SA.TopLevelTP, env: ResolveEnv): (CA.TopLevelTP, ResolveEnv) = {
    val (elab, nextEnv) = elabPattern(pattern, env)
    elab match {
      case topLevel: CA.TopLevelTP => (topLevel, nextEnv)
      case CA.TypePattern.Capture(ref, span, _) =>
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
      else envWithCaptures.bindNamed(b.name, allowShadow = false, b.span)
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
      else CA.Term.Pi(params, outTy, header.span, NodeId.fresh())
    HeaderResult(ty, bodyEnv)
  }

  def getType(header: SA.FuncHeader): CA.TypeTerm =
    elabHeader(header, ResolveEnv.kernel).ty

  private def elabLam(
      pi: CA.Term.Pi,
      bodyEnv: ResolveEnv,
      body: SA.Term,
      name: Option[String],
      recursion: Option[CA.Recursion],
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
    CA.Term.Lam(pi, checkedUses, elabTerm(newBody, bodyEnv), span, name, recursion, NodeId.fresh())
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

  private sealed trait LoweredBindingPattern {
    def ref: CA.LocalRef
  }
  private object LoweredBindingPattern {
    final case class Leaf(ref: CA.LocalRef) extends LoweredBindingPattern
    final case class Unpack(ref: CA.LocalRef, children: Vector[LoweredBindingPattern], span: Span)
      extends LoweredBindingPattern
  }

  private sealed trait PatternSlot {
    def ref: CA.LocalRef
  }
  private object PatternSlot {
    final case class Leaf(ref: CA.LocalRef) extends PatternSlot
    final case class Unpack(ref: CA.LocalRef, fields: Vector[SA.Term.BindingPattern], span: Span) extends PatternSlot
  }

  private def duplicatePatternName(pattern: SA.Term.BindingPattern): Option[(String, Span)] = {
    def loop(
        current: SA.Term.BindingPattern,
        seen: Set[String]
    ): Either[(String, Span), Set[String]] = current match {
      case SA.Term.BindingPattern.Bind(name, span) =>
        if (seen.contains(name)) Left(name -> span) else Right(seen + name)
      case _: SA.Term.BindingPattern.Discard => Right(seen)
      case SA.Term.BindingPattern.Unpack(fields, _) =>
        fields.foldLeft[Either[(String, Span), Set[String]]](Right(seen)) { (acc, field) =>
          acc.flatMap(names => loop(field, names))
        }
    }

    loop(pattern, Set.empty).left.toOption
  }

  private def allocateImmediatePatternFields(
      patterns: Vector[SA.Term.BindingPattern],
      env: ResolveEnv
  ): (Vector[PatternSlot], ResolveEnv) =
    patterns.foldLeft((Vector.empty[PatternSlot], env)) { case ((nodes, curEnv), pattern) =>
      pattern match {
        case SA.Term.BindingPattern.Bind(name, span) =>
          val (ref, nextEnv) = curEnv.bindNamed(name, allowShadow = true, span)
          (nodes :+ PatternSlot.Leaf(ref), nextEnv)
        case SA.Term.BindingPattern.Discard(_) =>
          val (ref, nextEnv) = curEnv.allocate("_")
          (nodes :+ PatternSlot.Leaf(ref), nextEnv)
        case SA.Term.BindingPattern.Unpack(fields, span) =>
          val (ref, nextEnv) = curEnv.allocate("_")
          (nodes :+ PatternSlot.Unpack(ref, fields, span), nextEnv)
      }
    }

  // Allocate every immediate child slot before visiting descendants. This mirrors the runtime order of nested matches.
  private def allocatePatternDescendants(
      nodes: Vector[PatternSlot],
      env: ResolveEnv
  ): (Vector[LoweredBindingPattern], ResolveEnv) = {
    import LoweredBindingPattern.{Leaf => LoweredLeaf, Unpack => LoweredUnpack}
    import PatternSlot.{Leaf => LeafSlot, Unpack => UnpackSlot}
    nodes.foldLeft((Vector.empty[LoweredBindingPattern], env)) { case ((completed, curEnv), node) =>
      node match {
        case UnpackSlot(ref, fields, span) =>
          val (immediate, afterImmediate) = allocateImmediatePatternFields(fields, curEnv)
          val (children, afterDescendants) = allocatePatternDescendants(immediate, afterImmediate)
          (completed :+ LoweredUnpack(ref, children, span), afterDescendants)
        case LeafSlot(ref) => (completed :+ LoweredLeaf(ref), curEnv)
      }
    }
  }

  private def lowerNestedPatternMatches(
      nodes: Vector[LoweredBindingPattern],
      continuation: CA.Term
  ): CA.Term = {
    import LoweredBindingPattern._
    nodes.foldRight(continuation) {
      case (Unpack(ref, children, span), rest) =>
        val nestedBody = lowerNestedPatternMatches(children, rest)
        CA.Term.MatchOne(
          CA.Term.LocalRef(ref, span),
          None,
          children.map(_.ref),
          nestedBody,
          span,
          NodeId.fresh()
        )
      case (_: Leaf, rest) => rest
    }
  }

  private def elabBodyStatements(
      statements: Vector[SA.Term.BodyStmt],
      out: SA.Term,
      initialEnv: ResolveEnv,
      bodySpan: Span
  ): CA.Term = {
    def loop(
        remaining: Vector[SA.Term.BodyStmt],
        curEnv: ResolveEnv,
        pendingLets: Vector[CA.Let]
    ): CA.Term = remaining.headOption match {
      case None =>
        val result = elabTerm(out, curEnv)
        CA.Term.Body(pendingLets, result, bodySpan)
      case Some(SA.Term.UseStmt(use)) =>
        throw WTF("Use statements only allowed at top of fn declaration", Some(use.span))
      case Some(SA.Term.OpenStmt(open)) =>
        loop(remaining.tail, curEnv.addOpen(open), pendingLets)
      case Some(SA.Term.LetStmt(let: SA.Term.Let.Instance)) =>
        val ty = let.ty.map(elabType(_, curEnv))
        val value = elabTerm(let.value, curEnv)
        val (ref, nextEnv) = curEnv.bindRequired(let.name, let.span, allowShadow = true)
        loop(remaining.tail, nextEnv, pendingLets :+ CA.Let(ref, ty, value, let.span, isInstance = true))
      case Some(SA.Term.LetStmt(SA.Term.Let.Binding(SA.Term.BindingPattern.Bind(name, _), ty, value, span))) =>
        val checkedTy = ty.map(elabType(_, curEnv))
        val checkedValue = elabTerm(value, curEnv)
        val (ref, nextEnv) = curEnv.bindRequired(name, span, allowShadow = true)
        loop(remaining.tail, nextEnv, pendingLets :+ CA.Let(ref, checkedTy, checkedValue, span))
      case Some(SA.Term.LetStmt(SA.Term.Let.Binding(SA.Term.BindingPattern.Discard(span), ty, value, letSpan))) =>
        val checkedTy = ty.map(elabType(_, curEnv))
        val checkedValue = elabTerm(value, curEnv)
        val (ref, nextEnv) = curEnv.allocate("_")
        loop(remaining.tail, nextEnv, pendingLets :+ CA.Let(ref, checkedTy, checkedValue, letSpan))
      case Some(
            SA.Term.LetStmt(
              SA.Term.Let.Binding(pattern @ SA.Term.BindingPattern.Unpack(fields, patternSpan), ty, value, letSpan)
            )
          ) =>
        duplicatePatternName(pattern).foreach { case (name, duplicateSpan) =>
          throw InvalidDestructuring(s"duplicate name '$name' in one let pattern", Some(duplicateSpan))
        }
        // The RHS and its annotation are resolved before any names introduced by the pattern.
        val checkedTy = ty.map(elabType(_, curEnv))
        val checkedValue = elabTerm(value, curEnv)
        val (rootRef, envWithRoot) = curEnv.allocate("_")
        val (immediate, envWithFields) = allocateImmediatePatternFields(fields, envWithRoot)
        val (patternFields, patternEnv) = allocatePatternDescendants(immediate, envWithFields)
        val rest = loop(remaining.tail, patternEnv, Vector.empty)
        val nested = lowerNestedPatternMatches(patternFields, rest)
        val matchOne = CA.Term.MatchOne(
          CA.Term.LocalRef(rootRef, letSpan),
          None,
          patternFields.map(_.ref),
          nested,
          patternSpan,
          NodeId.fresh()
        )
        CA.Term.Body(
          pendingLets :+ CA.Let(rootRef, checkedTy, checkedValue, letSpan),
          matchOne,
          bodySpan
        )
    }

    loop(statements, initialEnv, Vector.empty)
  }

  private def elabTerm(term: SurfaceAst.Term, env: ResolveEnv): CA.Term = term match {
    case i: SA.Term.Ident =>
      elabPathTerm(identPath(i.name, i.span), env)
    case s: SA.Term.Select =>
      flattenTermPath(s) match {
        case Some(path) => elabPathTerm(path, env)
        case None       => CA.Term.Select(elabTerm(s.base, env), s.field, s.span)
      }
    case SA.Term.App(fn, args, sp)  => CA.Term.App(elabTerm(fn, env), args.map(elabTerm(_, env)), sp)
    case SA.Term.Derive(goal, sp)   => CA.Term.Derive(elabType(goal, env), sp)
    case pi: SA.Term.Pi             => elabPi(pi, env)
    case SA.Term.NatLit(number, sp) => CA.Term.NatLit(number, sp)
    case SA.Term.StrLit(text, sp)   => CA.Term.StrLit(text, sp)
    case l: SA.Term.Lam             => elabAnonymousLam(l, env)
    case b: SA.Term.Body =>
      elabBodyStatements(b.statements, b.out, env.enterOpenScope, b.span)
    case SA.Term.Match(scrut, motive, cases, wildcard, equation, sp) =>
      // The equation is bound in every case's scope after its fields, the wildcard's included, not in the scrutinee or
      // the motive.
      def withEquation(caseEnv: ResolveEnv): (Option[CA.LocalRef], ResolveEnv) =
        equation match {
          case Some(eq) =>
            val (ref, next) = caseEnv.bindRequired(eq.name, eq.span)
            (Some(ref), next)
          case None => (None, caseEnv)
        }
      CA.Term.Match(
        elabTerm(scrut, env),
        motive.map(elabType(_, env)),
        cases.map { c =>
          val caseEnv = env.enterLocalScope
          val (argRefs, fieldsEnv) =
            c.argNames.foldLeft((Vector.empty[Option[CA.LocalRef]], caseEnv)) { case ((curRefs, curEnv), argName) =>
              val (ref, nextEnv) = curEnv.bind(argName, c.span)
              (curRefs :+ ref, nextEnv)
            }
          val (equationRef, bodyEnv) = withEquation(fieldsEnv)
          val (ctorName, isFullyQualified) =
            if (c.useShortName) (c.ctorPath.head, false)
            else {
              val first = c.ctorPath.head
              if (env.hasLocal(first))
                throw LocalCaseHead(first, Some(c.span))
              (globalName(env.resolveGlobalBinding(c.ctorPath, c.span)), true)
            }
          CA.Case(ctorName, isFullyQualified, argRefs, elabTerm(c.body, bodyEnv), c.span, equationRef)
        },
        // A wildcard binds no field: the fields of the cases it stands for are anonymous.
        wildcard.map { w =>
          val (equationRef, bodyEnv) = withEquation(env.enterLocalScope)
          CA.Wildcard(elabTerm(w.body, bodyEnv), w.span, equationRef)
        },
        equation.map(_.span),
        sp,
        NodeId.fresh()
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
        val envWithSelf = env.addGlobal(name, c.header.nameSpan)
        val body = c.body match {
          case SA.ConstBody.Builtin(sp) =>
            if (c.decreases.nonEmpty)
              throw InvalidDecreaseSpec(
                "builtin definitions cannot have decreases annotations",
                Some(c.decreases.get.span)
              )
            CA.ConstBody.Builtin(sp)
          // Only a header with parameters makes a function definition, whose body is the function's. A header without
          // any, such as `def f : Nat -> Nat := Nat.succ`, declares a constant of its type, which may be a function.
          case SA.ConstBody.TermBody(term) =>
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
          CA.Decl.ConstDecl(nameText, header.ty, body, c.span, c.isInstance, c.lazyGlobal),
          envWithSelf
        )
      case c: SurfaceAst.Command.Decl.AxiomDecl =>
        val name = env.qualify(c.header.name)
        val nameText = globalName(name)
        val header = elabHeader(c.header.funcHeader, env)
        (
          CA.Decl.AxiomDecl(nameText, header.ty, c.span, c.isInstance),
          env.addGlobal(name, c.header.nameSpan)
        )
      case c: SurfaceAst.Command.Decl.InductiveDecl =>
        val name = env.qualify(c.header.name)
        val withHead = env.addGlobal(name, c.header.nameSpan)
        val (decl, ctorNames) = elabInductive(c, name, env, withHead)
        (decl, addConstructors(withHead, c, ctorNames))
    }

  /** `env` with the constructors of `c`, named `ctorNames` in its order, declared at their names. */
  private def addConstructors(
      env: ResolveEnv,
      c: SA.Command.Decl.InductiveDecl,
      ctorNames: Vector[GlobalName]
  ): ResolveEnv =
    c.ctors.zip(ctorNames).foldLeft(env) { case (cur, (ctor, ctorName)) => cur.addGlobal(ctorName, ctor.nameSpan) }

  /**
   * The family `c`, named `name`: its header resolved in `env`, and its constructors in `ctorEnv`, which also has the
   * family's head and, in a mutual block, its siblings' heads, but no constructor. Returns it with its constructors'
   * names.
   */
  private def elabInductive(
      c: SA.Command.Decl.InductiveDecl,
      name: GlobalName,
      env: ResolveEnv,
      ctorEnv: ResolveEnv
  ): (CA.Decl.InductiveDecl, Vector[GlobalName]) = {
    c.ctors.foreach { ctor =>
      checkConstructorParamDiscipline(c.header, ctor, globalName(name :+ ctor.name))
    }
    val headerEnv = env.enterLocalScope
    val (params, envWithParams) = elabBinders(c.header.params, headerEnv)
    val (indices, envWithIndices) = elabBinders(c.header.indices, envWithParams)
    val resultTy = elabType(c.header.resultTy, envWithIndices)
    val header = CA.InductiveHeader(globalName(name), params, indices, resultTy, c.span)

    val ctorNames = c.ctors.map(ctor => name :+ ctor.name)
    val ctors =
      c.ctors.zip(ctorNames).map { case (ctor, ctorName) =>
        val (erasedBinders, envWithErased) = elabBinders(ctor.erasedBinders, ctorEnv.enterLocalScope)
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
    (CA.Decl.InductiveDecl(header, ctors, c.span), ctorNames)
  }

  /**
   * A mutual block (docs/kernel.md, "Mutual blocks"): only inductive families, whose constructors see every family's
   * head, or only recursive definitions, whose bodies call every member through a slot of their own. Each name is
   * published once the whole block has checked.
   */
  private def elabMutual(mutual: SA.Command.Mutual, env: ResolveEnv): (CA.Decl, ResolveEnv) = {
    def invalid(reason: String, span: Span) = InvalidMutualBlock(reason, Some(span))
    val families = mutual.body.collect { case family: SA.Command.Decl.InductiveDecl => family }
    val definitions = mutual.body.collect { case definition: SA.Command.Decl.ConstDecl => definition }
    if (mutual.body.isEmpty) throw invalid("a mutual block declares at least one family or definition", mutual.span)
    if (families.length == mutual.body.length) {
      val names = families.map(family => env.qualify(family.header.name))
      val withHeads = families.zip(names).foldLeft(env) { case (cur, (family, name)) =>
        cur.addGlobal(name, family.header.nameSpan)
      }
      val elaborated = families.zip(names).map { case (family, name) => elabInductive(family, name, env, withHeads) }
      (
        CA.Decl.MutualInductives(elaborated.map(_._1), mutual.span),
        families.zip(elaborated).foldLeft(withHeads) { case (cur, (family, (_, ctorNames))) =>
          addConstructors(cur, family, ctorNames)
        }
      )
    } else if (definitions.length == mutual.body.length) {
      val names = definitions.map(definition => env.qualify(definition.header.name))
      val withNames = definitions.zip(names).foldLeft(env) { case (cur, (definition, name)) =>
        cur.addGlobal(name, definition.header.nameSpan)
      }
      val reserved = env.reserveRecursiveNames(definitions.map(_.header.name))
      val peers = definitions.map(_.header.name).zip(names)
      val members = definitions.zip(names).map { case (definition, name) =>
        if (definition.isInstance) throw invalid("a mutual definition is not an instance", definition.span)
        val decreases = definition.decreases.getOrElse {
          throw invalid("every mutual definition has a decreases annotation", definition.span)
        }
        val term = definition.body match {
          case SA.ConstBody.TermBody(term) => term
          case SA.ConstBody.Builtin(sp)    => throw invalid("a mutual definition is not a builtin", sp)
        }
        val header = elabHeader(definition.header.funcHeader, reserved)
        header.ty match {
          case pi: CA.Term.Pi =>
            val (peerRefs, bodyEnv) = header.bodyEnv.bindRecursivePeers(peers)
            val lam = elabLam(pi, bodyEnv, term, Some(globalName(name)), None, definition.span, withNames)
            CA.MutualDef(globalName(name), lam, elabDecreaseSpec(decreases, header.bodyEnv), peerRefs, definition.span)
          case _ => throw InvalidDecreaseSpec("decreases requires a function definition", Some(decreases.span))
        }
      }
      (CA.Decl.MutualDefs(members, mutual.span), withNames)
    } else throw invalid("a mutual block declares only inductive families or only definitions", mutual.span)
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
        val (nextDecl, nextEnv) = elabMutual(mutual, curEnv)
        decls += nextDecl
        curEnv = nextEnv
    }
    (decls.result(), curEnv)
  }

  private lazy val (elaboratedKernel, elaboratedProtocol, kernelRoot) = {
    val (decls, env) = elabCommands(expandStructSelectors(Kernel.surface.decls), ResolveEnv.primitive)
    val (protocolDecls, protocolEnv) = elabCommands(expandStructSelectors(Kernel.protocolSurface.decls), env)
    (decls, protocolDecls, protocolEnv.root)
  }

  private[raccoonlang] def kernelDecls: Vector[CA.Decl] = elaboratedKernel

  /** The kernel's protocol declarations, which `Kernel.env` evaluates over the core declarations. */
  private[raccoonlang] def kernelProtocolDecls: Vector[CA.Decl] = elaboratedProtocol

  private def preludeEnv(prelude: Prelude.Config): ResolveEnv = {
    val (_, env) = elabCommands(expandStructSelectors(prelude.surface.decls), ResolveEnv.kernel)
    ResolveEnv.kernel.copy(root = env.root)
  }

  private[raccoonlang] def elabWithoutPrelude(p: SA.Program): CA.Program =
    elabProgram(p, ResolveEnv.kernel)

  def elab(p: SA.Program): CA.Program =
    elab(p, Prelude.default)

  def elab(p: SA.Program, prelude: Prelude.Config): CA.Program =
    elabProgram(p, preludeEnv(prelude))

  private def elabProgram(p: SA.Program, startEnv: ResolveEnv): CA.Program = {
    p.imports.headOption.foreach { imp =>
      throw UnsupportedImport(imp.path.mkString("."), Some(imp.span))
    }

    val (decls, env) = elabCommands(expandStructSelectors(p.decls), startEnv)
    CA.Program(decls, p.body.map(elabTerm(_, env)))
  }
}
