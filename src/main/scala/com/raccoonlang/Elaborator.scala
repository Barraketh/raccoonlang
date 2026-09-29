package com.raccoonlang

import scala.annotation.tailrec

object Elaborator {
  val SA = SurfaceAst
  val CA = CoreAst

  private type GlobalName = Vector[String]

  private val RootName = "_root_"

  private def globalName(parts: GlobalName): String = parts.mkString(".")

  /** A form's qualified name. The kernel owns these names, and the elaborator lowers them to `FormOp`s. */
  private def formPath(form: CA.Form): GlobalName = Vector(form.parameter.name, form.name)

  private val Forms: Map[String, CA.Form] = CA.Form.all.map(form => form.qualifiedName -> form).toMap

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
          case Some(_) => fail(AlreadyDefined(globalName(fullName)))
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
   * `scopes` are the locals. `fieldForms` are the forms of the sort or closure field being elaborated, by short name.
   * `recursiveAliases` are the members of the recursive group whose bodies are being elaborated, by full name: a
   * definition's own name and its peers' are not locals (spec §1), but in the group's bodies they denote local refs.
   * Global names and namespace objects live in `root`. Open scopes are snapshots of resolved objects, so later
   * declarations do not affect an earlier `open`. `elabPath` states the order in which these are consulted.
   */
  private final case class ResolveEnv(
      scopes: List[Map[String, CA.LocalRef]],
      nextLocal: Int,
      root: NameNode,
      namespace: GlobalName,
      opens: List[OpenScope],
      reservedLocals: Set[String],
      recursiveAliases: Map[GlobalName, CA.LocalRef],
      fieldForms: Map[String, CA.Form]
  ) {
    def enterLocalScope: ResolveEnv = copy(scopes = Map.empty[String, CA.LocalRef] :: scopes)

    def enterOpenScope: ResolveEnv = copy(opens = Map.empty[String, ResolvedObject] :: opens)

    def exitScoped(inner: ResolveEnv): ResolveEnv = copy(root = inner.root)

    /** The scope of a sort or closure field of `parameter`: that parameter's forms resolve unqualified. */
    def openForms(parameter: CA.Parameter): ResolveEnv =
      copy(fieldForms = parameter.forms.map(form => form.name -> form).toMap)

    private def rootObject(parts: GlobalName): Option[ResolvedObject] =
      root.lookup(parts).map(ResolvedObject(parts, _))

    private def scopedObject(parts: GlobalName): Option[ResolvedObject] =
      namespace.inits
        .map(prefix => prefix ++ parts)
        .collectFirst(Function.unlift(rootObject))

    def local(name: String): Option[CA.LocalRef] =
      scopes.collectFirst(Function.unlift(_.get(name)))

    /** A member of the recursive group, by its short name or a qualified one, found as its global name would be. */
    def recursiveMember(path: SurfacePath): Option[CA.LocalRef] =
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
        at(path.span) { fail(NotFound(path.parts.headOption.getOrElse(RootName))) }
      }
      if (tail.isEmpty) {
        obj.node.binding match {
          case Some(name) => globalRef(name)
          case None       => at(path.span) { fail(NotFound(globalName(obj.path))) }
        }
      } else {
        obj.node.binding match {
          case Some(name) => selectTail(globalRef(name), tail)
          case None       => at(path.span) { fail(NotFound(globalName(obj.path :+ tail.head))) }
        }
      }
    }

    def resolveGlobalBinding(parts: GlobalName, span: Span): GlobalName = {
      val (obj, tail) = resolveObjectPrefix(SurfacePath(root = false, parts, span)).getOrElse {
        at(span) { fail(NotFound(parts.headOption.getOrElse(RootName))) }
      }
      if (tail.nonEmpty)
        at(span) { fail(NotFound(globalName(obj.path :+ tail.head))) }
      obj.node.binding match {
        case Some(name) => name
        case None       => at(span) { fail(NotFound(globalName(obj.path))) }
      }
    }

    /** Snapshot an open into the current open scope and reject alias conflicts immediately. */
    def addOpen(open: SA.Command.Open): ResolveEnv = {
      def openName: String =
        if (open.root) (RootName +: open.namespace).mkString(".") else globalName(open.namespace)

      val namespace =
        resolveObjectPrefix(SurfacePath(open.root, open.namespace, open.span))
          .collect { case (obj, tail) if tail.isEmpty && obj.node.children.nonEmpty => obj }
          .getOrElse(at(open.span) { fail(NotFound(openName)) })

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
              at(open.span) { fail(NotFound(globalName(namespace.path :+ name))) }
          }
        case SA.Command.AliasRule.Wildcard | SA.Command.AliasRule.Exclude(_) =>
      }

      val nextOpenScope =
        aliases.result().foldLeft(opens.head) { case (scope, (alias, obj)) =>
          scope.get(alias) match {
            case Some(existing) if existing.path == obj.path =>
              scope + (alias -> obj)
            case Some(existing) =>
              at(open.span) { fail(AmbiguousName(alias, Vector(globalName(existing.path), globalName(obj.path)))) }
            case None =>
              scope + (alias -> obj)
          }
        }
      copy(opens = nextOpenScope :: opens.tail)
    }

    def addGlobal(name: GlobalName): ResolveEnv =
      copy(root = root.insertGlobal(name, name))

    def qualify(name: String): GlobalName = namespace :+ name

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
     * Bind every member of a recursive group to the local ref its name denotes in the group's bodies. The names are
     * reserved beforehand, so no parameter or let takes one.
     */
    def bindRecursivePeers(peers: Vector[(String, GlobalName)]): (Vector[CA.LocalRef], ResolveEnv) = {
      peers.foldLeft((Vector.empty[CA.LocalRef], this)) { case ((refs, cur), (name, fullName)) =>
        if (!cur.reservedLocals.contains(name)) wtf(s"$name is not reserved for recursive peer binding")
        if (cur.recursiveAliases.contains(fullName)) fail(AlreadyDefined(name))
        val (ref, next) = cur.allocate(name)
        (refs :+ ref, next.copy(recursiveAliases = next.recursiveAliases + (fullName -> ref)))
      }
    }

    /** `_` binds an anonymous local (spec §1): it has a ref, as every local does, but no name resolves to it. */
    def bind(name: String, allowShadow: Boolean): (CA.LocalRef, ResolveEnv) =
      if (name == "_") allocate(name)
      else if (reservedLocals.contains(name)) fail(AlreadyDefined(name))
      else if (!allowShadow && scopes.head.contains(name)) fail(AlreadyDefined(name))
      else {
        val (ref, nextEnv) = allocate(name)
        (ref, nextEnv.copy(scopes = (scopes.head + (name -> ref)) :: scopes.tail))
      }
  }

  private object ResolveEnv {
    private val BuiltinGlobals: Set[GlobalName] =
      CA.Parameter.all.map(parameter => Vector(parameter.name)).toSet ++ CA.Form.all.map(formPath)

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
        Map.empty,
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

    // The selector's parameter must not capture a name its header or result type mentions.
    val binders = header.binders ++ ctor.binders
    val usedNames =
      binders.map(_.name).toSet ++ binders.flatMap(binder => freeIdentifiers(binder.ty, Set.empty).map(_.name)) +
        header.name
    val selfName = (Iterator.single("self") ++ Iterator.from(1).map(suffix => s"self$suffix")).find(!usedNames(_)).get
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
        // The result type is the field's own type, as written, with each earlier field it mentions bound to that
        // field's selector applied to `self`. The selector is spelled qualified so it resolves whether or not the
        // namespace is open. Only a mentioned field is bound: an unmentioned one would put `self` in the type for
        // nothing, which a linear struct cannot have (spec §3.5). Each binding stands at the field's first mention,
        // where an error about it belongs. The type keeps the field type's spans, so an error in it is located where
        // the field's type is written. It is elaborated twice, as the header's codomain and as the match's motive, and
        // so is two nodes, each with an identity of its own (docs/kernel.md#value-identity).
        val mentions = freeIdentifiers(field.ty, Set.empty)
        val earlierFields = storedBinders.take(fieldIdx).filter(_.name != "_")
        val bindings = earlierFields.flatMap { earlier =>
          mentions.find(_.name == earlier.name).map { mention =>
            val span = mention.span
            val selected = SA.Term.App(
              SA.Term.Select(SA.Term.Ident(header.name, span), earlier.name, span),
              Vector(SA.Term.Ident(selfName, span)),
              span
            )
            SA.Term.LetStmt(SA.Term.Let(earlier.name, None, selected, span))
          }
        }
        val resultTy = if (bindings.isEmpty) field.ty else SA.Term.Body(bindings, field.ty, field.ty.span)
        val selectorHeader =
          SA.Command.DeclHeader(
            field.name,
            SA.FuncHeader(implicitFamilyBinders :+ selfBinder, resultTy, field.span),
            field.span
          )
        // The selector is an ordinary match on `self` binding every stored field, each where its binder is written, and
        // returning the selected one, at the selector's declared result type.
        val patternVars = storedBinders.map(binder => SA.Term.PatternVar(binder.name, binder.span))
        val body = SA.Term.Match(
          SA.Term.Ident(selfName, selfSpan),
          motive = resultTy,
          Vector(
            SA.Term.Case(
              Vector(ctor.name),
              useShortName = true,
              patternVars,
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
          selectorOf = Some(decl),
          field.span
        )
      }

    Some(SA.Command.Namespace(Vector(header.name), selectors, header.span))
  }

  /**
   * The identifiers a term leaves free, at any depth and in source order: those no binder inside it binds, `bound`
   * naming the ones already bound around it.
   */
  private def freeIdentifiers(term: SA.Term, bound: Set[String]): Vector[SA.Term.Ident] = {
    def free(part: SA.Term): Vector[SA.Term.Ident] = freeIdentifiers(part, bound)
    def closure(written: SA.Closure): Vector[SA.Term.Ident] = (written.kind.toVector ++ written.scope).flatMap(free)
    // Binders in one group scope left to right: each one's type sees the names bound before it.
    def group(binders: Vector[SA.Binder]): (Vector[SA.Term.Ident], Set[String]) =
      binders.foldLeft((Vector.empty[SA.Term.Ident], bound)) { case ((found, inner), binder) =>
        (found ++ freeIdentifiers(binder.ty, inner), inner + binder.name)
      }
    term match {
      case ident: SA.Term.Ident                  => if (bound(ident.name)) Vector.empty else Vector(ident)
      case _: SA.Term.NatLit | _: SA.Term.StrLit => Vector.empty
      case SA.Term.Select(base, _, _)            => free(base)
      case SA.Term.App(fn, args, _)              => (fn +: args).flatMap(free)
      case SA.Term.Sort(level, kind, scope, _) =>
        val written = level match {
          case SA.Term.SortLevel.Written(written)             => Vector(written)
          case SA.Term.SortLevel.Zero | SA.Term.SortLevel.One => Vector.empty
        }
        (written ++ kind ++ scope).flatMap(free)
      case SA.Term.Pi(written, binders, body, _) =>
        val (inBinders, inner) = group(binders)
        closure(written) ++ inBinders ++ freeIdentifiers(body, inner)
      case SA.Term.Lam(written, header, body, _) =>
        val (inBinders, inner) = group(header.params)
        closure(written) ++ inBinders ++ freeIdentifiers(header.ty, inner) ++ freeIdentifiers(body, inner)
      case SA.Term.Scope(name, body, _) => freeIdentifiers(body, bound + name)
      case SA.Term.Match(scrut, motive, cases, _) =>
        free(scrut) ++ free(motive) ++ cases.flatMap(c => freeIdentifiers(c.body, bound ++ c.patternVars.map(_.name)))
      case SA.Term.Body(statements, out, _) =>
        // Lets scope left to right, each one's own value outside it; an open binds no local.
        val (inLets, inner) =
          statements.foldLeft((Vector.empty[SA.Term.Ident], bound)) {
            case ((found, inner), SA.Term.LetStmt(let)) =>
              (found ++ (let.ty.toVector :+ let.value).flatMap(freeIdentifiers(_, inner)), inner + let.name)
            case (acc, _: SA.Term.OpenStmt) => acc
          }
        inLets ++ freeIdentifiers(out, inner)
    }
  }

  /**
   * Elaborate a dotted path. This is the one order in which a name resolves (spec §1):
   *   1. a local, the rest of the path being a projection chain;
   *   2. in a sort or closure field, one of the field's forms, as its qualified name does;
   *   3. a member of the recursive group being elaborated, by its short or qualified name. It is not a local, so a
   *      field's forms win over it: `level = succ(u)` means `Level.succ(u)` even in the body of a recursive `def succ`;
   *   4. a global, through the current namespace and then the open scopes.
   * A rooted path skips the first two.
   */
  private def elabPath[A](path: SurfacePath, env: ResolveEnv)(
      local: (CA.LocalRef, Span) => A,
      global: (String, Span) => A,
      select: (A, String, Span) => A
  ): A = {
    def selectTail(base: A): A =
      path.parts.tail.foldLeft(base) { case (cur, field) => select(cur, field, path.span) }

    val first = if (path.root) None else path.parts.headOption
    first
      .flatMap(env.local)
      .map(ref => selectTail(local(ref, path.span)))
      .orElse(first.flatMap(env.fieldForms.get).map(form => selectTail(global(form.qualifiedName, path.span))))
      .orElse(env.recursiveMember(path).map(local(_, path.span)))
      .getOrElse(env.resolvePath(path)(global, select))
  }

  /** A path as an application head: a form, or an ordinary term. */
  private def elabPathHead(path: SurfacePath, env: ResolveEnv): Either[CA.Form, CA.Term] =
    elabPath[Either[CA.Form, CA.Term]](path, env)(
      (ref, span) => Right(CA.Term.LocalRef(ref, span)),
      (name, span) => Forms.get(name).toLeft(CA.Term.GlobalRef(name, span)),
      (base, field, span) => Right(CA.Term.Select(unapplied(base, span), field, span))
    )

  /**
   * A head that is not applied. A nullary form is complete as written; any other form exists only applied to all of its
   * arguments (spec §2.2), so naming it without them is applying it to none.
   */
  private def unapplied(head: Either[CA.Form, CA.Term], span: Span): CA.Term =
    head match {
      case Right(term)                   => term
      case Left(form) if form.arity == 0 => CA.Term.FormOp(form, Vector.empty, span)
      case Left(form)                    => at(span) { fail(ArityMismatch(form.arity, 0)) }
    }

  private def elabPathTerm(path: SurfacePath, env: ResolveEnv): CA.Term =
    unapplied(elabPathHead(path, env), path.span)

  /**
   * A surface Pi's binders are already exactly its group — the parser decided the grouping — so a Pi body is NOT merged
   * into the enclosing group. `(a: A) -> ((b: B) -> C)` stays a 1-ary Pi returning a Pi, which is a different type from
   * the 2-ary `(a: A) -> (b: B) -> C`.
   */
  private def elabPi(pi: SA.Term.Pi, env: ResolveEnv): CA.Term.Pi = {
    val piEnv = env.enterLocalScope
    val (binders, binderEnv) = elabBinders(pi.binders, CA.BinderSite.Function, piEnv)
    val body = elabTerm(pi.body, binderEnv)
    // A function type captures nothing, so an omitted closure field is Kind.unr or Lifetime.empty (spec §1).
    val omitted = CA.Closure.unrestricted(pi.span)
    CA.Term.Pi(
      binders,
      body,
      CA.Closure(
        pi.closure.kind.map(elabField(_, CA.Parameter.Kind, env)).fold(omitted.kind)(CA.ClosureField.Written),
        pi.closure.scope.map(elabField(_, CA.Parameter.Lifetime, env)).fold(omitted.scope)(CA.ClosureField.Written)
      ),
      pi.span,
      NodeId.fresh()
    )
  }

  /**
   * A sort's or closure's written field, elaborated with its parameter's forms open (spec §1). What an omitted field is
   * depends on what omits it, so each caller supplies that.
   */
  private def elabField(written: SA.Term, parameter: CA.Parameter, env: ResolveEnv): CA.Term =
    elabTerm(written, env.openForms(parameter))

  private def elabBinder(b: SA.Binder, site: CA.BinderSite, env: ResolveEnv): (CA.Binder, ResolveEnv) = {
    val ty = elabTerm(b.ty, env)
    val (ref, nextEnv) = env.bind(b.name, allowShadow = false)
    (CA.Binder(ref, ty, b.span, site, b.isImplicit), nextEnv)
  }

  private def elabBinders(
      binders: Vector[SA.Binder],
      site: CA.BinderSite,
      env: ResolveEnv
  ): (Vector[CA.Binder], ResolveEnv) =
    binders.foldLeft((Vector.empty[CA.Binder], env)) { case ((curBinders, curEnv), binder) =>
      val (nextBinder, nextEnv) = elabBinder(binder, site, curEnv)
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

  /**
   * A declaration's header binds `Parameter` s and its type's closure is unrestricted, since a declaration captures
   * nothing (spec §3.3); a lambda's header binds `Function` binders at the lambda's closure.
   */
  private def elabHeader(
      header: SA.FuncHeader,
      site: CA.BinderSite,
      closure: CA.Closure,
      env: ResolveEnv
  ): HeaderResult = {
    val headerEnv = env.enterLocalScope
    val (params, bodyEnv) = elabBinders(header.params, site, headerEnv)
    val outTy = elabTerm(header.ty, bodyEnv)
    val ty =
      if (params.isEmpty) outTy
      else CA.Term.Pi(params, outTy, closure, header.span, NodeId.fresh())
    HeaderResult(ty, bodyEnv)
  }

  private def elabDeclHeader(header: SA.FuncHeader, env: ResolveEnv): HeaderResult =
    elabHeader(header, CA.BinderSite.Parameter, CA.Closure.unrestricted(header.span), env)

  def getType(header: SA.FuncHeader): CA.Term = elabDeclHeader(header, ResolveEnv.empty).ty

  private def elabLam(
      pi: CA.Term.Pi,
      bodyEnv: ResolveEnv,
      body: SA.Term,
      name: Option[String],
      recursion: Option[CA.Recursion],
      span: Span
  ): CA.Term.Lam = {
    CA.Term.Lam(pi, elabTerm(body, bodyEnv), span, NodeId.fresh(), name, recursion)
  }

  private def elabDecreaseRef(name: String, span: Span, env: ResolveEnv): CA.LocalRef =
    elabTerm(SA.Term.Ident(name, span), env) match {
      case CA.Term.LocalRef(ref, _) => ref
      case _ =>
        at(span) { fail(InvalidDecreaseSpec(s"$name is not a function parameter")) }
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
    case SA.Term.App(fn, args, sp) =>
      val head = flattenTermPath(fn) match {
        case Some(path) => elabPathHead(path, env)
        case None       => Right(elabTerm(fn, env))
      }
      head match {
        case Left(form) if form.arity > 0 =>
          if (args.length != form.arity) at(sp) { fail(ArityMismatch(form.arity, args.length)) }
          CA.Term.FormOp(form, args.map(elabTerm(_, env)), sp)
        case _ => CA.Term.App(unapplied(head, fn.span), args.map(elabTerm(_, env)), sp)
      }
    case SA.Term.Sort(level, kind, scope, sp) =>
      // `Type` and `Prop` fix the level, and an omitted kind or scope is Kind.unr or Lifetime.empty (spec §1).
      def fixed(form: CA.Form): CA.Term = CA.Term.FormOp(form, Vector.empty, sp)
      val levelTerm = level match {
        case SA.Term.SortLevel.Zero          => fixed(CA.Form.LevelZero)
        case SA.Term.SortLevel.One           => fixed(CA.Form.LevelOne)
        case SA.Term.SortLevel.Written(term) => elabField(term, CA.Parameter.Level, env)
      }
      CA.Term.Sort(
        levelTerm,
        kind.fold(fixed(CA.Form.KindUnr))(elabField(_, CA.Parameter.Kind, env)),
        scope.fold(fixed(CA.Form.LifetimeEmpty))(elabField(_, CA.Parameter.Lifetime, env)),
        sp
      )
    case pi: SA.Term.Pi => elabPi(pi, env)
    case l: SA.Term.Lam =>
      // A lambda's omitted closure field is derived from its captures by the checker (spec §4.3).
      val closure = CA.Closure(
        l.closure.kind
          .map(elabField(_, CA.Parameter.Kind, env))
          .fold[CA.ClosureField](CA.ClosureField.Omitted)(CA.ClosureField.Written),
        l.closure.scope
          .map(elabField(_, CA.Parameter.Lifetime, env))
          .fold[CA.ClosureField](CA.ClosureField.Omitted)(CA.ClosureField.Written)
      )
      val header = elabHeader(l.header, CA.BinderSite.Function, closure, env)
      header.ty match {
        case pi: CA.Term.Pi =>
          elabLam(pi, header.bodyEnv, l.body, None, None, l.span)
        case _ => at(l.span) { wtf("Lambda header must produce a function type") }
      }
    case SA.Term.Scope(name, body, span) =>
      val (ref, bodyEnv) = env.enterLocalScope.bind(name, allowShadow = false)
      CA.Term.Scope(ref, elabTerm(body, bodyEnv), span, NodeId.fresh())
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
            val (ref, nextEnv) = curEnv.bind(l.name, allowShadow = true)
            checkedLets += CA.Let(ref, ty, value, l.span)
            nextEnv
        }
      }
      CA.Term.Body(checkedLets.result(), elabTerm(b.out, bodyEnv), b.span)
    case SA.Term.Match(scrut, motive, cases, sp) =>
      CA.Term.Match(
        elabTerm(scrut, env),
        elabTerm(motive, env),
        cases.map { c =>
          val caseEnv = env.enterLocalScope
          val (patternVars, bodyEnv) =
            c.patternVars.foldLeft((Vector.empty[CA.PatternVar], caseEnv)) { case ((curVars, curEnv), patternVar) =>
              val (ref, nextEnv) = curEnv.bind(patternVar.name, allowShadow = false)
              (curVars :+ CA.PatternVar(ref, patternVar.span), nextEnv)
            }
          val (ctorName, isFullyQualified) =
            if (c.useShortName) (c.ctorPath.head, false)
            else {
              val first = c.ctorPath.head
              if (env.local(first).nonEmpty)
                at(c.span) { fail(LocalCaseHead(first)) }
              (globalName(env.resolveGlobalBinding(c.ctorPath, c.span)), true)
            }
          CA.Case(ctorName, isFullyQualified, patternVars, elabTerm(c.body, bodyEnv), c.span)
        },
        sp,
        NodeId.fresh()
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
        at(defn.span) { fail(InvalidRecursiveGroup("mutual definitions cannot be opaque")) }
      defn.body match {
        case SA.ConstBody.TermBody(_) =>
        case SA.ConstBody.Builtin(_) =>
          at(defn.span) { fail(InvalidRecursiveGroup("mutual definitions cannot have builtin bodies")) }
      }
      val decrease = defn.decreases.getOrElse {
        at(defn.span) { fail(InvalidDecreaseSpec("every mutual definition requires a decreases annotation")) }
      }
      val header = elabDeclHeader(defn.header.funcHeader, allocator)
      allocator = allocator.copy(nextLocal = header.bodyEnv.nextLocal)
      header.ty match {
        case pi: CA.Term.Pi => PreparedRecursiveDefinition(defn, name, header, pi, decrease)
        case _ =>
          at(defn.span) { fail(InvalidDecreaseSpec("decreases requires a function definition")) }
      }
    }

    val peerInfo = headers.map(definition => definition.surface.header.name -> definition.name)
    val (peerRefs, peerEnv) = allocator.bindRecursivePeers(peerInfo)

    val definitions = headers.zip(peerRefs).map { case (definition, ownPeerRef) =>
      val bodyEnv = definition.header.bodyEnv
      val bodyBase = bodyEnv.copy(nextLocal = peerEnv.nextLocal, recursiveAliases = peerEnv.recursiveAliases)
      val decrease = elabDecreaseSpec(definition.decrease, bodyEnv)
      val body = definition.surface.body match {
        case SA.ConstBody.TermBody(term) => elabTerm(term, bodyBase)
        case SA.ConstBody.Builtin(_) =>
          at(definition.surface.span) { wtf("builtin body reached mutual elaboration") }
      }
      CA.RecursiveDef(
        globalName(definition.name),
        ownPeerRef,
        definition.pi,
        body,
        decrease,
        definition.surface.span,
        NodeId.fresh()
      )
    }
    (CA.Decl.RecursiveDefBlock(definitions, span), groupEnv)
  }

  /**
   * The seal of the family that `family` declares under the global name `name`, if it is `sealed`. Its constructors and
   * its generated selectors both take their seal from here, so they are kept to one module: the source the declaration
   * was read from. Every parsed program has a source (LanguageParser.parseProgram), so a sealed declaration without one
   * was read from no file and cannot be kept to it; that is a broken invariant, not a program's error.
   */
  private def familySeal(family: SA.Command.Decl.InductiveDecl, name: String): Option[Sealing.Seal] =
    Option.when(family.isSealed) {
      Sealing.Seal(name, family.span.source.getOrElse(wtf(s"Sealed family $name has no source")))
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
      val (params, envWithParams) = elabBinders(family.header.params, CA.BinderSite.Parameter, headerEnv)
      val (indices, envWithIndices) = elabBinders(family.header.indices, CA.BinderSite.Field, envWithParams)
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
        val (binders, envWithBinders) = elabBinders(constructor.binders, CA.BinderSite.Field, constructorEnv)
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
        CA.Decl.InductiveDecl(
          family.header,
          constructors,
          familySeal(family.surface, family.header.name),
          family.surface.span
        ),
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
      at(mutual.span) { fail(InvalidRecursiveGroup("the group must not be empty")) }

    val definitions = mutual.body.collect { case definition: SA.Command.Decl.ConstDecl => definition }
    val families = mutual.body.collect { case family: SA.Command.Decl.InductiveDecl => family }
    if (definitions.length == mutual.body.length)
      elabMutualDefs(definitions, env, mutual.span)
    else if (families.length == mutual.body.length)
      elabMutualInductives(families, env, mutual.span)
    else
      at(mutual.span) {
        fail(InvalidRecursiveGroup("a mutual group must contain only definitions or only inductive declarations"))
      }
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
        val header = elabDeclHeader(c.header.funcHeader, headerEnv)
        val envWithSelf = env.addGlobal(name)
        val body = c.body match {
          case SA.ConstBody.Builtin(sp) =>
            if (c.decreases.nonEmpty)
              at(c.decreases.get.span) {
                fail(InvalidDecreaseSpec("builtin definitions cannot have decreases annotations"))
              }
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
                  at(c.decreases.get.span) { fail(InvalidDecreaseSpec("decreases requires a function definition")) }
                CA.ConstBody.TermBody(elabTerm(term, envWithSelf))
            }
        }
        // A selector is declared in its family's namespace, so that namespace names its family.
        val sealedBy = c.selectorOf.flatMap(family => familySeal(family, globalName(env.namespace)))
        (
          CA.Decl.ConstDecl(c.isOpaque, nameText, header.ty, body, sealedBy, c.span),
          envWithSelf
        )
      case c: SurfaceAst.Command.Decl.AxiomDecl =>
        val name = env.qualify(c.header.name)
        val nameText = globalName(name)
        val header = elabDeclHeader(c.header.funcHeader, env)
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
      at(imp.span) { fail(UnsupportedImport(imp.path.mkString("."))) }
    }

    val (decls, env) = elabCommands(expandStructSelectors(p.decls), startEnv)
    CA.Program(decls, p.body.map(elabTerm(_, env)))
  }
}
