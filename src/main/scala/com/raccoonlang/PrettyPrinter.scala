package com.raccoonlang

object PrettyPrinter {
  private def printString(scalars: Vector[Int]): String = UnicodeScalarString.renderQuoted(scalars)

  /**
   * Implicit arguments are never written in source, so a saturated call prints only its explicit ones. Anything that is
   * not a plain saturated call keeps every argument.
   */
  private def explicitArgs(head: Value, args: Seq[Value]): Seq[Value] =
    head.tpe match {
      case pi: Value.VPi if pi.binders.length == args.length =>
        args.zip(pi.binders).collect { case (arg, binder) if !binder.isImplicit => arg }
      case _ => args
    }

  private def printApp(head: Value, args: Seq[Value]): String = {
    val headStr = head match {
      case _: Value.VApp | _: Value.VConst | _: Value.Var | _: Value.VSort => print(head)
      // A named lambda prints as its name, such as a native operation heading its neutral application.
      case Value.VLam(_, _: Value.ValueId.Const, _) => print(head)
      case _                                        => s"(${print(head)})"
    }
    val argsStr = explicitArgs(head, args).map(print).mkString(", ")
    s"$headStr($argsStr)"
  }

  /** A value that prints as loose syntax, so it is parenthesized where an atom is expected. */
  private def isLoose(value: Value): Boolean =
    value match {
      case _: Value.VPi                               => true
      case Value.VLam(_, _: Value.ValueId.LocalId, _) => true
      case thunk: Value.NeutralThunk                  => printedCall(thunk).isEmpty
      case _                                          => false
    }

  private def isForm(term: CoreAst.Term, form: CoreAst.Form): Boolean =
    term match {
      case CoreAst.Term.FormOp(`form`, _, _) => true
      case _                                 => false
    }

  /** A sort as its former and the fields it spells out; a field left at its former's value is not printed. */
  private def printSort(former: String, level: Option[String], kind: Option[String], scope: Option[String]): String = {
    val fields = fieldList(
      level.map(l => s"level = $l").toVector ++ kind.map(k => s"kind = $k") ++ scope.map(l => s"scope = $l")
    )
    if (fields.isEmpty) former else s"$former $fields"
  }

  /**
   * A closure prefix: the fields that are not `Kind.unr` or `Lifetime.empty`, with a trailing space, or nothing. A
   * lambda's derived field prints as the expression the checker derived, once it has.
   */
  private def printClosure(kind: Option[String], scope: Option[String]): String = {
    val fields = fieldList(kind.map(k => s"kind = $k").toVector ++ scope.map(l => s"scope = $l"))
    if (fields.isEmpty) "" else s"$fields "
  }

  private def fieldList(fields: Vector[String]): String = if (fields.isEmpty) "" else s"{ ${fields.mkString(", ")} }"

  /**
   * Core syntax as source, under the values its free locals are bound to: a bound local prints as its value, and any
   * other by its binder's name. A value holding syntax (a function type's binders, a stuck match) prints under its own
   * environment, so a generated name such as a selector's parameter never shows for the argument it stands for.
   */
  private final class SyntaxPrinter(bound: CoreAst.LocalRef => Option[Value]) {
    private def printRef(ref: CoreAst.Term.Ref): String = ref match {
      case CoreAst.Term.GlobalRef(name, _) => name
      case CoreAst.Term.LocalRef(ref, _)   => bound(ref).fold(ref.name)(print)
    }

    def printDecreaseSpec(spec: CoreAst.DecreaseSpec): String =
      spec match {
        case CoreAst.DecreaseSpec.Lexicographic(args, _) =>
          s"decreases lexicographic(${args.map(_.name).mkString(", ")})"
        case CoreAst.DecreaseSpec.Measure(term, _) =>
          s"decreases measure(${printCoreTerm(term)})"
      }

    def printBinder(b: CoreAst.Binder): String = {
      val body = s"${b.name}: ${printCoreTerm(b.ty)}"
      if (b.isImplicit) s"{$body}" else s"($body)"
    }

    def printPiBinder(b: CoreAst.Binder): String =
      if (b.name == "_" && !b.isImplicit) printTermAtom(b.ty)
      else printBinder(b)

    def printBinders(binders: Vector[CoreAst.Binder]): String =
      binders.map(printBinder).mkString(" ")

    private def printLet(l: CoreAst.Let): String = {
      val tyStr = l.ty.map(t => s": ${printCoreTerm(t)}").getOrElse("")
      s"let ${l.name}$tyStr := ${printCoreTerm(l.value)}"
    }

    private def printBody(b: CoreAst.Term.Body): String = {
      if (b.lets.isEmpty) printCoreTerm(b.res)
      else {
        val letsStr = b.lets.map(printLet).mkString("\n")
        s"{ $letsStr \n ${printCoreTerm(b.res)} }"
      }
    }

    /**
     * A term in a position where an operator would bind tighter than the term prints: atoms and already-delimited forms
     * render as themselves, and the forms that print as loose infix-ish syntax get parenthesized.
     */
    private def printTermAtom(t: CoreAst.Term): String = t match {
      // A bound local stands for its value, which may itself print as loose syntax.
      case CoreAst.Term.LocalRef(ref, _) if bound(ref).exists(isLoose) => s"(${printCoreTerm(t)})"
      case _: CoreAst.Term.NatLit | _: CoreAst.Term.StrLit | _: CoreAst.Term.Ref | _: CoreAst.Term.App |
          _: CoreAst.Term.Select | _: CoreAst.Term.Sort | _: CoreAst.Term.FormOp =>
        printCoreTerm(t)
      case _: CoreAst.Term.Lam | _: CoreAst.Term.Scope | _: CoreAst.Term.Match | _: CoreAst.Term.Body |
          _: CoreAst.Term.Pi =>
        s"(${printCoreTerm(t)})"
    }

    /**
     * A function type's codomain, parenthesized when it is a function type itself, as the value printer's
     * `PrettyPrinter.printCodomain` says why; a local bound to a value prints as that value does there.
     */
    private def printCodomain(out: CoreAst.Term): String = out match {
      case _: CoreAst.Term.Pi            => s"(${printCoreTerm(out)})"
      case CoreAst.Term.LocalRef(ref, _) => bound(ref).fold(ref.name)(PrettyPrinter.printCodomain)
      case _                             => printCoreTerm(out)
    }

    def printCoreTerm(t: CoreAst.Term): String = t match {
      case CoreAst.Term.NatLit(value, _)   => value.toString
      case CoreAst.Term.StrLit(scalars, _) => printString(scalars)
      case ref: CoreAst.Term.Ref           => printRef(ref)
      case CoreAst.Term.Lam(ty, body, _, _, _, recursion, _) =>
        val decreaseStr = recursion.map(r => s" ${printDecreaseSpec(r.decreases)}").getOrElse("")
        s"fun ${printCoreClosure(ty.closure)}${printBinders(ty.binders)}: ${printCoreTerm(ty.out)}$decreaseStr => " +
          printCoreTerm(body)
      case CoreAst.Term.Scope(ref, body, _, _)   => s"scope ${ref.name} => ${printCoreTerm(body)}"
      case m @ CoreAst.Term.Match(_, _, _, _, _) => printMatch(m)
      case b: CoreAst.Term.Body                  => printBody(b)
      case CoreAst.Term.Select(base, field, _)   => s"${printTermAtom(base)}[$field]"
      case CoreAst.Term.App(fn, args, _) =>
        val headStr = printTermAtom(fn)
        val argsStr = args.map(printTermAtom).mkString(", ")
        s"$headStr($argsStr)"
      case CoreAst.Term.Pi(binders, out, closure, _, _, _) =>
        val bindersStr = binders.map(printPiBinder).mkString(" -> ")
        s"${printCoreClosure(closure)}$bindersStr -> ${printCodomain(out)}"
      case CoreAst.Term.Sort(level, kind, scope, _) =>
        val (former, levelField) =
          if (isForm(level, CoreAst.Form.LevelZero)) ("Prop", None)
          else if (isForm(level, CoreAst.Form.LevelOne)) ("Type", None)
          else ("Sort", Some(printCoreTerm(level)))
        printSort(
          former,
          levelField,
          Option.unless(isForm(kind, CoreAst.Form.KindUnr))(printCoreTerm(kind)),
          Option.unless(isForm(scope, CoreAst.Form.LifetimeEmpty))(printCoreTerm(scope))
        )
      case CoreAst.Term.FormOp(form, args, _) =>
        val argsStr = if (args.isEmpty) "" else args.map(printCoreTerm).mkString("(", ", ", ")")
        s"${form.qualifiedName}$argsStr"
    }

    private def printCoreClosure(closure: CoreAst.Closure): String =
      printClosure(
        closure.kind.term.filterNot(isForm(_, CoreAst.Form.KindUnr)).map(printCoreTerm),
        closure.scope.term.filterNot(isForm(_, CoreAst.Form.LifetimeEmpty)).map(printCoreTerm)
      )

    private def printCase(c: CoreAst.Case): String = {
      val argNames = c.argRefs.map(_.name)
      val args = if (argNames.isEmpty) "" else s" ${argNames.mkString(" ")}"
      val ctor = if (c.isFullyQualified) c.ctorName else s".${c.ctorName}"
      s"| $ctor$args => ${printCoreTerm(c.body)}"
    }

    def printMatch(m: CoreAst.Term.Match): String = {
      val scrutStr = printTermAtom(m.scrut)
      val casesStr = m.cases.map(printCase).mkString(" ")
      s"match $scrutStr returning ${printCoreTerm(m.motive)} with $casesStr"
    }
  }

  private val unbound = new SyntaxPrinter(_ => None)

  def printBinder(b: CoreAst.Binder): String = unbound.printBinder(b)

  def printTerm(t: CoreAst.Ast): String = t match {
    case term: CoreAst.Term             => unbound.printCoreTerm(term)
    case decrease: CoreAst.DecreaseSpec => unbound.printDecreaseSpec(decrease)
  }

  /**
   * A level as source syntax (`Level.succ`, `Level.max`), not its normalized `max(atom+k, …, c)` form; a constant is
   * `Level.zero`, `Level.one` or successors of it, since a level field takes no numeral.
   */
  private def printLevel(level: Value.Level): String = {
    def succs(base: String, offset: Int): String =
      if (offset == 0) base else s"Level.succ(${succs(base, offset - 1)})"

    def atom(a: Value.Level.Atom): String =
      a match {
        case Value.Level.ParamAtom(id)      => printParameterVar(id, "u")
        case Value.Level.IMaxAtom(lhs, rhs) => s"Level.imax(${printLevel(lhs)}, ${printLevel(rhs)})"
      }

    val terms = level.terms.toVector.map { case (a, offset) => succs(atom(a), offset) }
    val constant = if (level.c == 0) "Level.zero" else succs("Level.one", level.c - 1)
    val parts = if (level.c > 0 || terms.isEmpty) terms :+ constant else terms
    parts match {
      case Vector(single) => single
      case several        => s"Level.max(${several.mkString(", ")})"
    }
  }

  /** A kind as source syntax: `Kind.lin`, `Kind.unr`, or its variables joined. */
  private def printKind(kind: Value.Kind): String =
    if (kind.isLin) "Kind.lin"
    else joined(kind.vars, "k", "Kind.unr", "Kind.join")

  /** A lifetime as source syntax; an atom prints as its `scope` binder (spec §4.1). */
  private def printLifetime(lifetime: Value.Lifetime): String =
    joined(lifetime.vars, "l", "Lifetime.empty", "Lifetime.union")

  private def joined(vars: DepSet, prefix: String, empty: String, form: String): String = {
    val names = Vector.newBuilder[String]
    vars.foreach(id => names += printParameterVar(id, prefix))
    names.result().reduceLeftOption((acc, name) => s"$form($acc, $name)").getOrElse(empty)
  }

  /**
   * A variable of a sort parameter, or an atom, prints as its binder's name, as a `Var` does; only one bound by `_`
   * prints by id.
   */
  private def printParameterVar(id: Value.VarId, prefix: String): String =
    FreshVar.parameterName(id).filter(name => name.nonEmpty && name != "_").getOrElse(s"$prefix#$id")

  /**
   * Opens the telescope at fresh variables to print the codomain. Binders are joined by arrows because that is the
   * spelling the parser folds back into this one binder group.
   */
  private def printPi(pi: Value.VPi): String = {
    val bodyEnv = telescope.BinderOps.freshen(pi)
    val bindersStr = pi.binders.map(new SyntaxPrinter(pi.env.locals.get).printPiBinder).mkString(" -> ")
    val closure = printClosure(
      Option.unless(pi.closureKind.isUnr)(printKind(pi.closureKind)),
      Option.unless(pi.closureScope.isEmpty)(printLifetime(pi.closureScope))
    )
    s"$closure$bindersStr -> ${printCodomain(pi.codomain(bodyEnv))}"
  }

  /**
   * A function type in codomain position is parenthesized. Grouping is part of a function type's identity, and written
   * bare, `A -> (B -> C)` would read back as the one group `A -> B -> C`, and a closure there would be misplaced.
   */
  private def printCodomain(codomain: Value): String =
    codomain match {
      case _: Value.VPi => s"(${print(codomain)})"
      case _            => print(codomain)
    }

  /** A variable prints as its binder name; the id only disambiguates the nameless `_`. */
  private def varName(v: Value.Var): String =
    if (v.name.nonEmpty && v.name != "_") v.name else s"_#${v.id}"

  private def printLam(lam: Value.VLam): String =
    lam.id match {
      case Value.ValueId.Const(name) => name
      case _: Value.ValueId.LocalId =>
        s"fun ${new SyntaxPrinter(lam.tpe.env.locals.get).printBinders(lam.tpe.binders)} => …"
    }

  /**
   * The call a stuck match came from. A recursive function's body env binds its self reference, which is the only thing
   * in a thunk that names the call; the match equals that call only when it is the body's result, so a match nested
   * deeper (or a non-recursive body, which binds no name) prints as the eliminator it is.
   */
  private def blockedCall(thunk: Value.NeutralThunk): Option[String] = {
    @annotation.tailrec
    def isResult(term: CoreAst.Term): Boolean =
      term match {
        case body: CoreAst.Term.Body => isResult(body.res)
        case m: CoreAst.Term.Match   => m.id == thunk.term.id
        case _                       => false
      }

    val callers = thunk.env.locals.valuesIterator.collect {
      case Value.VLam(pi, Value.ValueId.Const(name), Value.LamBody.Core(lam, _)) if isResult(lam.body) => (name, pi)
    }.toVector
    callers match {
      case Vector((name, pi)) =>
        val args = pi.binders.filter(!_.isImplicit).map(binder => thunk.env.locals.get(binder.localRef))
        Option.when(args.forall(_.isDefined))(s"$name(${args.map(arg => print(arg.get)).mkString(", ")})")
      case _ => None
    }
  }

  /**
   * The selector call a stuck field projection stands for. A match with one branch, whose body is one of that branch's
   * fields, on a local of a one-constructor family, projects that field: a struct's selector is this match, and so is
   * structure eta's projection (StructEta), whose fields are named by position. Either prints as `P.x(v)`, with the
   * field named as the constructor names it. The kernel does not record which families are structs, so a
   * one-constructor `inductive`, which has no selectors, prints its projections the same way.
   */
  private def fieldProjection(thunk: Value.NeutralThunk): Option[String] =
    thunk.term match {
      case CoreAst.Term.Match(CoreAst.Term.LocalRef(scrutinee, _), _, Vector(branch), _, _) =>
        val fieldIdx = branch.body match {
          case CoreAst.Term.LocalRef(ref, _) => branch.argRefs.indexOf(ref)
          case _                             => -1
        }
        for {
          base <- thunk.env.locals.get(scrutinee) if fieldIdx >= 0
          family <- Value.InductiveFamilyValue.unapply(base.tpe)
          ctorHead <- family.meta.projectionInfo.flatMap(_.ctorHeadOption)
          field = ctorHead.fieldBinders(fieldIdx).name if field != "_"
        } yield s"${family.head.name}.$field(${print(base)})"
      case _ => None
    }

  /** A stuck match that prints as the call it stands for rather than as the match. */
  private def printedCall(thunk: Value.NeutralThunk): Option[String] = blockedCall(thunk).orElse(fieldProjection(thunk))

  def print(value: Value): String = value match {
    case sort: Value.VSort =>
      val (former, levelField) =
        if (Sorts.isProp(sort)) ("Prop", None)
        else if (sort.level == Value.Level.one) ("Type", None)
        else ("Sort", Some(printLevel(sort.level)))
      printSort(
        former,
        levelField,
        Option.unless(sort.kind.isUnr)(printKind(sort.kind)),
        Option.unless(sort.scope.isEmpty)(printLifetime(sort.scope))
      )
    case level: Value.Level                      => printLevel(level)
    case kind: Value.Kind                        => printKind(kind)
    case lifetime: Value.Lifetime                => printLifetime(lifetime)
    case pi: Value.VPi                           => printPi(pi)
    case Value.VConst(name, _, _)                => name
    case Value.ConstructorHead(name, _, _, _, _) => name
    case Value.VCtor(head, Vector(field: Value.VPacked), _)
        if head.name == "String.mk" && field.codec.isInstanceOf[Value.CharListCodec] =>
      printString(field.charScalars.getOrElse(wtf("Invalid packed String field")))
    case Value.VCtor(head, storedArgs, _) =>
      val headStr = print(head)
      if (storedArgs.isEmpty) headStr
      else s"$headStr(${storedArgs.map(print).mkString(", ")})"
    case v: Value.VApp => printApp(v.head, v.args)
    case v: Value.VLam => printLam(v)
    case v: Value.Var  => varName(v)
    case s: Value.NeutralThunk =>
      printedCall(s).getOrElse(new SyntaxPrinter(s.env.locals.get).printMatch(s.term))
    case p: Value.VProof => s"‹proof of ${print(p.tpe)}›"
    case p: Value.VPacked =>
      p.natValue
        .map(_.toString)
        .orElse(p.charScalars.map(scalars => s"proj[String,0](${printString(scalars)})"))
        .getOrElse(wtf("Unknown packed payload"))
    case Value.LevelTpe      => CoreAst.Parameter.Level.name
    case Value.KindTpe       => CoreAst.Parameter.Kind.name
    case Value.LifetimeTpe   => CoreAst.Parameter.Lifetime.name
    case Value.SortParameter => "SortParameter"
    case Value.Large         => "Large"
  }

}
