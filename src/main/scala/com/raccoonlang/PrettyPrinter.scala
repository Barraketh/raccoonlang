package com.raccoonlang

object PrettyPrinter {
  private def numeral[A](value: A)(layer: A => Option[(String, Vector[A])]): Option[BigInt] = {
    @annotation.tailrec
    def loop(current: A, count: BigInt): Option[BigInt] =
      layer(current) match {
        case Some(("Nat.zero", Vector()))         => Some(count)
        case Some(("Nat.succ", Vector(previous))) => loop(previous, count + 1)
        case _                                    => None
      }
    loop(value, BigInt(0))
  }

  private object NatValue {
    def unapply(value: Value): Option[BigInt] = numeral(value)(Value.ConstructorForm.unapply)
  }

  private object NatTerm {
    def unapply(term: CoreAst.Term): Option[BigInt] = numeral(term) {
      case CoreAst.Term.GlobalRef(name, _)                            => Some((name, Vector.empty))
      case CoreAst.Term.App(CoreAst.Term.GlobalRef(name, _), args, _) => Some((name, args))
      case _                                                          => None
    }
  }

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
      case _                                                               => s"(${print(head)})"
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

  private def printSort(former: String, level: Option[String]): String =
    level.fold(former)(value => s"$former { level = $value }")

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
      case _: CoreAst.Term.Ref | _: CoreAst.Term.App | _: CoreAst.Term.Select | _: CoreAst.Term.Sort |
          _: CoreAst.Term.FormOp =>
        printCoreTerm(t)
      case _: CoreAst.Term.Lam | _: CoreAst.Term.Match | _: CoreAst.Term.Body | _: CoreAst.Term.Pi =>
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
      case NatTerm(value)        => value.toString
      case ref: CoreAst.Term.Ref => printRef(ref)
      case CoreAst.Term.Lam(ty, body, _, _, _, recursion, _) =>
        val decreaseStr = recursion.map(r => s" ${printDecreaseSpec(r.decreases)}").getOrElse("")
        s"fun ${printBinders(ty.binders)}: ${printCoreTerm(ty.out)}$decreaseStr => " +
          printCoreTerm(body)
      case m @ CoreAst.Term.Match(_, _, _, _, _) => printMatch(m)
      case b: CoreAst.Term.Body                  => printBody(b)
      case CoreAst.Term.Select(base, field, _)   => s"${printTermAtom(base)}[$field]"
      case CoreAst.Term.App(fn, args, _) =>
        val headStr = printTermAtom(fn)
        val argsStr = args.map(printTermAtom).mkString(", ")
        s"$headStr($argsStr)"
      case CoreAst.Term.Pi(binders, out, _, _, _) =>
        val bindersStr = binders.map(printPiBinder).mkString(" -> ")
        s"$bindersStr -> ${printCodomain(out)}"
      case CoreAst.Term.Sort(level, _) =>
        val (former, levelField) =
          if (isForm(level, CoreAst.Form.LevelZero)) ("Prop", None)
          else if (isForm(level, CoreAst.Form.LevelOne)) ("Type", None)
          else ("Sort", Some(printCoreTerm(level)))
        printSort(former, levelField)
      case CoreAst.Term.FormOp(form, args, _) =>
        val argsStr = if (args.isEmpty) "" else args.map(printCoreTerm).mkString("(", ", ", ")")
        s"${form.qualifiedName}$argsStr"
    }

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

  private def printParameterVar(id: Value.VarId, prefix: String): String =
    FreshVar.parameterName(id).filter(name => name.nonEmpty && name != "_").getOrElse(s"$prefix#$id")

  /**
   * Opens the telescope at fresh variables to print the codomain. Binders are joined by arrows because that is the
   * spelling the parser folds back into this one binder group.
   */
  private def printPi(pi: Value.VPi): String = {
    val bodyEnv = telescope.BinderOps.freshen(pi)
    val bindersStr = pi.binders.map(new SyntaxPrinter(pi.env.locals.get).printPiBinder).mkString(" -> ")
    s"$bindersStr -> ${printCodomain(pi.codomain(bodyEnv))}"
  }

  /**
   * A function type in codomain position is parenthesized. Grouping is part of a function type's identity, and written
   * bare, `A -> (B -> C)` would read back as the one group `A -> B -> C`.
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
    case NatValue(number) => number.toString
    case sort: Value.VSort =>
      val (former, levelField) =
        if (Sorts.isProp(sort)) ("Prop", None)
        else if (sort.level == Value.Level.one) ("Type", None)
        else ("Sort", Some(printLevel(sort.level)))
      printSort(former, levelField)
    case level: Value.Level                      => printLevel(level)
    case pi: Value.VPi                           => printPi(pi)
    case Value.VConst(name, _, _)                => name
    case Value.ConstructorHead(name, _, _, _, _) => name
    case Value.VCtor(head, storedArgs, _) =>
      val headStr = print(head)
      if (storedArgs.isEmpty) headStr
      else s"$headStr(${storedArgs.map(print).mkString(", ")})"
    case v: Value.VApp => printApp(v.head, v.args)
    case v: Value.VLam => printLam(v)
    case v: Value.Var  => varName(v)
    case s: Value.NeutralThunk =>
      printedCall(s).getOrElse(new SyntaxPrinter(s.env.locals.get).printMatch(s.term))
    case p: Value.VProof     => s"‹proof of ${print(p.tpe)}›"
    case Value.LevelTpe      => CoreAst.Parameter.Level.name
    case Value.SortParameter => "SortParameter"
    case Value.Large         => "Large"
  }

}
