package com.raccoonlang

import scala.collection.mutable

object PrettyPrinter {
  private def printString(scalars: Vector[Int]): String = UnicodeScalarString.renderQuoted(scalars)

  /**
   * Printing expands pieces in a loop over an explicit stack, appending text to one buffer, so it takes no host stack
   * however deep the value is, and time linear in its output. A piece is text as printed, a value to print, or work
   * left for when it is reached, such as syntax to print or a codomain to compute; expanding one gives the pieces it
   * prints as, in order.
   */
  private sealed trait Piece
  private final case class Text(text: String) extends Piece
  private final case class Val(value: Value) extends Piece
  private final case class Later(pieces: () => Vector[Piece]) extends Piece

  private def parens(piece: Piece): Vector[Piece] = Vector(Text("("), piece, Text(")"))

  /** The items with the separator between each two. */
  private def separated(items: Seq[Piece], separator: String): Vector[Piece] = {
    val out = Vector.newBuilder[Piece]
    items.iterator.zipWithIndex.foreach { case (item, idx) =>
      if (idx > 0) out += Text(separator)
      out += item
    }
    out.result()
  }

  /** An argument list: the items, comma-separated, in parentheses. */
  private def argList(items: Seq[Piece]): Vector[Piece] = (Text("(") +: separated(items, ", ")) :+ Text(")")

  /**
   * Implicit and evidence arguments are not written among a call's arguments, so a saturated call prints only its
   * explicit ones. Anything that is not a plain saturated call keeps every argument but evidence, which printing
   * neither shows nor forces.
   */
  private def explicitArgs(app: Value.VApp): Seq[Value] =
    app.head.tpe match {
      case pi: Value.VPi => app.explicitArgs(pi).getOrElse(app.determiningArgs)
      case _             => app.determiningArgs
    }

  /**
   * A constructor application's stored fields but its evidence fields, which a construction does not write: its
   * determining arguments, so printing reads no evidence field and forces none.
   */
  private object WrittenFields {
    def unapply(value: Value): Option[(Value.ConstructorHead, Vector[Value])] =
      value match {
        case app: Value.VApp => Value.ConstructorApp.unapply(app).map(head => (head, app.determiningArgs))
        case _               => None
      }
  }

  private def printApp(app: Value.VApp): Vector[Piece] = {
    val head = app.head
    val headPieces = head match {
      case _: Value.VApp | _: Value.VConst | _: Value.Var | _: Value.VSort => Vector(Val(head))
      // A named lambda prints as its name, such as a native operation heading its neutral application.
      case Value.VLam(_, _: Value.ValueId.Const, _) => Vector(Val(head))
      case _                                        => parens(Val(head))
    }
    headPieces ++ argList(explicitArgs(app).map(Val))
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
  private def printSort(
      former: String,
      level: Option[Piece],
      kind: Option[Piece],
      scope: Option[Piece]
  ): Vector[Piece] = {
    val fields = fieldList(level.map("level" -> _).toVector ++ kind.map("kind" -> _) ++ scope.map("scope" -> _))
    if (fields.isEmpty) Vector(Text(former)) else Text(s"$former ") +: fields
  }

  /**
   * A closure prefix: the fields that are not `Kind.unr` or `Lifetime.empty`, with a trailing space, or nothing. A
   * lambda's derived field prints as the expression the checker derived, once it has.
   */
  private def printClosure(kind: Option[Piece], scope: Option[Piece]): Vector[Piece] = {
    val fields = fieldList(kind.map("kind" -> _).toVector ++ scope.map("scope" -> _))
    if (fields.isEmpty) Vector.empty else fields :+ Text(" ")
  }

  private def fieldList(fields: Vector[(String, Piece)]): Vector[Piece] =
    if (fields.isEmpty) Vector.empty
    else {
      val out = Vector.newBuilder[Piece]
      fields.iterator.zipWithIndex.foreach { case ((name, value), idx) =>
        out += Text(if (idx == 0) s"{ $name = " else s", $name = ")
        out += value
      }
      (out += Text(" }")).result()
    }

  /**
   * Core syntax as source, under the values its free locals are bound to: a bound local prints as its value, and any
   * other by its binder's name. A value holding syntax (a function type's binders, a stuck match) prints under its own
   * environment, so a generated name such as a selector's parameter never shows for the argument it stands for.
   */
  private final class SyntaxPrinter(bound: CoreAst.LocalRef => Option[Value]) {
    private def term(t: CoreAst.Term): Piece = Later(() => printCoreTerm(t))

    private def printRef(ref: CoreAst.Term.Ref): Piece = ref match {
      case CoreAst.Term.GlobalRef(name, _) => Text(name)
      case CoreAst.Term.LocalRef(ref, _)   => bound(ref).fold[Piece](Text(ref.name))(Val)
    }

    def printDecreaseSpec(spec: CoreAst.DecreaseSpec): Vector[Piece] =
      spec match {
        case CoreAst.DecreaseSpec.Lexicographic(args, _) =>
          Vector(Text(s"decreases lexicographic(${args.map(_.name).mkString(", ")})"))
        case CoreAst.DecreaseSpec.Measure(measure, _) =>
          Vector(Text("decreases measure("), term(measure), Text(")"))
      }

    /** A binder as written: `(x: A)`, `{x: A}` or `[h: P]`. */
    def printBinder(b: CoreAst.Binder): Vector[Piece] = {
      val (open, close) = b.mode match {
        case BinderMode.Explicit => ("(", ")")
        case BinderMode.Implicit => ("{", "}")
        case BinderMode.Evidence => ("[", "]")
      }
      Vector(Text(s"$open${b.name}: "), term(b.ty), Text(close))
    }

    def printPiBinder(b: CoreAst.Binder): Vector[Piece] =
      if (b.name == "_" && b.mode == BinderMode.Explicit) printTermAtom(b.ty)
      else printBinder(b)

    def printBinders(binders: Vector[CoreAst.Binder]): Vector[Piece] =
      separated(binders.map(b => Later(() => printBinder(b))), " ")

    /**
     * A block's lets as written. A nested pattern is a destructuring of an anonymous component of an earlier
     * destructuring in the block (PAIRS_AND_PRELUDE §3.3), and it prints inside that component's pattern. No name
     * resolves to an anonymous local, so nothing else in the block names one.
     */
    private def printLets(lets: Vector[CoreAst.Let]): Vector[Piece] = {
      val anonymous = lets.flatMap { l =>
        l.pattern match {
          case CoreAst.LetPattern.Fields(vars, _) => vars.map(_.ref).filter(_.name == "_")
          case _: CoreAst.LetPattern.Local        => Vector.empty
        }
      }.toSet
      def nestedAt(l: CoreAst.Let): Option[CoreAst.LocalRef] =
        l match {
          case CoreAst.Let(_: CoreAst.LetPattern.Fields, None, CoreAst.Term.LocalRef(ref, _), _) if anonymous(ref) =>
            Some(ref)
          case _ => None
        }
      val nested = lets.flatMap(l => nestedAt(l).map(_ -> l.pattern)).toMap
      def pattern(written: CoreAst.LetPattern): Vector[Piece] =
        written match {
          case CoreAst.LetPattern.Local(ref) => Vector(Text(ref.name))
          case CoreAst.LetPattern.Fields(vars, _) =>
            val components =
              vars.map(v => nested.get(v.ref).fold[Piece](Text(v.ref.name))(p => Later(() => pattern(p))))
            (Text("(") +: separated(components, ", ")) :+ Text(")")
        }
      val printed = lets.filter(nestedAt(_).isEmpty).map { l =>
        val ty = l.ty.toVector.flatMap(t => Vector(Text(": "), term(t)))
        Later(() => (Text("let ") +: pattern(l.pattern)) ++ ty ++ Vector(Text(" := "), term(l.value)))
      }
      separated(printed, "\n")
    }

    private def printBody(b: CoreAst.Term.Body): Vector[Piece] = {
      if (b.lets.isEmpty) Vector(term(b.res))
      else (Text("{ ") +: printLets(b.lets)) ++ Vector(Text(" \n "), term(b.res), Text(" }"))
    }

    /**
     * A term in a position where an operator would bind tighter than the term prints: atoms and already-delimited forms
     * render as themselves, and the forms that print as loose infix-ish syntax get parenthesized.
     */
    private def printTermAtom(t: CoreAst.Term): Vector[Piece] = t match {
      // A bound local stands for its value, which may itself print as loose syntax.
      case CoreAst.Term.LocalRef(ref, _) if bound(ref).exists(isLoose) => parens(term(t))
      case _: CoreAst.Term.NatLit | _: CoreAst.Term.StrLit | _: CoreAst.Term.Ref | _: CoreAst.Term.App |
          _: CoreAst.Term.Select | _: CoreAst.Term.Sort | _: CoreAst.Term.FormOp =>
        Vector(term(t))
      case _: CoreAst.Term.Lam | _: CoreAst.Term.Scope | _: CoreAst.Term.Match | _: CoreAst.Term.Body |
          _: CoreAst.Term.Pi =>
        parens(term(t))
    }

    /**
     * A function type's codomain, parenthesized when it is a function type itself, as the value printer's
     * `PrettyPrinter.printCodomain` says why; a local bound to a value prints as that value does there.
     */
    private def printCodomain(out: CoreAst.Term): Vector[Piece] = out match {
      case _: CoreAst.Term.Pi            => parens(term(out))
      case CoreAst.Term.LocalRef(ref, _) => bound(ref).fold(Vector[Piece](Text(ref.name)))(PrettyPrinter.printCodomain)
      case _                             => Vector(term(out))
    }

    def printCoreTerm(t: CoreAst.Term): Vector[Piece] = t match {
      case CoreAst.Term.NatLit(value, _)   => Vector(Text(value.toString))
      case CoreAst.Term.StrLit(scalars, _) => Vector(Text(printString(scalars)))
      case ref: CoreAst.Term.Ref           => Vector(printRef(ref))
      case CoreAst.Term.Lam(ty, body, _, _, _, recursion, _) =>
        val decrease = recursion.toVector.flatMap(r => Text(" ") +: printDecreaseSpec(r.decreases))
        (Text("fun ") +: printCoreClosure(ty.closure)) ++ printBinders(ty.binders) ++
          Vector(Text(": "), term(ty.out)) ++ decrease ++ Vector(Text(" => "), term(body))
      case CoreAst.Term.Scope(ref, body, _, _)   => Vector(Text(s"scope ${ref.name} => "), term(body))
      case m @ CoreAst.Term.Match(_, _, _, _, _) => printMatch(m)
      case b: CoreAst.Term.Body                  => printBody(b)
      case CoreAst.Term.Select(base, field, _)   => printTermAtom(base) :+ Text(s"[$field]")
      case CoreAst.Term.App(fn, args, evidence, _) =>
        val evidencePieces =
          if (evidence.isEmpty) Vector.empty
          else (Text("[") +: separated(evidence.map(proof => Later(() => printTermAtom(proof))), ", ")) :+ Text("]")
        printTermAtom(fn) ++ argList(args.map(arg => Later(() => printTermAtom(arg)))) ++ evidencePieces
      case CoreAst.Term.Pi(binders, out, closure, _, _, _) =>
        val bindersPieces = separated(binders.map(b => Later(() => printPiBinder(b))), " -> ")
        printCoreClosure(closure) ++ bindersPieces ++ (Text(" -> ") +: printCodomain(out))
      case CoreAst.Term.Sort(level, kind, scope, _) =>
        val (former, levelField) =
          if (isForm(level, CoreAst.Form.LevelZero)) ("Prop", None)
          else if (isForm(level, CoreAst.Form.LevelOne)) ("Type", None)
          else ("Sort", Some(term(level)))
        printSort(
          former,
          levelField,
          Option.unless(isForm(kind, CoreAst.Form.KindUnr))(term(kind)),
          Option.unless(isForm(scope, CoreAst.Form.LifetimeEmpty))(term(scope))
        )
      case CoreAst.Term.FormOp(form, args, _) =>
        Text(form.qualifiedName) +: (if (args.isEmpty) Vector.empty else argList(args.map(term)))
    }

    private def printCoreClosure(closure: CoreAst.Closure): Vector[Piece] =
      printClosure(
        closure.kind.term.filterNot(isForm(_, CoreAst.Form.KindUnr)).map(term),
        closure.scope.term.filterNot(isForm(_, CoreAst.Form.LifetimeEmpty)).map(term)
      )

    private def printCase(c: CoreAst.Case): Vector[Piece] = {
      val argNames = c.argRefs.map(_.name)
      val args = if (argNames.isEmpty) "" else s" ${argNames.mkString(" ")}"
      val ctor = if (c.isFullyQualified) c.ctorName else s".${c.ctorName}"
      Vector(Text(s"| $ctor$args => "), term(c.body))
    }

    def printMatch(m: CoreAst.Term.Match): Vector[Piece] = {
      val cases = separated(m.cases.map(c => Later(() => printCase(c))), " ")
      (Text("match ") +: printTermAtom(m.scrut)) ++ Vector(Text(" returning "), term(m.motive), Text(" with ")) ++ cases
    }
  }

  private val unbound = new SyntaxPrinter(_ => None)

  def printBinder(b: CoreAst.Binder): String = new Printer(None).run(unbound.printBinder(b))

  def printTerm(t: CoreAst.Ast): String = t match {
    case term: CoreAst.Term             => new Printer(None).run(unbound.printCoreTerm(term))
    case decrease: CoreAst.DecreaseSpec => new Printer(None).run(unbound.printDecreaseSpec(decrease))
  }

  /**
   * A level as source syntax (`Level.succ`, `Level.max`), not its normalized `max(atom+k, …, c)` form; a constant is
   * `Level.zero`, `Level.one` or successors of it, since a level field takes no numeral.
   */
  private def printLevel(level: Value.Level): Vector[Piece] = {
    def succs(base: Piece, offset: Int): Piece =
      if (offset == 0) base else Later(() => Vector(Text("Level.succ(" * offset), base, Text(")" * offset)))

    def atom(a: Value.Level.Atom): Piece =
      a match {
        case Value.Level.ParamAtom(id) => Text(printParameterVar(id, "u"))
        case Value.Level.IMaxAtom(lhs, rhs) =>
          Later(() => (Text("Level.imax(") +: printLevel(lhs)) ++ (Text(", ") +: printLevel(rhs)) :+ Text(")"))
      }

    val terms = level.terms.toVector.map { case (a, offset) => succs(atom(a), offset) }
    val constant = if (level.c == 0) Text("Level.zero") else succs(Text("Level.one"), level.c - 1)
    val parts = if (level.c > 0 || terms.isEmpty) terms :+ constant else terms
    parts match {
      case Vector(single) => Vector(single)
      case several        => (Text("Level.max(") +: separated(several, ", ")) :+ Text(")")
    }
  }

  /** A kind as source syntax: `Kind.lin`, `Kind.unr`, or its variables joined. */
  private def printKind(kind: Value.Kind): String =
    if (kind.isLin) "Kind.lin"
    else joined(kind.vars, "k", "Kind.unr", "Kind.join")

  /** A lifetime as source syntax; an atom prints as its `scope` binder (spec §4.1). */
  private def printLifetime(lifetime: Value.Lifetime): String =
    joined(lifetime.vars, "l", "Lifetime.empty", "Lifetime.union")

  /** The variables joined by `form`, nested to the left, `form(form(a, b), c)`, or `empty` when there are none. */
  private def joined(vars: DepSet, prefix: String, empty: String, form: String): String = {
    val names = Vector.newBuilder[String]
    vars.foreach(id => names += printParameterVar(id, prefix))
    names.result() match {
      case first +: rest =>
        val out = new StringBuilder(s"$form(" * rest.length).append(first)
        rest.foreach(name => out.append(", ").append(name).append(')'))
        out.result()
      case _ => empty
    }
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
  private def printPi(pi: Value.VPi): Vector[Piece] = {
    val bodyEnv = telescope.BinderOps.freshen(pi)
    val syntax = new SyntaxPrinter(pi.env.locals.get)
    val binders = separated(pi.binders.map(b => Later(() => syntax.printPiBinder(b))), " -> ")
    val closure = printClosure(
      Option.unless(pi.closureKind.isUnr)(Text(printKind(pi.closureKind))),
      Option.unless(pi.closureScope.isEmpty)(Text(printLifetime(pi.closureScope)))
    )
    closure ++ binders ++ Vector(Text(" -> "), Later(() => printCodomain(pi.codomain(bodyEnv))))
  }

  /**
   * A function type in codomain position is parenthesized. Grouping is part of a function type's identity, and written
   * bare, `A -> (B -> C)` would read back as the one group `A -> B -> C`, and a closure there would be misplaced.
   */
  private def printCodomain(codomain: Value): Vector[Piece] =
    codomain match {
      case _: Value.VPi => parens(Val(codomain))
      case _            => Vector(Val(codomain))
    }

  /** A variable prints as its binder name; the id only disambiguates the nameless `_`. */
  private def varName(v: Value.Var): String =
    if (v.name.nonEmpty && v.name != "_") v.name else s"_#${v.id}"

  private def printLam(lam: Value.VLam): Vector[Piece] =
    lam.id match {
      case Value.ValueId.Const(name) => Vector(Text(name))
      case _: Value.ValueId.LocalId =>
        (Text("fun ") +: new SyntaxPrinter(lam.tpe.env.locals.get).printBinders(lam.tpe.binders)) :+ Text(" => …")
    }

  /**
   * The call a stuck match came from. A recursive function's body env binds its self reference, which is the only thing
   * in a thunk that names the call; the match equals that call only when it is the body's result, so a match nested
   * deeper (or a non-recursive body, which binds no name) prints as the eliminator it is.
   */
  private def blockedCall(thunk: Value.NeutralThunk): Option[Vector[Piece]] = {
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
        val args =
          pi.binders.filter(_.mode == BinderMode.Explicit).map(binder => thunk.env.locals.get(binder.localRef))
        Option.when(args.forall(_.isDefined))(Text(name) +: argList(args.map(arg => Val(arg.get))))
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
  private def fieldProjection(thunk: Value.NeutralThunk): Option[Vector[Piece]] =
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
        } yield Vector(Text(s"${family.head.name}.$field("), Val(base), Text(")"))
      case _ => None
    }

  /** A stuck match that prints as the call it stands for rather than as the match. */
  private def printedCall(thunk: Value.NeutralThunk): Option[Vector[Piece]] =
    blockedCall(thunk).orElse(fieldProjection(thunk))

  /**
   * The characters of a `String` value, when every one of them is known (docs/kernel.md, "Strings"). Those of a packed
   * scalar list are known by construction. Any other character is known only by the String layout, as `Char.ofNat(s)`
   * for a Unicode scalar `s`, so a reader without the layout knows only a packed String, and one with it also knows a
   * computed String, built of `List.cons` and `List.nil` around characters and packed tails.
   */
  private final class StringReader(strings: Option[Value.ValidatedStringLayout]) {

    /**
     * The constructor `Char.ofNat` applies to its argument, when its result is exactly that constructor over it: then
     * `Char.ofNat(s)` is that constructor over `s`, so the character it makes names its scalar. Found by applying it to
     * a fresh variable.
     */
    private lazy val charConstructor: Option[String] = strings.flatMap { layout =>
      val codec = layout.charListCodec
      val scalar = FreshVar.freshVar("value", codec.natTpe)
      Interpreter.evalApply(codec.charOfNat, Vector(scalar)) match {
        case Value.VCtor(head, Vector(Value.Var(_, id, _)), _) if id == scalar.id => Some(head.name)
        case _                                                                    => None
      }
    }

    private def scalar(char: Value): Option[Int] =
      char match {
        case Value.VCtor(head, Vector(code: Value.VPacked), _) if charConstructor.contains(head.name) =>
          code.natValue.filter(n => n.isValidInt && UnicodeScalarString.isScalar(n.toInt)).map(_.toInt)
        case _ => None
      }

    def scalars(value: Value): Option[Vector[Int]] =
      value match {
        case WrittenFields(head, Vector(chars)) if head.name == "String.mk" =>
          val known = Vector.newBuilder[Int]
          @annotation.tailrec
          def loop(rest: Value): Option[Vector[Int]] =
            rest match {
              case packed: Value.VPacked => packed.charScalars.map(tail => (known ++= tail).result())
              case Value.VCtor(cons, Vector(char, tail), _) if cons.name == "List.cons" =>
                scalar(char) match {
                  case Some(s) =>
                    known += s
                    loop(tail)
                  case None => None
                }
              case Value.VCtor(nil, Vector(), _) if nil.name == "List.nil" && strings.nonEmpty => Some(known.result())
              case _                                                                           => None
            }
          loop(chars)
        case _ => None
      }
  }

  /** Expands pieces in order into one buffer; see `Piece`. */
  private final class Printer(strings: Option[Value.ValidatedStringLayout]) {
    private val reader = new StringReader(strings)

    def run(pieces: Vector[Piece]): String = {
      val out = new StringBuilder
      val stack = mutable.Stack.empty[Piece]
      def push(expanded: Vector[Piece]): Unit = expanded.reverseIterator.foreach(stack.push)
      push(pieces)
      while (stack.nonEmpty)
        stack.pop() match {
          case Text(text)   => out.append(text)
          case Val(value)   => push(expand(value))
          case Later(later) => push(later())
        }
      out.result()
    }

    private def expand(value: Value): Vector[Piece] = value match {
      case sort: Value.VSort =>
        val (former, levelField) =
          if (Sorts.isProp(sort)) ("Prop", None)
          else if (sort.level == Value.Level.one) ("Type", None)
          else ("Sort", Some(Later(() => printLevel(sort.level))))
        printSort(
          former,
          levelField,
          Option.unless(sort.kind.isUnr)(Text(printKind(sort.kind))),
          Option.unless(sort.scope.isEmpty)(Text(printLifetime(sort.scope)))
        )
      case level: Value.Level                      => printLevel(level)
      case kind: Value.Kind                        => Vector(Text(printKind(kind)))
      case lifetime: Value.Lifetime                => Vector(Text(printLifetime(lifetime)))
      case pi: Value.VPi                           => printPi(pi)
      case Value.VConst(name, _, _)                => Vector(Text(name))
      case Value.ConstructorHead(name, _, _, _, _) => Vector(Text(name))
      case WrittenFields(head, fields) =>
        reader.scalars(value) match {
          case Some(scalars)          => Vector(Text(printString(scalars)))
          case None if fields.isEmpty => Vector(Text(head.name))
          case None                   => Text(head.name) +: argList(fields.map(Val))
        }
      case v: Value.VApp => printApp(v)
      case v: Value.VLam => printLam(v)
      case v: Value.Var  => Vector(Text(varName(v)))
      case s: Value.NeutralThunk =>
        printedCall(s).getOrElse(new SyntaxPrinter(s.env.locals.get).printMatch(s.term))
      case p: Value.VProof => Vector(Text("‹proof of "), Val(p.tpe), Text("›"))
      // Printing does not force it, so printing evaluates no proposition the program has not.
      case _: Value.DeferredEvidence => Vector(Text("‹deferred evidence›"))
      case p: Value.VPacked =>
        val printed = p.natValue
          .map(_.toString)
          .orElse(p.charScalars.map(scalars => s"proj[String,0](${printString(scalars)})"))
          .getOrElse(wtf("Unknown packed payload"))
        Vector(Text(printed))
      case Value.LevelTpe      => Vector(Text(CoreAst.Parameter.Level.name))
      case Value.KindTpe       => Vector(Text(CoreAst.Parameter.Kind.name))
      case Value.LifetimeTpe   => Vector(Text(CoreAst.Parameter.Lifetime.name))
      case Value.SortParameter => Vector(Text("SortParameter"))
      case Value.Large         => Vector(Text("Large"))
    }
  }

  /** A value as source, knowing only the characters a `String` value itself shows: those of a packed literal. */
  def print(value: Value): String = print(value, None)

  /** A value as source; a `String` whose characters the layout, when given, makes known prints as a literal. */
  def print(value: Value, strings: Option[Value.ValidatedStringLayout]): String =
    new Printer(strings).run(Vector(Val(value)))

  /** A `String` value's characters, unquoted and unescaped, when they are all known: what `--raw` prints. */
  def rawString(value: Value, strings: Option[Value.ValidatedStringLayout]): Option[String] =
    new StringReader(strings).scalars(value).map(scalars => new String(scalars.toArray, 0, scalars.length))
}
