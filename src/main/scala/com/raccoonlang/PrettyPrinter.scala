package com.raccoonlang

import scala.collection.mutable

object PrettyPrinter {
  private def numeral[A <: AnyRef](
      value: A,
      layer: A => Option[(String, Vector[A])],
      cache: java.util.IdentityHashMap[A, Option[BigInt]]
  ): Option[BigInt] = {
    if (cache.containsKey(value)) return cache.get(value)

    var path: mutable.ArrayBuffer[A] = null
    var current = value
    var terminal: Option[BigInt] = None
    var failed = false
    var done = false
    while (!done) {
      if (cache.containsKey(current)) {
        terminal = cache.get(current)
        failed = terminal.isEmpty
        done = true
      } else {
        layer(current) match {
          case Some(("Nat.zero", Vector())) =>
            terminal = Some(BigInt(0))
            done = true
          case Some(("Nat.succ", Vector(previous))) =>
            if (path == null) path = mutable.ArrayBuffer.empty[A]
            path += current
            current = previous
          case _ =>
            cache.put(current, None)
            failed = true
            done = true
        }
      }
    }

    if (failed) {
      if (path != null) path.foreach(node => cache.put(node, None))
      cache.put(value, None)
      None
    } else {
      val base = terminal.get
      val pathLength = if (path == null) 0 else path.length
      var index = pathLength - 1
      while (index >= 0) {
        cache.put(path(index), Some(base + BigInt(path.length - index)))
        index -= 1
      }
      val result = base + BigInt(pathLength)
      cache.put(value, Some(result))
      Some(result)
    }
  }

  /** Printing work is represented explicitly so values and syntax can be arbitrarily deep. */
  private sealed trait Piece
  private final case class Text(value: String) extends Piece
  private final case class Val(value: Value) extends Piece
  private final case class Term(value: CoreAst.Term, bound: CoreAst.LocalRef => Option[Value]) extends Piece
  private final case class Level(value: Value.Level) extends Piece
  private final case class Later(expand: () => Vector[Piece]) extends Piece

  private def parens(piece: Piece): Vector[Piece] = Vector(Text("("), piece, Text(")"))

  private def separated(items: Seq[Piece], separator: String): Vector[Piece] = {
    val out = Vector.newBuilder[Piece]
    items.iterator.zipWithIndex.foreach { case (item, idx) =>
      if (idx > 0) out += Text(separator)
      out += item
    }
    out.result()
  }

  private def argList(items: Seq[Piece]): Vector[Piece] = (Text("(") +: separated(items, ", ")) :+ Text(")")

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

  private def printApp(head: Value, args: Seq[Value]): Vector[Piece] = {
    val headPiece = head match {
      case _: Value.VApp | _: Value.VConst | _: Value.Var | _: Value.VSort => Val(head)
      case _                                                               => Later(() => parens(Val(head)))
    }
    headPiece +: argList(explicitArgs(head, args).map(Val))
  }

  /** A value that prints as loose syntax, so it is parenthesized where an atom is expected. */
  private def isLoose(value: Value): Boolean =
    value match {
      case _: Value.VPi                               => true
      case Value.VLam(_, _: Value.ValueId.LocalId, _) => true
      case thunk: Value.NeutralThunk                  => printedCall(thunk).isEmpty
      case _                                          => false
    }

  private def isForm(term: CoreAst.Term, form: CoreAst.LevelForm): Boolean =
    term match {
      case CoreAst.Term.FormOp(`form`, _, _) => true
      case _                                 => false
    }

  private def printSort(former: String, level: Option[Piece]): Vector[Piece] =
    level match {
      case None        => Vector(Text(former))
      case Some(value) => Vector(Text(s"$former { level = "), value, Text(" }"))
    }

  /**
   * Core syntax as source, under the values its free locals are bound to: a bound local prints as its value, and any
   * other by its binder's name. A value holding syntax prints under its own environment.
   */
  private final class SyntaxPrinter(bound: CoreAst.LocalRef => Option[Value]) {
    private def term(value: CoreAst.Term): Piece = Term(value, bound)

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

    def printBinder(binder: CoreAst.Binder): Vector[Piece] = {
      val (open, close) = if (binder.isImplicit) ("{", "}") else ("(", ")")
      Vector(Text(s"$open${binder.name}: "), term(binder.ty), Text(close))
    }

    def printPiBinder(binder: CoreAst.Binder): Vector[Piece] =
      if (binder.name == "_" && !binder.isImplicit) printTermAtom(binder.ty)
      else printBinder(binder)

    def printBinders(binders: Vector[CoreAst.Binder]): Vector[Piece] =
      separated(binders.map(binder => Later(() => printBinder(binder))), " ")

    private def printLet(let: CoreAst.Let): Vector[Piece] = {
      val ty = let.ty.toVector.flatMap(tpe => Vector(Text(s": "), term(tpe)))
      Vector(Text(s"let ${let.name}")) ++ ty ++ Vector(Text(" := "), term(let.value))
    }

    private def printBody(body: CoreAst.Term.Body): Vector[Piece] =
      if (body.lets.isEmpty) Vector(term(body.res))
      else
        Vector(Text("{ ")) ++ separated(body.lets.map(let => Later(() => printLet(let))), "\n") ++
          Vector(Text(" \n "), term(body.res), Text(" }"))

    /** Parenthesize loose forms in a position where an operator would bind tighter. */
    private def printTermAtom(value: CoreAst.Term): Vector[Piece] = value match {
      case CoreAst.Term.LocalRef(ref, _) if bound(ref).exists(isLoose) => parens(term(value))
      case _: CoreAst.Term.Ref | _: CoreAst.Term.App | _: CoreAst.Term.Select | _: CoreAst.Term.Sort |
          _: CoreAst.Term.Prop | _: CoreAst.Term.FormOp =>
        Vector(term(value))
      case _: CoreAst.Term.Lam | _: CoreAst.Term.Match | _: CoreAst.Term.Body | _: CoreAst.Term.Pi =>
        parens(term(value))
    }

    private def printCodomain(value: CoreAst.Term): Vector[Piece] = value match {
      case _: CoreAst.Term.Pi => parens(term(value))
      case CoreAst.Term.LocalRef(ref, _) =>
        bound(ref).fold(Vector[Piece](Text(ref.name)))(PrettyPrinter.printCodomain)
      case _ => Vector(term(value))
    }

    def printCoreTerm(value: CoreAst.Term, natural: CoreAst.Term => Option[BigInt]): Vector[Piece] =
      natural(value) match {
        case Some(number) => Vector(Text(number.toString))
        case None         => printNonNumeralTerm(value)
      }

    private def printNonNumeralTerm(value: CoreAst.Term): Vector[Piece] = value match {
      case ref: CoreAst.Term.Ref => Vector(printRef(ref))
      case CoreAst.Term.Lam(tpe, body, _, _, _, recursion, _) =>
        val decrease = recursion.toVector.flatMap(r => Vector(Text(" ")) ++ printDecreaseSpec(r.decreases))
        Vector(Text("fun ")) ++ printBinders(tpe.binders) ++ Vector(Text(": "), term(tpe.out)) ++ decrease ++
          Vector(Text(" => "), term(body))
      case matchTerm: CoreAst.Term.Match       => printMatch(matchTerm)
      case body: CoreAst.Term.Body             => printBody(body)
      case CoreAst.Term.Select(base, field, _) => printTermAtom(base) :+ Text(s"[$field]")
      case CoreAst.Term.App(fn, args, _)       => printTermAtom(fn) ++ argList(args.map(printTermAtomPiece))
      case CoreAst.Term.Pi(binders, out, _, _, _) =>
        val bindersPieces = separated(binders.map(binder => Later(() => printPiBinder(binder))), " -> ")
        bindersPieces ++ Vector(Text(" -> ")) ++ printCodomain(out)
      case CoreAst.Term.Sort(level, _) =>
        val levelField = Option.when(!isForm(level, CoreAst.LevelForm.LevelZero))(term(level))
        printSort("Type", levelField)
      case CoreAst.Term.Prop(_) => Vector(Text("Prop"))
      case CoreAst.Term.FormOp(form, args, _) =>
        Vector(Text(form.qualifiedName)) ++ (if (args.isEmpty) Vector.empty else argList(args.map(term)))
    }

    private def printTermAtomPiece(value: CoreAst.Term): Piece = Later(() => printTermAtom(value))

    private def printCase(c: CoreAst.Case): Vector[Piece] = {
      val argNames = c.argRefs.map(_.name)
      val args = if (argNames.isEmpty) "" else s" ${argNames.mkString(" ")}"
      val ctor = if (c.isFullyQualified) c.ctorName else s".${c.ctorName}"
      Vector(Text(s"| $ctor$args => "), term(c.body))
    }

    def printMatch(matchTerm: CoreAst.Term.Match): Vector[Piece] = {
      val cases = separated(matchTerm.cases.map(c => Later(() => printCase(c))), " ")
      Vector(Text("match ")) ++ printTermAtom(matchTerm.scrut) ++
        Vector(Text(" returning "), term(matchTerm.motive), Text(" with ")) ++ cases
    }
  }

  private val unbound = new SyntaxPrinter(_ => None)

  def printBinder(binder: CoreAst.Binder): String = new Printer().run(unbound.printBinder(binder))

  def printTerm(ast: CoreAst.Ast): String = ast match {
    case term: CoreAst.Term             => new Printer().run(Vector(Term(term, _ => None)))
    case decrease: CoreAst.DecreaseSpec => new Printer().run(unbound.printDecreaseSpec(decrease))
  }

  /** A level in source syntax, with successors rendered without recursively expanding nested levels. */
  private def printLevel(level: Value.Level): Vector[Piece] = {
    def succs(base: String, offset: Int): String =
      if (offset == 0) base else ("Level.succ(" * offset) + base + (")" * offset)

    val terms = level.terms.toVector.sortBy(_._1).map { case (id, offset) =>
      succs(printParameterVar(id, "u"), offset)
    }
    val constant = if (level.c == 0) "Level.zero" else succs("Level.one", level.c - 1)
    val parts = if (level.c > 0 || terms.isEmpty) terms :+ constant else terms
    parts match {
      case Vector(single) => Vector(Text(single))
      case several        => Vector(Text("Level.max(")) ++ separated(several.map(Text), ", ") ++ Vector(Text(")"))
    }
  }

  private def printParameterVar(id: Value.VarId, prefix: String): String =
    FreshVar.parameterName(id).filter(name => name.nonEmpty && name != "_").getOrElse(s"$prefix#$id")

  /** Opens the telescope at fresh variables to print its codomain. */
  private def printPi(pi: Value.VPi): Vector[Piece] = {
    val bodyEnv = telescope.BinderOps.freshen(pi)
    val syntax = new SyntaxPrinter(pi.env.locals.get)
    val binders = separated(pi.binders.map(binder => Later(() => syntax.printPiBinder(binder))), " -> ")
    binders ++ Vector(
      Text(" -> "),
      Later(() => printCodomain(pi.codomain(bodyEnv)))
    )
  }

  /** A function type in codomain position is parenthesized to preserve its binder grouping. */
  private def printCodomain(codomain: Value): Vector[Piece] =
    codomain match {
      case _: Value.VPi => parens(Val(codomain))
      case _            => Vector(Val(codomain))
    }

  /** A variable prints as its binder name; the id only disambiguates the nameless `_`. */
  private def varName(variable: Value.Var): String =
    if (variable.name.nonEmpty && variable.name != "_") variable.name else s"_#${variable.id}"

  private def printLam(lam: Value.VLam): Vector[Piece] =
    lam.id match {
      case Value.ValueId.Const(name) => Vector(Text(name))
      case _: Value.ValueId.LocalId =>
        Vector(Text("fun ")) ++ new SyntaxPrinter(lam.tpe.env.locals.get).printBinders(lam.tpe.binders) ++
          Vector(Text(" => …"))
    }

  /** Whether a match is the direct result of its recursive caller's body. */
  private def blockedCall(thunk: Value.NeutralThunk): Option[Vector[Piece]] = {
    @annotation.tailrec
    def isResult(term: CoreAst.Term): Boolean =
      term match {
        case body: CoreAst.Term.Body       => isResult(body.res)
        case matchTerm: CoreAst.Term.Match => matchTerm.id == thunk.term.id
        case _                             => false
      }

    val callers = thunk.env.locals.valuesIterator.collect {
      case Value.VLam(pi, Value.ValueId.Const(name), Value.LamBody.Core(lam, _)) if isResult(lam.body) => (name, pi)
    }.toVector
    callers match {
      case Vector((name, pi)) =>
        val args = pi.binders.filter(!_.isImplicit).map(binder => thunk.env.locals.get(binder.localRef))
        Option.when(args.forall(_.isDefined))(
          Vector(Text(name)) ++ argList(args.map(arg => Val(arg.get)))
        )
      case _ => None
    }
  }

  /** A stuck projection over a one-constructor family, printed as its field selector call. */
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

  private def printedCall(thunk: Value.NeutralThunk): Option[Vector[Piece]] =
    blockedCall(thunk).orElse(fieldProjection(thunk))

  private final class Printer {
    private val valueNumerals = new java.util.IdentityHashMap[Value, Option[BigInt]]()
    private val termNumerals = new java.util.IdentityHashMap[CoreAst.Term, Option[BigInt]]()
    private val valueLayer: Value => Option[(String, Vector[Value])] = Value.ConstructorForm.unapply
    private val termLayer: CoreAst.Term => Option[(String, Vector[CoreAst.Term])] = {
      case CoreAst.Term.GlobalRef(name, _)                            => Some((name, Vector.empty))
      case CoreAst.Term.App(CoreAst.Term.GlobalRef(name, _), args, _) => Some((name, args))
      case _                                                          => None
    }

    private def naturalValue(value: Value): Option[BigInt] =
      numeral(value, valueLayer, valueNumerals)

    private def naturalTerm(value: CoreAst.Term): Option[BigInt] =
      numeral(value, termLayer, termNumerals)

    def run(pieces: Vector[Piece]): String = {
      val out = new StringBuilder
      val stack = mutable.Stack.empty[Piece]
      def push(expanded: Vector[Piece]): Unit = expanded.reverseIterator.foreach(stack.push)
      push(pieces)
      while (stack.nonEmpty) {
        stack.pop() match {
          case Text(value)        => out.append(value)
          case Val(value)         => push(expandValue(value))
          case Term(value, bound) => push(new SyntaxPrinter(bound).printCoreTerm(value, naturalTerm))
          case Level(value)       => push(printLevel(value))
          case Later(expand)      => push(expand())
        }
      }
      out.result()
    }

    private def expandValue(value: Value): Vector[Piece] =
      naturalValue(value) match {
        case Some(number) => Vector(Text(number.toString))
        case None         => expandNonNumeralValue(value)
      }

    private def expandNonNumeralValue(value: Value): Vector[Piece] = value match {
      case sort: Value.VSort =>
        if (Sorts.isProp(sort)) Vector(Text("Prop"))
        else if (sort.level == Value.Level.zero) Vector(Text("Type"))
        else printSort("Type", Some(Level(sort.level)))
      case level: Value.Level                      => printLevel(level)
      case pi: Value.VPi                           => printPi(pi)
      case Value.VConst(name, _, _)                => Vector(Text(name))
      case Value.ConstructorHead(name, _, _, _, _) => Vector(Text(name))
      case Value.VCtor(head, storedArgs, _) =>
        if (storedArgs.isEmpty) Vector(Text(head.name))
        else Vector(Text(head.name)) ++ argList(storedArgs.map(Val))
      case app: Value.VApp     => printApp(app.head, app.args)
      case lam: Value.VLam     => printLam(lam)
      case variable: Value.Var => Vector(Text(varName(variable)))
      case thunk: Value.NeutralThunk =>
        printedCall(thunk).getOrElse(new SyntaxPrinter(thunk.env.locals.get).printMatch(thunk.term))
      case proof: Value.VProof   => Vector(Text("‹proof of "), Val(proof.tpe), Text("›"))
      case Value.LevelTpe        => Vector(Text("Level"))
      case Value.LevelClassifier => Vector(Text("LevelClassifier"))
      case Value.Large           => Vector(Text("Large"))
    }
  }

  def print(value: Value): String = new Printer().run(Vector(Val(value)))
}
