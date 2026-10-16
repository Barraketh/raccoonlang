package com.raccoonlang

import com.raccoonlang.Parser._
import com.raccoonlang.SurfaceAst.Command.Decl.{AxiomDecl, ConstDecl, InductiveDecl}
import com.raccoonlang.SurfaceAst.Command._
import com.raccoonlang.SurfaceAst.Term._
import com.raccoonlang.SurfaceAst._

object LanguageParser {
  // Whitespace handling
  private val skipWS = CharsWhile(c => c == ' ' || c == '\t').named("SkipWS")
  private val wsSep = P("WS", c => c == ' ' || c == '\t').rep(1).named("WsSep")
  private val comment = P("//") ~ CharsWhile(c => c != '\n')

  private val emptyLine = (skipWS ~ comment.? ~ Exact("\n")).named("EmptyLine")
  private val skipAllWs = (emptyLine.rep(0) ~ skipWS).named("AllWS")

  /** A list separator may contain any number of blank or comment-only lines. Items leave it to their list. */
  private val lineSep = (emptyLine.rep(1) ~ skipWS).named("LineSep")

  /** Check that an item ends its line without consuming the break owned by its enclosing list. */
  private val lineEnd: Parser[NoValue.type] = new Parser[NoValue.type] {
    private val rest = skipWS ~ comment.?

    override def parse(input: String, startIdx: Int): ParseResult[NoValue.type] =
      rest.parse(input, startIdx) match {
        case Success(_, _, endIdx) if endIdx == input.length || input.charAt(endIdx) == '\n' =>
          Success(NoValue, startIdx, startIdx)
        case _ => fail(startIdx, startIdx)
      }

    override def toString: String = "end of line"
  }

  private val wordAtom =
    (P("Word", c => IdentifierSyntax.isStart(c)) ~ P("WordPart", c => IdentifierSyntax.isContinue(c)).rep(0)).!
  private val identAtom = wordAtom.filter("Identifier", value => IdentifierSyntax.isAtom(value))

  private val rootName = "_root_"
  private val rootIdent: Parser[String] = P(rootName).!
  private val ident: Parser[String] = identAtom

  private val argName: Parser[String] = ident | P("_").!

  private def sym(c: Char) = (skipWS ~ P(c) ~/ skipWS).named(s"Sym($c)")
  private def sym(s: String) = (skipWS ~ P(s) ~/ skipWS).named(s"Sym($s)")

  // Variant that does not consume trailing whitespace; useful before ws-separated reps
  private def symTight(c: Char) = (skipWS ~ P(c)).named(s"SymTight($c)")
  private def symTight(s: String) = (skipWS ~ P(s)).named(s"SymTight($s)")
  private def layoutSym(c: Char) = (skipAllWs ~ P(c) ~/ skipAllWs).named(s"LayoutSym($c)")
  private def layoutSymTight(c: Char) = (skipAllWs ~ P(c)).named(s"LayoutSymTight($c)")
  private def layoutSymTight(s: String) = (skipAllWs ~ P(s)).named(s"LayoutSymTight($s)")

  private def kw(s: String) = (skipWS ~ P(s) ~ wsSep).named(s"Kw($s)")
  private def kwTight(s: String) = (skipWS ~ P(s)).named(s"KwTight($s)")

  private def identTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    ident.flatSpanned(sourceId).map(Ident.tupled)
  private def rootTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    rootIdent.flatSpanned(sourceId).map(Ident.tupled)
  private val natLitAtom: Parser[BigInt] =
    (P("Digit", c => c.isDigit) ~ P("Digit", c => c.isDigit).rep(0)).!.map(BigInt(_))
  private def natLitTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    natLitAtom.flatSpanned(sourceId).map(NatLit.tupled)

  private def pathP: Parser[Vector[String]] = ident.rep(min = 1, sep = P('.'))

  private def openPathP: Parser[(Vector[String], Boolean)] = {
    val rootPath = (rootIdent ~ P('.') ~/ pathP).map { case (_, path) => (path, true) }
    val scopedPath = pathP.map(path => (path, false))
    rootPath | scopedPath
  }

  private def termAtom(implicit sourceId: Option[SourceId]): Parser[Term] =
    (sym("(") ~/ skipAllWs ~ term ~ layoutSymTight(")")) | rootTerm | identTerm | typeFormer | propFormer | natLitTerm

  /** The only field accepted by Type. */
  private val typeFieldNames: Set[String] = Set("level")

  private def typeField(implicit sourceId: Option[SourceId]): Parser[(String, Term, Span)] =
    (wordAtom ~ sym('=') ~/ skipAllWs ~ term).flatSpanned(sourceId)

  /** A Type field list `{ level = e }` as written, with its span. */
  private def typeFieldList(implicit sourceId: Option[SourceId]): Parser[(Vector[(String, Term, Span)], Span)] =
    (P('{') ~/ skipAllWs ~ typeField.rep(0, layoutSym(',')) ~ layoutSymTight('}'))
      .flatSpanned(sourceId)
      .named("TypeFieldList")

  /**
   * A written Type field list's fields by name. An empty list, an unknown or repeated field is a parse error, with the
   * first error in source order reported.
   */
  private def typeFieldsByName(
      written: (Vector[(String, Term, Span)], Span)
  ): Map[String, Term] = {
    val (fields, span) = written
    if (fields.isEmpty) throw ParseError(span.start, span.start, "Empty field list")
    fields.foldLeft(Map.empty[String, Term]) { case (seen, (name, value, fieldSpan)) =>
      def reject(message: String): Nothing = throw ParseError(fieldSpan.start, fieldSpan.start, message)
      if (!typeFieldNames(name)) reject(s"Unknown field $name")
      if (seen.contains(name)) reject(s"Repeated field $name")
      seen + (name -> value)
    }
  }

  /** Type defaults to the first data universe; a written level is elaborated as a Level term. */
  private def typeFormer(implicit sourceId: Option[SourceId]): Parser[Term] =
    (wordAtom.filter("Type", _ == "Type") ~ (skipWS ~ typeFieldList).?).flatSpanned(sourceId).map {
      case (_, written, span) =>
        val fields = written.fold(Map.empty[String, Term])(typeFieldsByName)
        Type(fields.get("level"), span)
    }

  /** Prop is a bare former. Consume a following field list so it receives a direct syntax error. */
  private def propFormer(implicit sourceId: Option[SourceId]): Parser[Term] =
    (wordAtom.filter("Prop", _ == "Prop") ~ (skipWS ~ typeFieldList).?).flatSpanned(sourceId).map {
      case (_, Some((_, fieldListSpan)), _) =>
        throw ParseError(fieldListSpan.start, fieldListSpan.start, "Prop does not accept fields")
      case (_, None, span) => Prop(span)
    }

  private def parenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    P('(') ~/ skipAllWs ~ arg.rep(0, layoutSym(',')) ~ layoutSymTight(')')

  private def nonEmptyParenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    sym('(') ~/ skipAllWs ~ arg.rep(1, layoutSym(',')) ~ layoutSymTight(')')

  /**
   * A Pi written in *term* position. It must start with NAMED binders (`(a: A) -> ...`, `(a: A)(b: B) -> ...`): an
   * anonymous chain like `A -> B` would otherwise make this alternative compete with ordinary terms, since its first
   * segment is just a term. Adjacent param groups before one arrow are one binder group, as in a def's header.
   */
  private def simplePi(implicit sourceId: Option[SourceId]): Parser[Pi] =
    (namedSegment.rep(1) ~ typeExpr ~ chainRest).flatSpanned(sourceId).map { case (named, body, rest, sp) =>
      buildChain(named, body, rest, sp) match {
        case pi: Pi => pi
        case other  => at(other.span) { wtf("named binders always form a Pi") }
      }
    }

  // Type positions have their own grammar (arrows, no lambdas/matches) but produce ordinary Terms.
  // A parenthesised type is an ATOM: `((b: B) -> C)` stays a nested Pi rather than merging into an
  // enclosing arrow chain, because grouping is part of a function type's identity.
  private def typeAtom(implicit sourceId: Option[SourceId]): Parser[Term] =
    sym('(') ~ skipAllWs ~ typeTerm ~ layoutSymTight(')') |
      rootTerm |
      identTerm |
      typeFormer |
      propFormer |
      natLitTerm

  /**
   * A trailer's term covers its base as well as the trailer: an application its head, and a selection the path it
   * extends. So a diagnostic about `Nat.add(…)` underlines the whole call, from `Nat`.
   */
  private def trailerSpan(base: Term, trailer: Span): Span = trailer.copy(start = base.span.start)

  private sealed trait Trailer
  private final case class Dot(name: String, span: Span) extends Trailer
  private final case class Apply(args: Vector[Term], span: Span) extends Trailer

  private def trailers(args: => Parser[Vector[Term]])(implicit sourceId: Option[SourceId]): Parser[Vector[Trailer]] =
    ((P(".") ~/ identAtom).flatSpanned(sourceId).map[Trailer] { case (name, span) => Dot(name, span) } |
      args.flatSpanned(sourceId).map[Trailer] { case (args, span) => Apply(args, span) }).rep(0)

  private def foldTrailers(base: Term, trailers: Vector[Trailer]): Term =
    trailers.foldLeft(base) {
      case (cur, Dot(name, span))   => Select(cur, name, trailerSpan(cur, span))
      case (cur, Apply(args, span)) => App(cur, args, trailerSpan(cur, span))
    }

  private def typeExpr(implicit sourceId: Option[SourceId]): Parser[Term] =
    (typeAtom ~ trailers(nonEmptyParenArgs(typeTerm))).map { case (base, next) => foldTrailers(base, next) }

  /**
   * Named binder groups that open an arrow chain: `(a: A) ->`, `(a: A)(b: B) ->`. A binder commits once its `(name :`
   * or `{name :` is read, since nothing else in a type or term starts that way: a parenthesised type or term cannot be
   * a name followed by a colon. An error inside a binder's type is reported as itself.
   */
  private def namedSegment(implicit sourceId: Option[SourceId]): Parser[Vector[Binder]] =
    (param.rep(1) ~ skipAllWs ~ sym("->") ~ skipAllWs).named("PiBinders")

  /** The arrow-separated pieces after the first: each is leading named segments plus one type, parsed ONCE. */
  private def chainRest(implicit sourceId: Option[SourceId]): Parser[Vector[(Vector[Vector[Binder]], Term)]] =
    (skipAllWs ~ sym("->") ~/ skipAllWs ~ namedSegment.rep(0) ~ typeExpr).rep(0)

  /**
   * Fold an arrow chain into ONE binder group. Every piece but the last contributes its named binders and then an
   * anonymous binder for its type; the last piece contributes only its named binders, and its type is the body.
   */
  private def buildChain(
      named: Vector[Vector[Binder]],
      first: Term,
      rest: Vector[(Vector[Vector[Binder]], Term)],
      sp: Span
  ): Term = {
    val pieces = (named, first) +: rest
    val binders =
      pieces.init.flatMap { case (groups, domain) => groups.flatten :+ Binder("_", domain, domain.span) } ++
        pieces.last._1.flatten
    if (binders.isEmpty) pieces.last._2 else Pi(binders, pieces.last._2, sp)
  }

  /**
   * An arrow chain is ONE binder group: `A -> B -> C` and `(a: A) -> (b: B) -> C` are 2-ary function types, not nested
   * 1-ary ones. Nesting is written with parentheses — `(a: A) -> ((b: B) -> C)` — where the body is a parenthesised
   * atom and stays its own Pi. Grouping is part of a function type's identity (docs/kernel.md#definitional-equality),
   * so this is the only place the grouping of a written type is decided. Each type in the chain is parsed exactly once:
   * the arrow is looked for only after a piece has been read, never by speculatively re-parsing it as a domain.
   */
  private def typeTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    (namedSegment.rep(0) ~ typeExpr ~ chainRest).flatSpanned(sourceId).map { case (named, first, rest, sp) =>
      buildChain(named, first, rest, sp)
    }

  private def normalParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('(') ~ argName ~ sym(':') ~/ skipAllWs ~ typeTerm ~ layoutSymTight(')')).flatSpanned(sourceId).map {
      case (name, ty, span) =>
        Binder(name, ty, span)
    }

  private def implicitParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('{') ~ argName ~ sym(':') ~/ skipAllWs ~ typeTerm ~ layoutSymTight('}')).flatSpanned(sourceId).map {
      case (name, ty, span) =>
        Binder(name, ty, span, isImplicit = true)
    }

  private def param(implicit sourceId: Option[SourceId]): Parser[Binder] =
    normalParam | implicitParam
  private def layoutParam(implicit sourceId: Option[SourceId]): Parser[Binder] = skipAllWs ~ param

  private def let(implicit sourceId: Option[SourceId]): Parser[Let] =
    (kw("let") ~/ argName ~ (sym(':') ~ skipAllWs ~ typeTerm).? ~ sym(":=") ~/ skipAllWs ~ term)
      .flatSpanned(sourceId)
      .map { case (name, ty, value, span) =>
        Let(name, ty, value, span)
      }

  private def bodyStmt(implicit sourceId: Option[SourceId]): Parser[BodyStmt] =
    openP.map(OpenStmt.apply) | let.map(LetStmt.apply)

  private def body(implicit sourceId: Option[SourceId]): Parser[Body] = {
    val content = (bodyStmt.rep(0, lineSep) ~ skipAllWs ~ term)
      .map { case (statements, res) =>
        (statements, res)
      }
      .spanned(sourceId)
    (sym("{") ~/ skipAllWs ~ content ~ skipAllWs ~ sym("}"))
      .map { s =>
        Body(s.value._1, s.value._2, s.span)
      }
      .named("Body")
  }

  private def lambda(implicit sourceId: Option[SourceId]): Parser[Term] =
    (kw("fun") ~/ funcHeader ~ sym("=>") ~/ skipAllWs ~ term)
      .flatSpanned(sourceId)
      .map[SurfaceAst.Term] { case (header, body, span) =>
        if (header.params.isEmpty) throw ParseError(header.span.start, header.span.start, "A lambda binds a parameter")
        Lam(header, body, span)
      }

  private def caseHead: Parser[(Vector[String], Boolean)] = {
    val shortName = (symTight(".") ~/ ident).map(name => (Vector(name), true))
    val globalPath = pathP.map(path => (path, false))
    shortName | globalPath
  }

  private def matchCase(implicit sourceId: Option[SourceId]): Parser[Case] = {
    val patternVar = argName.spanned(sourceId).map(name => PatternVar(name.value, name.span))
    (sym("|") ~/ caseHead ~ (wsSep ~ patternVar).rep(0) ~ sym("=>") ~/ skipAllWs ~ term ~ lineEnd)
      .flatSpanned(sourceId)
      .map { case (ctorPath, useShortName, patternVars, body, span) =>
        Case(ctorPath, useShortName, patternVars, body, span)
      }
      .named("Case")
  }

  /** `returning` continues the header, so it may start the next line, as an arrow or a parameter group may. */
  private def matchP(implicit sourceId: Option[SourceId]): Parser[Match] = {
    (kw("match") ~/ term ~ (skipAllWs ~ kw("returning") ~/ typeTerm).named("returning clause") ~
      kwTight("with") ~/ lineEnd ~ (lineSep ~ matchCase).rep(0))
      .flatSpanned(sourceId)
      .map { case (scrut, motive, cases, sp) => Match(scrut, motive, cases, sp) }
  }

  private def term(implicit sourceId: Option[SourceId]): Parser[Term] =
    ((lambda | matchP | body | simplePi | termAtom) ~ trailers(parenArgs(term))).map { case (base, next) =>
      foldTrailers(base, next)
    }

  private def funcHeader(implicit sourceId: Option[SourceId]): Parser[FuncHeader] =
    (layoutParam.rep(0) ~ skipAllWs ~ sym(':') ~/ skipAllWs ~ typeTerm).flatSpanned(sourceId).map(FuncHeader.tupled)

  private def declHeader(implicit sourceId: Option[SourceId]): Parser[DeclHeader] =
    (ident ~ funcHeader).flatSpanned(sourceId).map(DeclHeader.tupled)

  // New inductive-specific parsers
  private def inductiveHeader(implicit sourceId: Option[SourceId]): Parser[InductiveHeader] = {
    val paramsP = layoutParam.rep(0)
    val indicesP = (kw("indices") ~/ layoutParam.rep(0)).?.map(_.getOrElse(Vector.empty))
    (ident ~ paramsP ~ indicesP ~ skipAllWs ~ sym(':') ~/ skipAllWs ~ typeTerm)
      .flatSpanned(sourceId)
      .map { case (name, params, indices, ty, sp) => InductiveHeader(name, params, indices, ty, sp) }
  }

  private def ctorDecl(implicit sourceId: Option[SourceId]): Parser[ConstructorDecl] = {
    (sym("|") ~/ ident ~ layoutParam.rep(0) ~ skipAllWs ~ sym(':') ~/ skipAllWs ~
      typeTerm ~ lineEnd)
      .flatSpanned(sourceId)
      .map { case (name, binders, resTy, sp) =>
        ConstructorDecl(name, binders, resTy, sp)
      }
  }

  private def constBody(implicit sourceId: Option[SourceId]): Parser[ConstBody] =
    kwTight("builtin").!.flatSpanned(sourceId).map { case (_, span) => ConstBody.Builtin(span) } |
      term.map(ConstBody.TermBody.apply)

  private def decreasesP(implicit sourceId: Option[SourceId]): Parser[DecreaseSpec] = {
    val structural =
      (kwTight("structural") ~/ symTight("(") ~/ ident ~ symTight(")"))
        .flatSpanned(sourceId)
        .map { case (arg, span) => DecreaseSpec.Structural(arg, span) }

    val lexicographic =
      (kwTight("lexicographic") ~/ symTight("(") ~/ ident.rep(1, sym(",")) ~ symTight(")"))
        .flatSpanned(sourceId)
        .map { case (args, span) => DecreaseSpec.Lexicographic(args, span) }

    val measure =
      (kwTight("measure") ~/ symTight("(") ~/ term ~ symTight(")"))
        .flatSpanned(sourceId)
        .map { case (measureTerm, span) => DecreaseSpec.Measure(measureTerm, span) }

    val keyword = (skipWS ~ P("decreases") ~ (lineSep | wsSep)).named("Kw(decreases)")
    keyword ~/ (structural | lexicographic | measure).named("structural(x), lexicographic(x, ...) or measure(e)")
  }

  /** A decrease clause continues the definition header, so it may start on a later line. */
  private def constP(implicit sourceId: Option[SourceId]): Parser[ConstDecl] =
    (kw("def") ~/ declHeader ~ (skipAllWs ~ decreasesP).? ~
      (sym(":=") ~/ skipAllWs ~ constBody))
      .flatSpanned(sourceId)
      .map { case (header, decreases, body, span) =>
        ConstDecl(
          header,
          decreases,
          body,
          span
        )
      }

  private def axiomP(implicit sourceId: Option[SourceId]): Parser[AxiomDecl] =
    (kw("axiom") ~/ declHeader)
      .flatSpanned(sourceId)
      .map { case (header, span) =>
        AxiomDecl(header, span)
      }

  private def inductiveP(implicit sourceId: Option[SourceId]): Parser[InductiveDecl] =
    (kw("inductive") ~/ inductiveHeader ~ lineEnd ~ (lineSep ~ ctorDecl).rep(0))
      .flatSpanned(sourceId)
      .map { case (h, cs, sp) => InductiveDecl(h, cs, generateSelectors = false, sp) }

  private def structP(implicit sourceId: Option[SourceId]): Parser[InductiveDecl] =
    (kw("struct") ~/ inductiveHeader ~ lineEnd ~ lineSep ~ ctorDecl)
      .flatSpanned(sourceId)
      .map { case (h, cs, sp) => InductiveDecl(h, Vector(cs), generateSelectors = true, sp) }

  private def commandP(implicit sourceId: Option[SourceId]): Parser[Command] =
    declP | namespaceP | openP | mutualP | blockP

  private def commandsP(implicit sourceId: Option[SourceId]): Parser[Vector[Command]] =
    skipAllWs ~ commandP.rep(0, lineSep) ~ skipAllWs

  private def declP(implicit sourceId: Option[SourceId]): Parser[Decl] = constP | axiomP | inductiveP | structP

  private def namespaceP(implicit sourceId: Option[SourceId]): Parser[Namespace] =
    (kw("namespace") ~/ pathP ~ sym('{') ~/ commandsP ~ symTight('}')).flatSpanned(sourceId).map {
      case (path, commands, span) => Namespace(path, commands, span)
    }

  private def aliasRuleP: Parser[AliasRule] = {
    val wildcard = symTight("*").map(_ => AliasRule.Wildcard)
    val exclude = (symTight("-") ~/ ident).map(AliasRule.Exclude.apply)
    val include = (ident ~ (kw("as") ~/ ident).?).map { case (name, as) => AliasRule.Include(name, as) }
    wildcard | exclude | include
  }

  private def openRulesP: Parser[Vector[AliasRule]] =
    symTight(".") ~/ symTight("{") ~/ aliasRuleP.rep(1, sym(",")) ~ symTight("}")

  private def openP(implicit sourceId: Option[SourceId]): Parser[Open] =
    (kw("open") ~/ openPathP ~ openRulesP.?).flatSpanned(sourceId).map { case (path, root, rules, span) =>
      Open(path, root, rules.getOrElse(Vector(AliasRule.Wildcard)), span)
    }

  private def blockP(implicit sourceId: Option[SourceId]): Parser[Block] =
    (sym("{") ~ commandsP ~ symTight("}")).flatSpanned(sourceId).map(Block.tupled)

  /** Mutual groups use the ordinary command-block layout and are lowered atomically by the elaborator. */
  private def mutualP(implicit sourceId: Option[SourceId]): Parser[Mutual] =
    (kw("mutual") ~/ skipAllWs ~ sym("{") ~ commandsP ~ symTight("}"))
      .flatSpanned(sourceId)
      .map(Mutual.tupled)

  private def importP(implicit sourceId: Option[SourceId]): Parser[Import] =
    (kw("import") ~/ pathP ~/ lineEnd).flatSpanned(sourceId).map(Import.tupled)

  private def programP(implicit sourceId: Option[SourceId]): Parser[Program] = {
    (skipAllWs ~ importP.rep(0, lineSep) ~ commandsP ~ term.? ~ skipAllWs ~/ End).map(Program.tupled)
  }

  private def tryParse[A](input: String, parser: Parser[A]): ParseResult[A] = try {
    parser.parse(input, 0)
  } catch {
    case p: ParseError => Failure(p.startIdx, p.curIdx, p.message)
  }

  def parseFuncHeader(input: String): ParseResult[FuncHeader] = {
    implicit val sourceId: Option[SourceId] = None
    tryParse(input, funcHeader)
  }

  def parseProgram(input: String): ParseResult[Program] = {
    implicit val sourceId: Option[SourceId] = Some(SourceId.fresh())
    tryParse(input, programP)
  }

  def parseProgram(input: String, id: SourceId): ParseResult[Program] = {
    implicit val sourceId: Option[SourceId] = Some(id)
    tryParse(input, programP)
  }

}
