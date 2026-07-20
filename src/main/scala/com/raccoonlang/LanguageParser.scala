package com.raccoonlang

import com.raccoonlang.Parser._
import com.raccoonlang.SurfaceAst.Command.Decl.{AxiomDecl, ConstDecl, InductiveDecl}
import com.raccoonlang.SurfaceAst.Command._
import com.raccoonlang.SurfaceAst.Term._
import com.raccoonlang.SurfaceAst._

object LanguageParser {
  // Whitespace handling
  private val skipWS = CharsWhile(c => c == ' ' || c == '\t').named("SkipWS")
  private val wsSep = P(c => c == ' ' || c == '\t').rep(1).named("WsSep")
  private val comment = P("//") ~ CharsWhile(c => c != '\n')

  private val emptyLine = (skipWS ~ comment.? ~ Exact("\n")).named("EmptyLine")
  private val lineSep = (emptyLine ~ skipWS).named("LineSep")
  private val skipAllWs = (emptyLine.rep(0) ~ skipWS).named("AllWS")
  private val skipOneLine = emptyLine.? ~ skipWS

  private val keywords = List(
    "fun",
    "let",
    "match",
    "as",
    "returning",
    "with",
    "opaque",
    "axiom",
    "def",
    "inductive",
    "struct",
    "namespace",
    "open",
    "import",
    "builtin",
    "decreases",
    "structural",
    "lexicographic",
    "measure",
    "indices",
    "in"
  )

  private val identAtom =
    (P(c => c.isLetter) ~ P(c => c.isLetterOrDigit || c == '_').rep(0)).!.filter(s => !keywords.contains(s))

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
    (P(c => c.isDigit) ~ P(c => c.isDigit).rep(0)).!.map(BigInt(_))
  private def natLitTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    natLitAtom.flatSpanned(sourceId).map(NatLit.tupled)

  private val strLitAtom: Parser[Vector[Int]] = new Parser[Vector[Int]] {
    override def parse(input: String, startIdx: Int): ParseResult[Vector[Int]] = {
      if (startIdx >= input.length || input.charAt(startIdx) != '"') return fail(startIdx, startIdx)
      try {
        val decoded = UnicodeScalarString.decodeQuoted(input, startIdx)
        Success(decoded.scalars, startIdx, decoded.endIdx)
      } catch {
        case invalid: UnicodeScalarString.Invalid =>
          throw ParseError(startIdx, invalid.offset, invalid.message)
      }
    }

    override def toString: String = "StringLiteral"
  }

  private def strLitTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    strLitAtom.flatSpanned(sourceId).map(StrLit.tupled)

  private def pathP: Parser[Vector[String]] = ident.rep(min = 1, sep = P('.'))

  private def openPathP: Parser[(Vector[String], Boolean)] = {
    val rootPath = (rootIdent ~ P('.') ~/ pathP).map { case (_, path) => (path, true) }
    val scopedPath = pathP.map(path => (path, false))
    rootPath | scopedPath
  }

  private def termAtom(implicit sourceId: Option[SourceId]): Parser[Term] =
    (sym("(") ~/ skipAllWs ~ term ~ layoutSymTight(")")) | rootTerm | identTerm | natLitTerm | strLitTerm

  private def parenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    P('(') ~/ skipAllWs ~ arg.rep(0, layoutSym(',')) ~ layoutSymTight(')')

  private def nonEmptyParenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    sym('(') ~/ skipAllWs ~ arg.rep(1, layoutSym(',')) ~ layoutSymTight(')')

  private def simplePi(implicit sourceId: Option[SourceId]): Parser[Pi] =
    (param ~ skipAllWs ~ sym("->") ~/ skipAllWs ~ typeTerm).flatSpanned(sourceId).map { Pi.tupled }

  // Type positions have their own grammar (arrows, no lambdas/matches) but produce ordinary Terms.
  private def typeAtom(implicit sourceId: Option[SourceId]): Parser[Term] =
    simplePi |
      sym('(') ~ skipAllWs ~ typeTerm ~ layoutSymTight(')') |
      rootTerm |
      identTerm |
      natLitTerm |
      strLitTerm

  sealed trait TypeTrailer
  case class Dot(name: String, span: Span) extends TypeTrailer
  case class AppTrailer(args: Vector[Term], span: Span) extends TypeTrailer

  private def typeTrailers(implicit sourceId: Option[SourceId]): Parser[Vector[TypeTrailer]] =
    ((P(".") ~/ identAtom).flatSpanned(sourceId).map(Dot.tupled) |
      nonEmptyParenArgs(typeTerm).flatSpanned(sourceId).map(AppTrailer.tupled)).rep(0)

  private def typeExpr(implicit sourceId: Option[SourceId]): Parser[Term] =
    (typeAtom ~ typeTrailers).map { case (ta, trailers) =>
      trailers.foldLeft(ta) { case (curTerm, nextTrailer) =>
        nextTrailer match {
          case Dot(name, sp)        => Select(curTerm, name, sp)
          case AppTrailer(args, sp) => App(curTerm, args, sp)
        }
      }
    }

  private def typeTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    (typeExpr ~ (skipAllWs ~ sym("->") ~/ skipAllWs ~ typeExpr).rep(0)).flatSpanned(sourceId).map {
      case (first, others, sp) =>
        val pieces = first +: others
        pieces.init.foldRight(pieces.last) { case (lhs, rhs) =>
          Pi(Binder("_", lhs, lhs.span), rhs, sp)
        }
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
    (kw("let") ~/ ident ~ (sym(':') ~ skipAllWs ~ typeTerm).? ~ sym(":=") ~/ skipAllWs ~ term)
      .flatSpanned(sourceId)
      .map { case (name, ty, value, span) =>
        Let(name, ty, value, span)
      }

  private def bodyStmt(implicit sourceId: Option[SourceId]): Parser[BodyStmt] =
    openP.map(OpenStmt.apply) | let.map(LetStmt.apply)

  private def body(implicit sourceId: Option[SourceId]): Parser[Body] = {
    val content = (bodyStmt.rep(0, lineSep) ~ skipOneLine ~ term)
      .map { case (statements, res) =>
        (statements, res)
      }
      .spanned(sourceId)
    (sym("{") ~/ skipOneLine ~ content ~ skipOneLine ~ sym("}"))
      .map { s =>
        Body(s.value._1, s.value._2, s.span)
      }
      .named("Body")
  }

  private def lambda(implicit sourceId: Option[SourceId]): Parser[Term] =
    (kw("fun") ~/ funcHeader ~ sym("=>") ~/ skipAllWs ~ term)
      .flatSpanned(sourceId)
      .map[SurfaceAst.Term] { case (header, body, span) => Lam(header, body, span) }

  private def caseHead: Parser[(Vector[String], Boolean)] = {
    val shortName = (symTight(".") ~/ ident).map(name => (Vector(name), true))
    val globalPath = pathP.map(path => (path, false))
    shortName | globalPath
  }

  private def matchCase(implicit sourceId: Option[SourceId]): Parser[Case] =
    (sym("|") ~/ caseHead ~ (wsSep ~ argName).rep(0) ~ sym("=>") ~/ skipAllWs ~ term ~ lineSep)
      .flatSpanned(sourceId)
      .map { case (ctorPath, useShortName, argNames, body, span) =>
        Case(ctorPath, useShortName, argNames, body, span)
      }
      .named("Case")

  private def matchP(implicit sourceId: Option[SourceId]): Parser[Match] = {
    (kw("match") ~/ term ~ (kw("returning") ~/ typeTerm).? ~
      (kwTight("with") ~/ lineSep) ~ matchCase.rep(0)).flatSpanned(sourceId).map { case (scrut, motive, cases, sp) =>
      Match(scrut, motive, cases, sp)
    }
  }

  sealed trait TermTrailer
  case class TermDot(name: String, span: Span) extends TermTrailer
  case class TermApp(args: Vector[Term], span: Span) extends TermTrailer

  private def termTrailers(implicit sourceId: Option[SourceId]): Parser[Vector[TermTrailer]] =
    ((P(".") ~/ identAtom).flatSpanned(sourceId).map(TermDot.tupled) |
      parenArgs(term).flatSpanned(sourceId).map(TermApp.tupled)).rep(0)

  private def term(implicit sourceId: Option[SourceId]): Parser[Term] =
    ((lambda | matchP | body | simplePi | termAtom) ~ termTrailers).map { case (base, trailers) =>
      trailers.foldLeft(base) {
        case (cur, TermDot(name, sp)) => Select(cur, name, sp)
        case (cur, TermApp(args, sp)) => App(cur, args, sp)
      }
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
      typeTerm ~ lineSep)
      .flatSpanned(sourceId)
      .map { case (name, binders, resTy, sp) =>
        ConstructorDecl(name, binders, resTy, sp)
      }
  }

  private def opaqueP: Parser[Boolean] =
    kw("opaque").!.?.map(_.isDefined)

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

    kw("decreases") ~/ (structural | lexicographic | measure)
  }

  // opaque? def foo (a: A)(c : C): D := body
  private def constP(implicit sourceId: Option[SourceId]): Parser[ConstDecl] =
    (opaqueP ~ kw("def") ~/ declHeader ~ decreasesP.? ~
      (sym(":=") ~/ skipAllWs ~ constBody))
      .flatSpanned(sourceId)
      .map { case (isOpaque, header, decreases, body, span) =>
        ConstDecl(
          isOpaque,
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
    (kw("inductive") ~/ inductiveHeader ~ lineSep ~ ctorDecl.rep(0))
      .flatSpanned(sourceId)
      .map { case (h, cs, sp) => InductiveDecl(h, cs, generateSelectors = false, sp) }

  private def structP(implicit sourceId: Option[SourceId]): Parser[InductiveDecl] =
    (kw("struct") ~/ inductiveHeader ~ lineSep ~ ctorDecl)
      .flatSpanned(sourceId)
      .map { case (h, cs, sp) => InductiveDecl(h, Vector(cs), generateSelectors = true, sp) }

  private def commandP(implicit sourceId: Option[SourceId]): Parser[Command] = declP | namespaceP | openP | blockP

  private def commandsP(implicit sourceId: Option[SourceId]): Parser[Vector[Command]] =
    skipAllWs ~ commandP.rep(0, lineSep.rep(1)) ~ skipAllWs

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

  private def importP(implicit sourceId: Option[SourceId]): Parser[Import] =
    (kw("import") ~/ pathP ~/ emptyLine).flatSpanned(sourceId).map(Import.tupled)

  private def programP(implicit sourceId: Option[SourceId]): Parser[Program] = {
    (skipAllWs ~ importP.rep(0) ~ commandsP ~ term.? ~ skipAllWs ~ End).map(Program.tupled)
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
