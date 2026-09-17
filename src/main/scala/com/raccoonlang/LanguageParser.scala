package com.raccoonlang

import com.raccoonlang.Parser._
import com.raccoonlang.SurfaceAst.Command.Decl.ConstDecl
import com.raccoonlang.SurfaceAst.Command._
import com.raccoonlang.SurfaceAst.Term._
import com.raccoonlang.SurfaceAst._

/** Parser for the base surface language. Later commits extend `commandP` and `term` with additional constructs. */
object LanguageParser {
  private val skipWS = CharsWhile(c => c == ' ' || c == '\t').named("SkipWS")
  private val wsSep = P(c => c == ' ' || c == '\t').rep(1).named("WsSep")
  private val comment = P("//") ~ CharsWhile(c => c != '\n')

  private val emptyLine = (skipWS ~ comment.? ~ Exact("\n")).named("EmptyLine")
  private val lineSep = (emptyLine ~ skipWS).named("LineSep")
  private val skipAllWs = (emptyLine.rep(0) ~ skipWS).named("AllWS")
  private val skipOneLine = emptyLine.? ~ skipWS

  private val identAtom =
    (P(c => IdentifierSyntax.isStart(c)) ~ P(c => IdentifierSyntax.isContinue(c)).rep(0)).!.filter(value =>
      IdentifierSyntax.isAtom(value)
    )

  private val rootName = "_root_"
  private val rootIdent: Parser[String] = P(rootName).!
  private val ident: Parser[String] = identAtom
  private val argName: Parser[String] = ident | P("_").!

  private def sym(c: Char) = (skipWS ~ P(c) ~/ skipWS).named(s"Sym($c)")
  private def sym(s: String) = (skipWS ~ P(s) ~/ skipWS).named(s"Sym($s)")
  private def layoutSym(c: Char) = (skipAllWs ~ P(c) ~/ skipAllWs).named(s"LayoutSym($c)")
  private def layoutSymTight(c: Char) = (skipAllWs ~ P(c)).named(s"LayoutSymTight($c)")
  private def layoutSymTight(s: String) = (skipAllWs ~ P(s)).named(s"LayoutSymTight($s)")

  private def kw(s: String) = (skipWS ~ P(s) ~ wsSep).named(s"Kw($s)")

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

  private def termAtom(implicit sourceId: Option[SourceId]): Parser[Term] =
    (sym("(") ~/ skipAllWs ~ term ~ layoutSymTight(")")) | rootTerm | identTerm | natLitTerm | strLitTerm

  private def parenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    P('(') ~/ skipAllWs ~ arg.rep(0, layoutSym(',')) ~ layoutSymTight(')')

  private def nonEmptyParenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    sym('(') ~/ skipAllWs ~ arg.rep(1, layoutSym(',')) ~ layoutSymTight(')')

  private def simplePi(implicit sourceId: Option[SourceId]): Parser[Pi] =
    (namedSegment.rep(1) ~ typeExpr ~ chainRest).flatSpanned(sourceId).map { case (named, body, rest, sp) =>
      buildChain(named, body, rest, sp) match {
        case pi: Pi => pi
        case _      => throw new IllegalStateException("named binders always form a Pi")
      }
    }

  private def typeAtom(implicit sourceId: Option[SourceId]): Parser[Term] =
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
      trailers.foldLeft(ta) {
        case (curTerm, Dot(name, sp))        => Select(curTerm, name, sp)
        case (curTerm, AppTrailer(args, sp)) => App(curTerm, args, sp)
      }
    }

  private def namedSegment(implicit sourceId: Option[SourceId]): Parser[Vector[Binder]] =
    Attempt(param.rep(1) ~ skipAllWs ~ sym("->") ~ skipAllWs).named("PiBinders")

  private def chainRest(implicit sourceId: Option[SourceId]): Parser[Vector[(Vector[Vector[Binder]], Term)]] =
    (skipAllWs ~ sym("->") ~/ skipAllWs ~ namedSegment.rep(0) ~ typeExpr).rep(0)

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

  private def typeTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    (namedSegment.rep(0) ~ typeExpr ~ chainRest).flatSpanned(sourceId).map { case (named, first, rest, sp) =>
      buildChain(named, first, rest, sp)
    }

  private def normalParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('(') ~ argName ~ sym(':') ~/ skipAllWs ~ typeTerm ~ layoutSymTight(')')).flatSpanned(sourceId).map {
      case (name, ty, span) => Binder(name, ty, span)
    }

  private def implicitParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('{') ~ argName ~ sym(':') ~/ skipAllWs ~ typeTerm ~ layoutSymTight('}')).flatSpanned(sourceId).map {
      case (name, ty, span) => Binder(name, ty, span, isImplicit = true)
    }

  private def param(implicit sourceId: Option[SourceId]): Parser[Binder] = normalParam | implicitParam
  private def layoutParam(implicit sourceId: Option[SourceId]): Parser[Binder] = skipAllWs ~ param

  private def let(implicit sourceId: Option[SourceId]): Parser[Let] =
    (kw("let") ~/ ident ~ (sym(':') ~ skipAllWs ~ typeTerm).? ~ sym(":=") ~/ skipAllWs ~ term)
      .flatSpanned(sourceId)
      .map { case (name, ty, value, span) => Let(name, ty, value, span) }

  private def bodyStmt(implicit sourceId: Option[SourceId]): Parser[BodyStmt] = let.map(LetStmt.apply)

  private def body(implicit sourceId: Option[SourceId]): Parser[Body] = {
    val content = (bodyStmt.rep(0, lineSep) ~ skipOneLine ~ term)
      .map { case (statements, res) =>
        (statements, res)
      }
      .spanned(sourceId)
    (sym("{") ~/ skipOneLine ~ content ~ skipOneLine ~ sym("}"))
      .map(s => Body(s.value._1, s.value._2, s.span))
      .named("Body")
  }

  private def lambda(implicit sourceId: Option[SourceId]): Parser[Term] =
    (kw("fun") ~/ funcHeader ~ sym("=>") ~/ skipAllWs ~ term)
      .flatSpanned(sourceId)
      .map[SurfaceAst.Term] { case (header, body, span) => Lam(header, body, span) }

  sealed trait TermTrailer
  case class TermDot(name: String, span: Span) extends TermTrailer
  case class TermApp(args: Vector[Term], span: Span) extends TermTrailer

  private def termTrailers(implicit sourceId: Option[SourceId]): Parser[Vector[TermTrailer]] =
    ((P(".") ~/ identAtom).flatSpanned(sourceId).map(TermDot.tupled) |
      parenArgs(term).flatSpanned(sourceId).map(TermApp.tupled)).rep(0)

  private def term(implicit sourceId: Option[SourceId]): Parser[Term] =
    ((lambda | body | simplePi | termAtom) ~ termTrailers).map { case (base, trailers) =>
      trailers.foldLeft(base) {
        case (cur, TermDot(name, sp)) => Select(cur, name, sp)
        case (cur, TermApp(args, sp)) => App(cur, args, sp)
      }
    }

  private def funcHeader(implicit sourceId: Option[SourceId]): Parser[FuncHeader] =
    (layoutParam.rep(0) ~ skipAllWs ~ sym(':') ~/ skipAllWs ~ typeTerm).flatSpanned(sourceId).map(FuncHeader.tupled)

  private def declHeader(implicit sourceId: Option[SourceId]): Parser[DeclHeader] =
    (ident ~ funcHeader).flatSpanned(sourceId).map(DeclHeader.tupled)

  private def opaqueP: Parser[Boolean] = kw("opaque").!.?.map(_.isDefined)

  private def constP(implicit sourceId: Option[SourceId]): Parser[ConstDecl] =
    (opaqueP ~ kw("def") ~/ declHeader ~ (sym(":=") ~/ skipAllWs ~ term))
      .flatSpanned(sourceId)
      .map { case (isOpaque, header, body, span) =>
        ConstDecl(isOpaque, header, decreases = None, ConstBody.TermBody(body), span)
      }

  private def declP(implicit sourceId: Option[SourceId]): Parser[Decl] = constP

  private def commandP(implicit sourceId: Option[SourceId]): Parser[Command] = declP

  private def commandsP(implicit sourceId: Option[SourceId]): Parser[Vector[Command]] =
    skipAllWs ~ commandP.rep(0, lineSep.rep(1)) ~ skipAllWs

  private def programP(implicit sourceId: Option[SourceId]): Parser[Program] =
    (skipAllWs ~ commandsP ~ term.? ~ skipAllWs ~ End).map { case (decls, body) => Program(Vector.empty, decls, body) }

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
