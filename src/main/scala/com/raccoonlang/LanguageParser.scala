package com.raccoonlang

import com.raccoonlang.Parser._
import com.raccoonlang.SurfaceAst.Decl.{ConstDecl, InductiveDecl}
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

  private val keywords = List("fun", "let", "match", "as", "returning", "with", "inline", "def", "inductive")

  private val ident =
    (P(c => c.isLetter || c == '_') ~ P(c => c.isLetterOrDigit || c == '_' || c == '$' || c == '.').rep(0)).!.filter(
      s => !keywords.contains(s)
    ).named("Ident")

  private def sym(c: Char) = (skipWS ~ P(c) ~/ skipWS).named(s"Sym($c)")
  private def sym(s: String) = (skipWS ~ P(s) ~/ skipWS).named(s"Sym($s)")

  private def kw(s: String) = (skipWS ~ P(s) ~/ wsSep).named(s"Kw($s)")

  // TApp or Ident
  private def typeExpr: Parser[TypeTerm] =
    ident.rep(1, wsSep).map { idents =>
      idents.tail.foldLeft(Ident(idents.head): TypeTerm) { case (curTerm, nextName) => TApp(curTerm, Ident(nextName)) }
    }

  private def param = (sym('(') ~ ident ~ sym(':') ~/ typeTerm ~ sym(')')).map(Binder.tupled)

  private def pi: Parser[Pi] = (param ~ sym("->") ~ typeTerm).map { Pi.tupled }

  private def typeTerm: Parser[TypeTerm] =
    pi |
      (P('$') ~ ident).map(TypeVar) |
      sym('(') ~ typeTerm ~ sym(')') |
      (typeExpr ~ sym("->") ~ typeTerm).map { case (expr, term) => Pi(Binder("_", expr), term) } |
      typeExpr

  private def let: Parser[Let] = (kw("let") ~ ident ~ (sym(':') ~ typeTerm).? ~ sym(":=") ~ term).map {
    case (name, ty, term) => Let(name, ty, term)
  }

  private def body: Parser[Body] =
    (let.rep(0, lineSep) ~ skipOneLine ~ term).map { case (lets, term) => Body(lets, term) }.named("Body")

  private def lambda: Parser[Lam] =
    (kw("fun") ~ param.rep(1, skipWS) ~ sym("=>") ~ body).map(Lam.tupled)

  private def matchCase: Parser[Case] =
    (sym("|") ~ ident ~ wsSep ~ ident.rep(0, wsSep) ~ sym("=>") ~ term ~ lineSep)
      .map(Case.tupled)
      .named("Case")

  private def matchP: Parser[Match] = {
    (kw("match") ~ term ~ kw("as") ~ ident ~ kw("returning") ~ typeTerm ~
      kw("with") ~ lineSep ~ matchCase.rep(1)).map(Match.tupled)
  }

  private def term: Parser[Term] = (lambda | matchP |
    sym("(") ~ term ~ sym(")") |
    ident.map(Ident))
    .rep(1, wsSep)
    .map { terms =>
      terms.tail.foldLeft(terms.head) { case (curTerm, nextTerm) => App(curTerm, nextTerm) }
    }

  private def declHeader: Parser[DeclHeader] = (ident ~ param.rep(0) ~ sym(':') ~ typeTerm).map(DeclHeader.tupled)

  // inline? def foo (a: A)(b : B): C a := body
  private val constP: Parser[ConstDecl] =
    (kw("inline").!.?.map(_.isDefined) ~ kw("def") ~ declHeader ~ (sym(":=") ~ skipOneLine ~ body).?)
      .map(ConstDecl.tupled)

  private def inductiveP: Parser[InductiveDecl] =
    (kw("inductive") ~ declHeader ~ lineSep ~ (sym("|") ~ declHeader ~ lineSep).rep(0)).map(InductiveDecl.tupled)

  private def declP: Parser[Decl] = constP | inductiveP

  private def decls: Parser[Vector[Decl]] = skipAllWs ~ declP.rep(1, lineSep) ~ skipAllWs ~ End

  private def doBlock = kw("do") ~ sym("{") ~ skipOneLine ~ body ~ skipOneLine ~ sym("}")

  private def programP: Parser[Program] = (skipAllWs ~ declP.rep(1, lineSep) ~ skipAllWs ~ doBlock).map(Program.tupled)

  def parseDecls(input: String): ParseResult[Vector[Decl]] = {
    try {
      decls.parse(input, 0)
    } catch {
      case p: ParseError => Failure(p.startIdx, p.curIdx, p.message)
    }
  }

  def parseProgram(input: String): ParseResult[Program] =
    try {
      programP.parse(input, 0)
    } catch {
      case p: ParseError => Failure(p.startIdx, p.curIdx, p.message)
    }

}
