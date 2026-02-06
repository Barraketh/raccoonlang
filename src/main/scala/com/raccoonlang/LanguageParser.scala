package com.raccoonlang

import com.raccoonlang.Parser._
import com.raccoonlang.SurfaceAst.Decl.{ConstDecl, InductiveDecl}
import com.raccoonlang.SurfaceAst.Term._
import com.raccoonlang.SurfaceAst._
import com.raccoonlang.Util.NEL

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

  // Type atoms: identifier, type variable, or parenthesized type
  private def typeAtom: Parser[TypeTerm] = sym('(') ~ typeTerm ~ sym(')') | ident.map(Ident)

  // General type application chain: atom atom ... -> TApp(...(atom1 atom2) atom3)
  private def typeExpr: Parser[TypeTerm] =
    typeAtom.rep(1, wsSep).map { atoms =>
      if (atoms.length == 1) atoms.head
      else TApp(atoms.head, NEL.mk(atoms.tail))
    }

  private def param = (sym('(') ~ ident ~ sym(':') ~/ typeTerm ~ sym(')')).map(Binder.tupled)

  private def pi: Parser[Pi] = (param ~ sym("->") ~ typeTerm).map { Pi.tupled }

  private def typeTerm: Parser[TypeTerm] =
    pi |
      sym('(') ~ typeTerm ~ sym(')') |
      (typeExpr ~ sym("->") ~ typeTerm).map { case (expr, term) => Pi(Binder("_", expr), term) } |
      typeExpr

  private def let: Parser[Let] = (kw("let") ~ ident ~ (sym(':') ~ typeTerm).? ~ sym(":=") ~ term).map {
    case (name, ty, term) => Let(name, ty, term)
  }

  private def body: Parser[Body] =
    (let.rep(0, lineSep) ~ skipOneLine ~ term).map { case (lets, term) => Body(lets, term) }.named("Body")

  private def lambda: Parser[Lam] =
    (kw("fun") ~ funcHeader ~ sym("=>") ~ body).map(Lam.tupled)

  private def matchCase: Parser[Case] =
    (sym("|") ~ ident ~ wsSep ~ ident.rep(0, wsSep) ~ sym("=>") ~ term ~ lineSep)
      .map(Case.tupled)
      .named("Case")

  private def matchP: Parser[Match] = {
    (kw("match") ~ term ~ kw("as") ~ ident ~ kw("returning") ~ typeTerm ~
      kw("with") ~ lineSep ~ matchCase.rep(1)).map(Match.tupled)
  }

  private def term: Parser[Term] = (lambda | matchP | sym("(") ~ term ~ sym(")") | ident.map(Ident))
    .rep(1, wsSep)
    .map { terms =>
      if (terms.length == 1) terms.head
      else App(terms.head, NEL.mk(terms.tail))
    }

  private def funcHeader: Parser[FuncHeader] = (param.rep(0) ~ sym(':') ~ typeTerm).map(FuncHeader.tupled)

  private def declHeader: Parser[DeclHeader] = (ident ~ wsSep ~ funcHeader).map(DeclHeader.tupled)

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
