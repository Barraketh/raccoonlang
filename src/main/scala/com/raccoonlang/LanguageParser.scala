package com.raccoonlang

import com.raccoonlang.CoreAst.UnfoldStrategy
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

  private val keywords = List(
    "fun",
    "let",
    "use",
    "match",
    "as",
    "returning",
    "with",
    "inline",
    "def",
    "inductive",
    "indices",
    "stable",
    "Sort"
  )

  private val ident =
    (P(c => c.isLetter || c == '_') ~ P(c => c.isLetterOrDigit || c == '_' || c == '$' || c == '.').rep(0)).!.filter(
      s => !keywords.contains(s)
    ).named("Ident")

  private def sym(c: Char) = (skipWS ~ P(c) ~/ skipWS).named(s"Sym($c)")
  private def sym(s: String) = (skipWS ~ P(s) ~/ skipWS).named(s"Sym($s)")
  // Variant that does not consume trailing whitespace; useful before ws-separated reps
  private def symTight(c: Char) = (skipWS ~ P(c)).named(s"SymTight($c)")
  private def symTight(s: String) = (skipWS ~ P(s)).named(s"SymTight($s)")

  private def kw(s: String) = (skipWS ~ P(s) ~/ wsSep).named(s"Kw($s)")

  private def identTerm = ident.flatSpanned.map(Ident.tupled)

  // Type atoms: identifier, type variable, or parenthesized type
  private def typeAtom: Parser[TypeTerm] = sym('(') ~ typeTerm ~ symTight(')') | identTerm

  // General type application chain: atom atom ... -> TApp(...(atom1 atom2) atom3)
  private def typeExpr: Parser[TypeTerm] = {
    (identTerm ~ wsSep ~ typeAtom.rep(1, wsSep)).flatSpanned.map { case (name, args, span) =>
      TApp(name, NEL.mk(args), span)
    } | typeAtom
  }

  private def param = (sym('(') ~ ident ~ sym(':') ~/ typeTerm ~ symTight(')')).flatSpanned.map(Binder.tupled)

  private def pi: Parser[Pi] = (param ~ sym("->") ~ typeTerm).flatSpanned.map { Pi.tupled }

  private def sort: Parser[Sort] = ((kw("Sort") ~/ typeTerm)).flatSpanned.map(Sort.tupled)

  private def typeTerm: Parser[TypeTerm] =
    pi |
      sort |
      sym('(') ~ typeTerm ~ sym(')') |
      (typeExpr.spanned ~ sym("->") ~ typeTerm).spanned.mapAsT { case ((expr, term), span) =>
        Pi(Binder("_", expr.value, expr.span), term, span)
      } |
      typeExpr

  private def let: Parser[Let] = (kw("let") ~ ident ~ (sym(':') ~ typeTerm).? ~ sym(":=") ~ term).flatSpanned.map {
    Let.tupled
  }

  private def useStmt: Parser[Use] = (kw("use") ~/ term).flatSpanned.map(Use.tupled)

  private def body: Parser[Body] = {
    val content = (useStmt.rep(0, lineSep) ~ let.rep(0, lineSep) ~ skipOneLine ~ term).map { case (uses, lets, res) =>
      (uses, lets, res)
    }.spanned
    (sym("{") ~/ skipOneLine ~ content ~ skipOneLine ~ sym("}"))
      .map { s =>
        Body(s.value._1, s.value._2, s.value._3, s.span)
      }
      .named("Body")
  }

  // no longer support `using normalizer` in parser; replaced by `use` statements

  private def lambda: Parser[Term] =
    (kw("fun") ~ funcHeader ~ sym("=>") ~ term).flatSpanned
      .map[SurfaceAst.Term] { case (header, body, span) => Lam(header, body, span) }

  private def matchCase: Parser[Case] =
    (sym("|") ~/ ident ~ (wsSep ~ ident).rep(0) ~ sym("=>") ~ term ~ lineSep).flatSpanned
      .map(Case.tupled)
      .named("Case")

  private def matchP: Parser[Match] = {
    (kw("match") ~/ term ~ kw("as") ~/ ident ~ kw("returning") ~/ typeTerm ~
      (skipWS ~ P("with") ~/ lineSep) ~ matchCase.rep(1)).flatSpanned.map(Match.tupled)
  }

  private def term: Parser[Term] =
    (lambda | matchP | body | sym("(") ~/ term ~ symTight(")") | ident.flatSpanned.map(Ident.tupled))
      .rep(1, wsSep)
      .spanned
      .mapAsT { case (terms, span) =>
        if (terms.length == 1) terms.head
        else App(terms.head, NEL.mk(terms.tail), span)
      }

  private def funcHeader: Parser[FuncHeader] = (param.rep(0) ~ sym(':') ~ typeTerm).flatSpanned.map(FuncHeader.tupled)

  private def declHeader: Parser[DeclHeader] = (ident ~ funcHeader).flatSpanned.map(DeclHeader.tupled)

  // New inductive-specific parsers
  private def inductiveHeader: Parser[InductiveHeader] = {
    val paramsP = param.rep(0)
    val indicesP = (kw("indices") ~/ param.rep(0)).?.map(_.getOrElse(Vector.empty))
    (ident ~ paramsP ~ indicesP ~ sym(':') ~ typeTerm).flatSpanned
      .map { case (name, ps, is, ty, sp) => InductiveHeader(name, ps, is, ty, sp) }
  }

  private def ctorDecl: Parser[ConstructorDecl] = {
    (sym("|") ~/ ident ~ param.rep(0) ~ sym(':') ~ typeTerm ~ lineSep).flatSpanned
      .map { case (name, fields, resTy, sp) => ConstructorDecl(name, fields, resTy, sp) }
  }

  private def unfoldStrategy: Parser[UnfoldStrategy] =
    kw("inline").!.map(_ => UnfoldStrategy.Inline) | kw("stable").!.map(_ => UnfoldStrategy.Stable)

  // inline? def foo (a: A)(b : B): C a := body
  private val constP: Parser[ConstDecl] =
    (unfoldStrategy.? ~ kw("def") ~/ declHeader ~ (sym(":=") ~/ term)).flatSpanned.map(ConstDecl.tupled)

  private def inductiveP: Parser[InductiveDecl] =
    (kw("inductive") ~/ inductiveHeader ~ lineSep ~ ctorDecl.rep(0)).flatSpanned
      .map(InductiveDecl.tupled)

  private def declP: Parser[Decl] = constP | inductiveP

  private def decls: Parser[Vector[Decl]] = skipAllWs ~ declP.rep(1, lineSep) ~ skipAllWs ~ End

  private def programP: Parser[Program] =
    (skipAllWs ~ declP.rep(0, lineSep.rep(1)) ~ skipAllWs ~ term.?).map(Program.tupled)

  private def tryParse[A](input: String, parser: Parser[A]): ParseResult[A] = try {
    parser.parse(input, 0)
  } catch {
    case p: ParseError => Failure(p.startIdx, p.curIdx, p.message)
  }

  def parseFuncHeader(input: String): ParseResult[FuncHeader] = tryParse(input, funcHeader)

  def parseDecls(input: String): ParseResult[Vector[Decl]] = tryParse(input, decls)

  def parseProgram(input: String): ParseResult[Program] = tryParse(input, programP)

}
