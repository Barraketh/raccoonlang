package com.raccoonlang

import com.raccoonlang.CoreAst.UnfoldStrategy
import com.raccoonlang.Parser._
import com.raccoonlang.SurfaceAst.Command.Decl.{ConstDecl, InductiveDecl}
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
    "use",
    "match",
    "as",
    "returning",
    "with",
    "inline",
    "def",
    "instance",
    "derive",
    "inductive",
    "struct",
    "indices",
    "stable",
    "namespace",
    "open",
    "import"
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

  private def kw(s: String) = (skipWS ~ P(s) ~ wsSep).named(s"Kw($s)")
  private def kwTight(s: String) = (skipWS ~ P(s)).named(s"KwTight($s)")

  private def identTerm = ident.flatSpanned.map(Ident.tupled)
  private def rootTerm = rootIdent.flatSpanned.map(Ident.tupled)

  private def pathP: Parser[Vector[String]] = ident.rep(min = 1, sep = P('.'))

  private def openPathP: Parser[(Vector[String], Boolean)] = {
    val rootPath = (rootIdent ~ P('.') ~/ pathP).map { case (_, path) => (path, true) }
    val scopedPath = pathP.map(path => (path, false))
    rootPath | scopedPath
  }

  private def termAtom: Parser[Term] = {
    val derive: Parser[Term] =
      (kwTight("derive") ~/ symTight("[") ~/ typeTerm ~ symTight("]")).flatSpanned.map(Derive.tupled)
    derive | (sym("(") ~/ term ~ symTight(")")) | rootTerm | identTerm
  }

  // Type atoms: identifier, type variable, or parenthesized type, with bracket selects as a postfix variant
  private def capture: Parser[TypeTerm] = (symTight("$") ~/ ident).flatSpanned.map(Capture.tupled)

  private def identTypeTerm: Parser[TypeTerm] = ident.flatSpanned.map[TypeTerm](Ident.tupled)
  private def rootTypeTerm: Parser[TypeTerm] = rootIdent.flatSpanned.map[TypeTerm](Ident.tupled)

  private def parenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    P('(') ~/ arg.rep(0, sym(',')) ~ symTight(')')

  private def nonEmptyParenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    sym('(') ~/ arg.rep(1, sym(',')) ~ symTight(')')

  private def simplePi: Parser[Pi] = (param ~ sym("->") ~ typeTerm).flatSpanned.map { Pi.tupled }

  private def typeAtom: Parser[TypeTerm] =
    simplePi |
      sym('(') ~ typeTerm ~ sym(')') |
      capture |
      rootTypeTerm |
      identTypeTerm

  sealed trait TypeTrailer
  case class Dot(name: String, span: Span) extends TypeTrailer
  case class AppTrailer(args: Vector[TypeTerm], span: Span) extends TypeTrailer

  private def typeTrailers: Parser[Vector[TypeTrailer]] =
    ((P(".") ~/ identAtom).flatSpanned.map(Dot.tupled) |
      nonEmptyParenArgs(typeTerm).flatSpanned.map(AppTrailer.tupled)).rep(0)

  private def typeExpr: Parser[TypeTerm] =
    (typeAtom ~ typeTrailers).map { case (ta, trailers) =>
      trailers.foldLeft(ta) { case (curTypeTerm, nextTrailer) =>
        nextTrailer match {
          case Dot(name, sp) => TSelect(curTypeTerm, name, sp)
          case AppTrailer(args, sp) => TApp(curTypeTerm, args, sp)
        }
      }
    }

  private def typeTerm: Parser[TypeTerm] = (typeExpr ~ (sym("->") ~/ typeExpr).rep(0)).flatSpanned.map {
    case (first, others, sp) =>
      val pieces = first +: others
      pieces.init.foldRight(pieces.last: TypeTerm) { case (lhs, rhs) =>
        Pi(Binder("_", lhs, lhs.span), rhs, sp)
      }
  }

  private def normalParam: Parser[Binder] =
    (sym('(') ~ argName ~ sym(':') ~/ typeTerm ~ symTight(')')).flatSpanned.map { case (name, ty, span) =>
      Binder(name, ty, span)
    }

  private def instanceParam: Parser[Binder] =
    (sym('[') ~ argName ~ sym(':') ~/ typeTerm ~ symTight(']')).flatSpanned.map { case (name, ty, span) =>
      Binder(name, ty, span, isInstance = true)
    }

  private def param: Parser[Binder] = normalParam | instanceParam

  private def let: Parser[Let] =
    (kw("let") ~/ kw("instance").!.? ~ ident ~ (sym(':') ~ typeTerm).? ~ sym(":=") ~ term).flatSpanned.map {
      case (instanceOpt, name, ty, value, span) => Let(name, ty, value, span, isInstance = instanceOpt.isDefined)
    }

  private def useStmt: Parser[Use] = (kw("use") ~/ term).flatSpanned.map(Use.tupled)

  private def bodyStmt: Parser[BodyStmt] =
    useStmt.map(UseStmt.apply) | openP.map(OpenStmt.apply) | let.map(LetStmt.apply)

  private def body: Parser[Body] = {
    val content = (bodyStmt.rep(0, lineSep) ~ skipOneLine ~ term).map { case (statements, res) =>
      (statements, res)
    }.spanned
    (sym("{") ~/ skipOneLine ~ content ~ skipOneLine ~ sym("}"))
      .map { s =>
        Body(s.value._1, s.value._2, s.span)
      }
      .named("Body")
  }

  // no longer support `using normalizer` in parser; replaced by `use` statements

  private def lambda: Parser[Term] =
    (kw("fun") ~/ funcHeader ~ sym("=>") ~ term).flatSpanned
      .map[SurfaceAst.Term] { case (header, body, span) => Lam(header, body, span) }

  private def caseHead: Parser[(Vector[String], Boolean)] = {
    val shortName = (symTight(".") ~/ ident).map(name => (Vector(name), true))
    val globalPath = pathP.map(path => (path, false))
    shortName | globalPath
  }

  private def matchCase: Parser[Case] =
    (sym("|") ~/ caseHead ~ (wsSep ~ argName).rep(0) ~ sym("=>") ~ term ~ lineSep).flatSpanned
      .map { case (ctorPath, useShortName, argNames, body, span) =>
        Case(ctorPath, useShortName, argNames, body, span)
      }
      .named("Case")

  private def matchP: Parser[Match] = {
    (kw("match") ~/ term ~ (kw("returning") ~/ typeTerm).? ~
      (kwTight("with") ~/ lineSep) ~ matchCase.rep(0)).flatSpanned.map { case (scrut, motive, cases, sp) =>
      Match(scrut, motive, cases, sp)
    }
  }

  sealed trait TermTrailer
  case class TermDot(name: String, span: Span) extends TermTrailer
  case class TermApp(args: Vector[Term], span: Span) extends TermTrailer

  private def termTrailers: Parser[Vector[TermTrailer]] =
    ((P(".") ~/ identAtom).flatSpanned.map(TermDot.tupled) |
      parenArgs(term).flatSpanned.map(TermApp.tupled)).rep(0)

  private def term: Parser[Term] =
    ((lambda | matchP | body | simplePi | termAtom) ~ termTrailers).map {
      case (base, trailers) =>
        trailers.foldLeft(base) {
          case (cur, TermDot(name, sp))  => Select(cur, name, sp)
          case (cur, TermApp(args, sp)) => App(cur, args, sp)
        }
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

  // inline? def instance? foo (a: A)[b: B](c : C): D := body
  private val constP: Parser[ConstDecl] =
    (unfoldStrategy.? ~ kw("def") ~/ kw("instance").!.? ~ declHeader ~ (sym(":=") ~/ term)).flatSpanned.map {
      case (unfoldStrategy, instanceOpt, header, body, span) =>
        ConstDecl(unfoldStrategy, header, body, span, isInstance = instanceOpt.isDefined)
    }

  private def inductiveP: Parser[InductiveDecl] =
    (kw("inductive") ~/ inductiveHeader ~ lineSep ~ ctorDecl.rep(0)).flatSpanned
      .map { case (h, cs, sp) => InductiveDecl(h, cs, isStruct = false, sp) }

  private def structP: Parser[InductiveDecl] =
    (kw("struct") ~/ inductiveHeader ~ lineSep ~ ctorDecl).flatSpanned
      .map { case (h, cs, sp) => InductiveDecl(h, Vector(cs), isStruct = true, sp) }

  private def commandP: Parser[Command] = declP | namespaceP | openP | blockP

  private def commandsP: Parser[Vector[Command]] = skipAllWs ~ commandP.rep(0, lineSep.rep(1)) ~ skipAllWs

  private def declP: Parser[Decl] = constP | inductiveP | structP

  private def namespaceP: Parser[Namespace] =
    (kw("namespace") ~/ pathP ~ sym('{') ~/ commandsP ~ symTight('}')).flatSpanned.map {
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

  private def openP: Parser[Open] =
    (kw("open") ~/ openPathP ~ openRulesP.?).flatSpanned.map { case (path, root, rules, span) =>
      Open(path, root, rules.getOrElse(Vector(AliasRule.Wildcard)), span)
    }

  private def blockP: Parser[Block] =
    (sym("{") ~ commandsP ~ symTight("}")).flatSpanned.map(Block.tupled)

  private def importP: Parser[Import] =
    (kw("import") ~/ pathP ~/ emptyLine).flatSpanned.map(Import.tupled)

  private def programP: Parser[Program] = {
    (skipAllWs ~ importP.rep(0) ~ commandsP ~ term.? ~ skipAllWs ~ End).map(Program.tupled)
  }

  private def tryParse[A](input: String, parser: Parser[A]): ParseResult[A] = try {
    parser.parse(input, 0)
  } catch {
    case p: ParseError => Failure(p.startIdx, p.curIdx, p.message)
  }

  def parseFuncHeader(input: String): ParseResult[FuncHeader] = tryParse(input, funcHeader)

  def parseProgram(input: String): ParseResult[Program] = tryParse(input, programP)

}
