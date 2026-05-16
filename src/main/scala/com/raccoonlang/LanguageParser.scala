package com.raccoonlang

import com.raccoonlang.CoreAst.UnfoldStrategy
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
    "use",
    "match",
    "as",
    "returning",
    "with",
    "inline",
    "axiom",
    "def",
    "instance",
    "derive",
    "inductive",
    "struct",
    "stable",
    "namespace",
    "open",
    "import",
    "builtin",
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

  private def kw(s: String) = (skipWS ~ P(s) ~ wsSep).named(s"Kw($s)")
  private def kwTight(s: String) = (skipWS ~ P(s)).named(s"KwTight($s)")

  private def identTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    ident.flatSpanned(sourceId).map(Ident.tupled)
  private def rootTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    rootIdent.flatSpanned(sourceId).map(Ident.tupled)

  private def pathP: Parser[Vector[String]] = ident.rep(min = 1, sep = P('.'))

  private def openPathP: Parser[(Vector[String], Boolean)] = {
    val rootPath = (rootIdent ~ P('.') ~/ pathP).map { case (_, path) => (path, true) }
    val scopedPath = pathP.map(path => (path, false))
    rootPath | scopedPath
  }

  private def termAtom(implicit sourceId: Option[SourceId]): Parser[Term] = {
    val derive: Parser[Term] =
      (kwTight("derive") ~/ symTight("[") ~/ typeTerm ~ symTight("]")).flatSpanned(sourceId).map(Derive.tupled)
    derive | (sym("(") ~/ term ~ symTight(")")) | rootTerm | identTerm
  }

  // Type atoms: identifier or parenthesized type, with bracket selects as a postfix variant.
  // `$name` captures are parsed only by binder-type pattern parsers below.
  private def identTypeTerm(implicit sourceId: Option[SourceId]): Parser[TypeTerm] =
    ident.flatSpanned(sourceId).map[TypeTerm](Ident.tupled)
  private def rootTypeTerm(implicit sourceId: Option[SourceId]): Parser[TypeTerm] =
    rootIdent.flatSpanned(sourceId).map[TypeTerm](Ident.tupled)

  private def parenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    P('(') ~/ arg.rep(0, sym(',')) ~ symTight(')')

  private def nonEmptyParenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    sym('(') ~/ arg.rep(1, sym(',')) ~ symTight(')')

  private def simplePi(implicit sourceId: Option[SourceId]): Parser[Pi] =
    (param ~ sym("->") ~ typeTerm).flatSpanned(sourceId).map { Pi.tupled }

  private def typeAtom(implicit sourceId: Option[SourceId]): Parser[TypeTerm] =
    simplePi |
      sym('(') ~ typeTerm ~ sym(')') |
      rootTypeTerm |
      identTypeTerm

  sealed trait TypeTrailer
  case class Dot(name: String, span: Span) extends TypeTrailer
  case class AppTrailer(args: Vector[TypeTerm], span: Span) extends TypeTrailer

  private def typeTrailers(implicit sourceId: Option[SourceId]): Parser[Vector[TypeTrailer]] =
    ((P(".") ~/ identAtom).flatSpanned(sourceId).map(Dot.tupled) |
      nonEmptyParenArgs(typeTerm).flatSpanned(sourceId).map(AppTrailer.tupled)).rep(0)

  private def typeExpr(implicit sourceId: Option[SourceId]): Parser[TypeTerm] =
    (typeAtom ~ typeTrailers).map { case (ta, trailers) =>
      trailers.foldLeft(ta) { case (curTypeTerm, nextTrailer) =>
        nextTrailer match {
          case Dot(name, sp)        => TSelect(curTypeTerm, name, sp)
          case AppTrailer(args, sp) => TApp(curTypeTerm, args, sp)
        }
      }
    }

  private def typeTerm(implicit sourceId: Option[SourceId]): Parser[TypeTerm] =
    (typeExpr ~ (sym("->") ~/ typeExpr).rep(0)).flatSpanned(sourceId).map { case (first, others, sp) =>
      val pieces = first +: others
      pieces.init.foldRight(pieces.last: TypeTerm) { case (lhs, rhs) =>
        Pi(Binder("_", BinderType.TypePattern(TypePattern.Type(lhs), lhs.span), lhs.span), rhs, sp)
      }
    }

  private def typePatternCapture(implicit sourceId: Option[SourceId]): Parser[TypePattern.Capture] =
    (symTight("$") ~/ ident).flatSpanned(sourceId).map(TypePattern.Capture.tupled)

  private def typePatternHead(implicit sourceId: Option[SourceId]): Parser[TypeTerm] =
    ((rootTypeTerm | identTypeTerm) ~ (P(".") ~/ identAtom).flatSpanned(sourceId).rep(0)).map { case (base, fields) =>
      fields.foldLeft(base) { case (cur, (field, span)) => TSelect(cur, field, span) }
    }

  private def typePatternApp(implicit sourceId: Option[SourceId]): Parser[TypePattern.App] =
    (typePatternHead ~ nonEmptyParenArgs(typePattern)).flatSpanned(sourceId).map(TypePattern.App.tupled)

  private def topLevelTypePattern(implicit sourceId: Option[SourceId]): Parser[TopLevelTP] =
    typePatternApp | typeTerm.map(TypePattern.Type.apply)

  private def typePattern(implicit sourceId: Option[SourceId]): Parser[TypePattern] =
    typePatternApp | typePatternCapture | typeTerm.map(TypePattern.Type.apply)

  private def constrainedCaptureBinderType(implicit sourceId: Option[SourceId]): Parser[BinderType] =
    (symTight("$") ~/ ident ~ kw("in") ~/ topLevelTypePattern)
      .flatSpanned(sourceId)
      .map { case (name, constraint, span) => BinderType.ConstrainedCapture(name, constraint, span) }

  private def binderType(implicit sourceId: Option[SourceId]): Parser[BinderType] =
    constrainedCaptureBinderType | topLevelTypePattern.map(tp => BinderType.TypePattern(tp, tp.span))

  private def normalParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('(') ~ argName ~ sym(':') ~/ binderType ~ symTight(')')).flatSpanned(sourceId).map { case (name, ty, span) =>
      Binder(name, ty, span)
    }

  private def instanceParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('[') ~ argName ~ sym(':') ~/ binderType ~ symTight(']')).flatSpanned(sourceId).map { case (name, ty, span) =>
      Binder(name, ty, span, isInstance = true)
    }

  private def erasedParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('{') ~ argName ~ sym(':') ~/ binderType ~ symTight('}')).flatSpanned(sourceId).map { case (name, ty, span) =>
      Binder(name, ty, span)
    }

  private def param(implicit sourceId: Option[SourceId]): Parser[Binder] = normalParam | instanceParam

  private def let(implicit sourceId: Option[SourceId]): Parser[Let] =
    (kw("let") ~/ kw("instance").!.? ~ ident ~ (sym(':') ~ typeTerm).? ~ sym(":=") ~ term)
      .flatSpanned(sourceId)
      .map { case (instanceOpt, name, ty, value, span) =>
        Let(name, ty, value, span, isInstance = instanceOpt.isDefined)
      }

  private def useStmt(implicit sourceId: Option[SourceId]): Parser[Use] =
    (kw("use") ~/ term).flatSpanned(sourceId).map(Use.tupled)

  private def bodyStmt(implicit sourceId: Option[SourceId]): Parser[BodyStmt] =
    useStmt.map(UseStmt.apply) | openP.map(OpenStmt.apply) | let.map(LetStmt.apply)

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

  // no longer support `using normalizer` in parser; replaced by `use` statements

  private def lambda(implicit sourceId: Option[SourceId]): Parser[Term] =
    (kw("fun") ~/ funcHeader ~ sym("=>") ~ term)
      .flatSpanned(sourceId)
      .map[SurfaceAst.Term] { case (header, body, span) => Lam(header, body, span) }

  private def caseHead: Parser[(Vector[String], Boolean)] = {
    val shortName = (symTight(".") ~/ ident).map(name => (Vector(name), true))
    val globalPath = pathP.map(path => (path, false))
    shortName | globalPath
  }

  private def matchCase(implicit sourceId: Option[SourceId]): Parser[Case] =
    (sym("|") ~/ caseHead ~ (wsSep ~ argName).rep(0) ~ sym("=>") ~ term ~ lineSep)
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
    (param.rep(0) ~ sym(':') ~ typeTerm).flatSpanned(sourceId).map(FuncHeader.tupled)

  private def declHeader(implicit sourceId: Option[SourceId]): Parser[DeclHeader] =
    (ident ~ funcHeader).flatSpanned(sourceId).map(DeclHeader.tupled)

  // New inductive-specific parsers
  private def inductiveHeader(implicit sourceId: Option[SourceId]): Parser[InductiveHeader] = {
    val bindersP = param.rep(0)
    (ident ~ bindersP ~ sym(':') ~ typeTerm)
      .flatSpanned(sourceId)
      .map { case (name, binders, ty, sp) => InductiveHeader(name, binders, ty, sp) }
  }

  private def ctorDecl(implicit sourceId: Option[SourceId]): Parser[ConstructorDecl] = {
    (sym("|") ~/ ident ~ erasedParam.rep(0) ~ param.rep(0) ~ sym(':') ~ typeTerm ~ lineSep)
      .flatSpanned(sourceId)
      .map { case (name, erasedBinders, fields, resTy, sp) =>
        ConstructorDecl(name, erasedBinders, fields, resTy, sp)
      }
  }

  private def unfoldStrategy: Parser[UnfoldStrategy] =
    kw("inline").!.map(_ => UnfoldStrategy.Inline) | kw("stable").!.map(_ => UnfoldStrategy.Stable)

  private def constBody(implicit sourceId: Option[SourceId]): Parser[ConstBody] =
    kwTight("builtin").!.flatSpanned(sourceId).map { case (_, span) => ConstBody.Builtin(span) } |
      term.map(ConstBody.TermBody.apply)

  // inline? def instance? foo (a: A)[b: B](c : C): D := body
  private def constP(implicit sourceId: Option[SourceId]): Parser[ConstDecl] =
    (unfoldStrategy.? ~ kw("def") ~/ kw("instance").!.? ~ declHeader ~ (sym(":=") ~/ constBody))
      .flatSpanned(sourceId)
      .map { case (unfoldStrategy, instanceOpt, header, body, span) =>
        ConstDecl(unfoldStrategy, header, body, span, isInstance = instanceOpt.isDefined)
      }

  private def axiomP(implicit sourceId: Option[SourceId]): Parser[AxiomDecl] =
    (kw("axiom") ~/ kw("instance").!.? ~ declHeader)
      .flatSpanned(sourceId)
      .map { case (instanceOpt, header, span) =>
        AxiomDecl(header, span, isInstance = instanceOpt.isDefined)
      }

  private def inductiveP(implicit sourceId: Option[SourceId]): Parser[InductiveDecl] =
    (kw("inductive") ~/ inductiveHeader ~ lineSep ~ ctorDecl.rep(0))
      .flatSpanned(sourceId)
      .map { case (h, cs, sp) => InductiveDecl(h, cs, isStruct = false, sp) }

  private def structP(implicit sourceId: Option[SourceId]): Parser[InductiveDecl] =
    (kw("struct") ~/ inductiveHeader ~ lineSep ~ ctorDecl)
      .flatSpanned(sourceId)
      .map { case (h, cs, sp) => InductiveDecl(h, Vector(cs), isStruct = true, sp) }

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
    implicit val sourceId: Option[SourceId] = None
    tryParse(input, programP)
  }

  def parseProgram(input: String, id: SourceId): ParseResult[Program] = {
    implicit val sourceId: Option[SourceId] = Some(id)
    tryParse(input, programP)
  }

}
