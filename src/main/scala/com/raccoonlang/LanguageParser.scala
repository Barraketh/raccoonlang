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
    "opaque",
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
    "decreases",
    "structural",
    "lexicographic",
    "measure",
    "indices",
    "of"
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

  private def pathP: Parser[Vector[String]] = ident.rep(min = 1, sep = P('.'))

  private def openPathP: Parser[(Vector[String], Boolean)] = {
    val rootPath = (rootIdent ~ P('.') ~/ pathP).map { case (_, path) => (path, true) }
    val scopedPath = pathP.map(path => (path, false))
    rootPath | scopedPath
  }

  private def deriveP(implicit sourceId: Option[SourceId]): Parser[Derive] =
    (kwTight("derive") ~/ symTight("[") ~/ skipAllWs ~ typePositionTerm ~ layoutSymTight("]"))
      .flatSpanned(sourceId)
      .map(Derive.tupled)

  private def termAtom(implicit sourceId: Option[SourceId]): Parser[Term] =
    deriveP | (sym("(") ~/ skipAllWs ~ term ~ layoutSymTight(")")) | rootTerm | identTerm

  // Type-position expressions use the same term AST, but keep a separate parser to preserve arrow precedence.
  // `$name` captures are parsed only by binder-type pattern parsers below.
  private def identTypeExpr(implicit sourceId: Option[SourceId]): Parser[Term] =
    ident.flatSpanned(sourceId).map(Ident.tupled)
  private def rootTypeExpr(implicit sourceId: Option[SourceId]): Parser[Term] =
    rootIdent.flatSpanned(sourceId).map(Ident.tupled)

  private def parenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    P('(') ~/ skipAllWs ~ arg.rep(0, layoutSym(',')) ~ layoutSymTight(')')

  private def nonEmptyParenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    sym('(') ~/ skipAllWs ~ arg.rep(1, layoutSym(',')) ~ layoutSymTight(')')

  private def simplePi(implicit sourceId: Option[SourceId]): Parser[Pi] =
    (param ~ skipAllWs ~ sym("->") ~/ skipAllWs ~ typePositionTerm).flatSpanned(sourceId).map { Pi.tupled }

  private def typePositionAtom(implicit sourceId: Option[SourceId]): Parser[Term] =
    simplePi |
      lambda |
      deriveP |
      sym('(') ~ skipAllWs ~ typePositionTerm ~ layoutSymTight(')') |
      rootTypeExpr |
      identTypeExpr

  sealed trait TypeTrailer
  case class Dot(name: String, span: Span) extends TypeTrailer
  case class AppTrailer(args: Vector[Term], span: Span) extends TypeTrailer

  private def typeTrailers(implicit sourceId: Option[SourceId]): Parser[Vector[TypeTrailer]] =
    ((P(".") ~/ identAtom).flatSpanned(sourceId).map(Dot.tupled) |
      nonEmptyParenArgs(typePositionTerm).flatSpanned(sourceId).map(AppTrailer.tupled)).rep(0)

  private def typePositionExpr(implicit sourceId: Option[SourceId]): Parser[Term] =
    (typePositionAtom ~ typeTrailers).map { case (ta, trailers) =>
      trailers.foldLeft(ta) { case (cur, nextTrailer) =>
        nextTrailer match {
          case Dot(name, sp)        => Select(cur, name, sp)
          case AppTrailer(args, sp) => App(cur, args, sp)
        }
      }
    }

  private def typePositionTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    (typePositionExpr ~ (skipAllWs ~ sym("->") ~/ skipAllWs ~ typePositionExpr).rep(0)).flatSpanned(sourceId).map {
      case (first, others, sp) =>
        val pieces = first +: others
        pieces.init.foldRight(pieces.last) { case (lhs, rhs) =>
          Pi(Binder("_", TypePattern.Type(lhs), lhs.span), rhs, sp)
        }
    }

  private def typePatternCapture(implicit sourceId: Option[SourceId]): Parser[TypePattern.Capture] =
    (symTight("$") ~/ ident).flatSpanned(sourceId).map(TypePattern.Capture.tupled)

  private def constrainedTypePattern(implicit sourceId: Option[SourceId]): Parser[TypePattern.ConstrainedCapture] =
    (symTight("$") ~ ident ~ kw("of") ~/ topLevelTypePattern)
      .flatSpanned(sourceId)
      .map(TypePattern.ConstrainedCapture.tupled)

  private def typePatternHead(implicit sourceId: Option[SourceId]): Parser[Term] =
    ((rootTypeExpr | identTypeExpr) ~ (P(".") ~/ identAtom).flatSpanned(sourceId).rep(0)).map { case (base, fields) =>
      fields.foldLeft(base) { case (cur, (field, span)) => Select(cur, field, span) }
    }

  private def notFollowedByArrow[A](p: Parser[A]): Parser[A] = new Parser[A] {
    override def parse(input: String, startIdx: Int): ParseResult[A] =
      p.parse(input, startIdx) match {
        case s @ Success(_, _, endIdx) =>
          var idx = endIdx
          while (idx < input.length && input.charAt(idx).isWhitespace) idx += 1
          if (input.startsWith("->", idx)) fail(startIdx, startIdx) else s
        case f: Failure => f
      }
  }

  private def typePatternApp(implicit sourceId: Option[SourceId]): Parser[TypePattern.App] =
    notFollowedByArrow(
      (typePatternHead ~ nonEmptyParenArgs(typePattern)).flatSpanned(sourceId).map(TypePattern.App.tupled)
    ).filter(hasCapture)

  private def hasCapture(pattern: TypePattern): Boolean =
    pattern match {
      case TypePattern.Type(_)                              => false
      case TypePattern.Capture(_, _)                        => true
      case TypePattern.ConstrainedCapture(_, constraint, _) => true
      case TypePattern.App(_, args, _)                      => args.exists(hasCapture)
      case TypePattern.Pi(binders, out, _) => binders.exists(binder => hasCapture(binder.ty)) || hasCapture(out)
    }

  private def splitTypePi(term: Term): (Vector[Binder], Term) =
    term match {
      case Term.Pi(binder, body, _) =>
        val (binders, out) = splitTypePi(body)
        (binder +: binders, out)
      case other => (Vector.empty, other)
    }

  private def splitPatternPi(pattern: TopLevelTP): (Vector[Binder], TopLevelTP) =
    pattern match {
      case TypePattern.Pi(binders, out, _) => (binders, out)
      case TypePattern.Type(term) =>
        val (binders, out) = splitTypePi(term)
        (binders, TypePattern.Type(out))
      case other => (Vector.empty, other)
    }

  private def typePatternPi(implicit sourceId: Option[SourceId]): Parser[TypePattern.Pi] =
    (param ~ skipAllWs ~ sym("->") ~/ skipAllWs ~ topLevelTypePattern)
      .flatSpanned(sourceId)
      .map { case (binder, out, span) =>
        val (tailBinders, tailOut) = splitPatternPi(out)
        TypePattern.Pi(binder +: tailBinders, tailOut, span)
      }
      .filter(hasCapture)

  private def topLevelTypePattern(implicit sourceId: Option[SourceId]): Parser[TopLevelTP] =
    typePatternPi | typePatternApp | constrainedTypePattern | typePositionTerm.map(TypePattern.Type.apply)

  private def typePattern(implicit sourceId: Option[SourceId]): Parser[TypePattern] =
    typePatternPi | typePatternApp | constrainedTypePattern | typePatternCapture |
      typePositionTerm.map(TypePattern.Type.apply)

  private def normalParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('(') ~ argName ~ sym(':') ~/ skipAllWs ~ topLevelTypePattern ~ layoutSymTight(')')).flatSpanned(sourceId).map {
      case (name, ty, span) =>
        Binder(name, ty, span)
    }

  private def instanceParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('[') ~ argName ~ sym(':') ~/ skipAllWs ~ topLevelTypePattern ~ layoutSymTight(']')).flatSpanned(sourceId).map {
      case (name, ty, span) =>
        Binder(name, ty, span, isInstance = true)
    }

  private def erasedParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('{') ~ argName ~ sym(':') ~/ skipAllWs ~ topLevelTypePattern ~ layoutSymTight('}')).flatSpanned(sourceId).map {
      case (name, ty, span) =>
        Binder(name, ty, span)
    }

  private def param(implicit sourceId: Option[SourceId]): Parser[Binder] = normalParam | instanceParam
  private def layoutParam(implicit sourceId: Option[SourceId]): Parser[Binder] = skipAllWs ~ param
  private def layoutErasedParam(implicit sourceId: Option[SourceId]): Parser[Binder] = skipAllWs ~ erasedParam

  private def let(implicit sourceId: Option[SourceId]): Parser[Let] =
    (kw("let") ~/ kw("instance").!.? ~ ident ~
      (sym(':') ~ skipAllWs ~ typePositionTerm).? ~ sym(":=") ~/ skipAllWs ~ term)
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

  private def lambda(implicit sourceId: Option[SourceId]): Parser[Lam] =
    (kw("fun") ~/ funcHeader ~ sym("=>") ~/ skipAllWs ~ term)
      .flatSpanned(sourceId)
      .map { case (header, body, span) => Lam(header, body, span) }

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
    (kw("match") ~/ term ~ (kw("returning") ~/ typePositionTerm).? ~
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
    (layoutParam.rep(0) ~ skipAllWs ~ sym(':') ~/ skipAllWs ~ typePositionTerm)
      .flatSpanned(sourceId)
      .map(FuncHeader.tupled)

  private def declHeader(implicit sourceId: Option[SourceId]): Parser[DeclHeader] =
    (ident ~ funcHeader).flatSpanned(sourceId).map(DeclHeader.tupled)

  // New inductive-specific parsers
  private def inductiveHeader(implicit sourceId: Option[SourceId]): Parser[InductiveHeader] = {
    val paramsP = layoutParam.rep(0)
    val indicesP = (kw("indices") ~/ layoutParam.rep(0)).?.map(_.getOrElse(Vector.empty))
    (ident ~ paramsP ~ indicesP ~ skipAllWs ~ sym(':') ~/ skipAllWs ~ typePositionTerm)
      .flatSpanned(sourceId)
      .map { case (name, params, indices, ty, sp) => InductiveHeader(name, params, indices, ty, sp) }
  }

  private def ctorDecl(implicit sourceId: Option[SourceId]): Parser[ConstructorDecl] = {
    (sym("|") ~/ ident ~ layoutErasedParam.rep(0) ~ layoutParam.rep(0) ~ skipAllWs ~ sym(':') ~/ skipAllWs ~
      typePositionTerm ~ lineSep)
      .flatSpanned(sourceId)
      .map { case (name, erasedBinders, fields, resTy, sp) =>
        ConstructorDecl(name, erasedBinders, fields, resTy, sp)
      }
  }

  private def explicitUnfoldStrategy: Parser[Option[UnfoldStrategy]] =
    kw("opaque").!.map(_ => None) | kw("stable").!.map(_ => Some(UnfoldStrategy.Stable))

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

  // (opaque | stable)? def instance? foo (a: A)[b: B](c : C): D := body
  private def constP(implicit sourceId: Option[SourceId]): Parser[ConstDecl] =
    (explicitUnfoldStrategy.? ~ kw("def") ~/ kw("instance").!.? ~ declHeader ~ decreasesP.? ~
      (sym(":=") ~/ skipAllWs ~ constBody))
      .flatSpanned(sourceId)
      .map { case (explicitStrategy, instanceOpt, header, decreases, body, span) =>
        val default = body match {
          case ConstBody.Builtin(_)  => None
          case ConstBody.TermBody(_) => Some(UnfoldStrategy.Inline)
        }
        ConstDecl(
          explicitStrategy.getOrElse(default),
          header,
          decreases,
          body,
          span,
          isInstance = instanceOpt.isDefined
        )
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
