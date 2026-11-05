package com.raccoonlang

import com.raccoonlang.Parser._
import com.raccoonlang.SurfaceAst.Command.Decl.{AxiomDecl, ConstDecl, InductiveDecl}
import com.raccoonlang.SurfaceAst.Command._
import com.raccoonlang.SurfaceAst.Term._
import com.raccoonlang.SurfaceAst._

object LanguageParser {
  // Whitespace handling
  private val skipWS = CharsWhile(c => c == ' ' || c == '\t').named("SkipWS")
  private val wsSep = P("whitespace", c => c == ' ' || c == '\t').rep(1).named("whitespace")
  private val comment = P("//") ~ CharsWhile(c => c != '\n')

  private val emptyLine = (skipWS ~ comment.? ~ Exact("\n")).named("a line break")
  private val skipAllWs = (emptyLine.rep(0) ~ skipWS).named("AllWS")

  /**
   * The line break between two items of a list: imports, commands, a block's statements, a match's cases, an
   * inductive's constructors. Any number of blank and comment-only lines may stand in its place. An item never consumes
   * the break after it, so a list ends at the first line that does not start another of its items.
   */
  private val lineSep = (emptyLine.rep(1) ~ skipWS).named("a line break")

  /**
   * Where an import, a case or a constructor ends, or the header a list of cases or constructors follows: the rest of
   * the line is blank or a comment. It consumes nothing, leaving the line break to the list, so an item written on the
   * same line is reported where it is.
   */
  private val lineEnd: Parser[NoValue.type] = new Parser[NoValue.type] {
    private val rest = skipWS ~ comment.?

    override def parse(input: String, startIdx: Int): ParseResult[NoValue.type] =
      rest.parse(input, startIdx) match {
        case Success(_, _, endIdx) if endIdx == input.length || input.charAt(endIdx) == '\n' =>
          Success(NoValue, startIdx, startIdx)
        case _ => fail(startIdx, startIdx)
      }

    override def toString: String = "the end of the line"
  }

  /** Succeeds, consuming nothing, where `p` does not match. */
  private def notFollowedBy(p: Parser[Any], name: String): Parser[NoValue.type] = new Parser[NoValue.type] {
    override def parse(input: String, startIdx: Int): ParseResult[NoValue.type] =
      p.parse(input, startIdx) match {
        case _: Success[_] => fail(startIdx, startIdx)
        case _: Failure    => Success(NoValue, startIdx, startIdx)
      }

    override def toString: String = name
  }

  // `use` is no keyword: a body statement that starts with it and a space is a `use` statement, and elsewhere it is an
  // identifier.
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
    "instance",
    "derive",
    "inductive",
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
    "in",
    "mutual"
  )

  private val identChar = P("a letter or digit", c => c.isLetterOrDigit || c == '_')

  private val identAtom =
    (P("a letter", c => c.isLetter) ~ identChar.rep(0)).!.filter("an identifier", s => !keywords.contains(s))

  private val rootName = "_root_"
  private val rootIdent: Parser[String] = P(rootName).!
  private val ident: Parser[String] = identAtom

  private val argName: Parser[String] = ident | P("_").!

  // Each token is named by its text, which a parse error reports as what was expected.
  private def sym(c: Char) = (skipWS ~ P(c) ~/ skipWS).named(s"'$c'")
  private def sym(s: String) = (skipWS ~ P(s) ~/ skipWS).named(s"'$s'")

  // Variant that does not consume trailing whitespace; useful before ws-separated reps
  private def symTight(c: Char) = (skipWS ~ P(c)).named(s"'$c'")
  private def symTight(s: String) = (skipWS ~ P(s)).named(s"'$s'")
  private def layoutSym(c: Char) = (skipAllWs ~ P(c) ~/ skipAllWs).named(s"'$c'")
  private def layoutSymTight(c: Char) = (skipAllWs ~ P(c)).named(s"'$c'")
  private def layoutSymTight(s: String) = (skipAllWs ~ P(s)).named(s"'$s'")

  private def kw(s: String) = (skipWS ~ P(s) ~ wsSep).named(s"'$s'")
  private def kwTight(s: String) = (skipWS ~ P(s)).named(s"'$s'")

  private def identTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    ident.flatSpanned(sourceId).map(Ident.tupled)
  private def rootTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    rootIdent.flatSpanned(sourceId).map(Ident.tupled)

  /** A string literal; a malformed one is a fatal error at the offending character or escape. */
  private val strLitAtom: Parser[String] = new Parser[String] {
    override def parse(input: String, startIdx: Int): ParseResult[String] =
      if (startIdx >= input.length || input.charAt(startIdx) != '"') fail(startIdx, startIdx)
      else
        try {
          val decoded = UnicodeScalarString.decodeQuoted(input, startIdx)
          Success(decoded.text, startIdx, decoded.endIdx)
        } catch {
          case invalid: UnicodeScalarString.Invalid => throw ParseError(startIdx, invalid.offset, invalid.message)
        }

    override def toString: String = "a string"
  }

  private def strLitTerm(implicit sourceId: Option[SourceId]): Parser[StrLit] =
    strLitAtom.flatSpanned(sourceId).map(StrLit.tupled)

  /** A Nat literal: ASCII decimal digits. */
  private val natLitAtom: Parser[BigInt] =
    P("a digit", c => c >= '0' && c <= '9').rep(1).!.map(BigInt(_)).named("a number")

  private def natLitTerm(implicit sourceId: Option[SourceId]): Parser[NatLit] =
    natLitAtom.flatSpanned(sourceId).map(NatLit.tupled)

  private def pathP: Parser[Vector[String]] = ident.rep(min = 1, sep = P('.'))

  private def openPathP: Parser[(Vector[String], Boolean)] = {
    val rootPath = (rootIdent ~ P('.') ~/ pathP).map { case (_, path) => (path, true) }
    val scopedPath = pathP.map(path => (path, false))
    rootPath | scopedPath
  }

  private def deriveP(implicit sourceId: Option[SourceId]): Parser[Derive] =
    (kwTight("derive") ~/ symTight("[") ~/ skipAllWs ~ typeTerm ~ layoutSymTight("]"))
      .flatSpanned(sourceId)
      .map(Derive.tupled)

  private def termAtom(implicit sourceId: Option[SourceId]): Parser[Term] =
    deriveP | (sym("(") ~/ skipAllWs ~ term ~ layoutSymTight(")")) | rootTerm | identTerm | natLitTerm | strLitTerm

  // Type atoms: identifier or parenthesized type, with bracket selects as a postfix variant.
  // `$name` captures are parsed only by binder-type pattern parsers below.
  private def identTypeTerm(implicit sourceId: Option[SourceId]): Parser[TypeTerm] =
    ident.flatSpanned(sourceId).map[TypeTerm](Ident.tupled)
  private def rootTypeTerm(implicit sourceId: Option[SourceId]): Parser[TypeTerm] =
    rootIdent.flatSpanned(sourceId).map[TypeTerm](Ident.tupled)

  private def parenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    P('(') ~/ skipAllWs ~ arg.rep(0, layoutSym(',')) ~ layoutSymTight(')')

  private def nonEmptyParenArgs[A](arg: => Parser[A]): Parser[Vector[A]] =
    sym('(') ~/ skipAllWs ~ arg.rep(1, layoutSym(',')) ~ layoutSymTight(')')

  /** A type's atoms. A lambda is one, so that a type may apply a family or a function to a predicate. */
  private def typeAtom(implicit sourceId: Option[SourceId]): Parser[TypeTerm] =
    lambda |
      deriveP |
      sym('(') ~ skipAllWs ~ typeTerm ~ layoutSymTight(')') |
      rootTypeTerm |
      identTypeTerm |
      natLitTerm |
      strLitTerm

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

  /** One link of an arrow chain: a named binder `(x: A)`, which the rest of the chain may mention, or a type. */
  private def arrowItem(implicit sourceId: Option[SourceId]): Parser[Either[Binder, TypeTerm]] =
    param.map[Either[Binder, TypeTerm]](Left(_)) | typeExpr.map[Either[Binder, TypeTerm]](Right(_))

  /**
   * A type: an arrow chain `d1 -> ... -> dn -> out`, one function type of the n parameters `d1 ... dn`, or a type
   * expression alone. A parenthesized chain is an atom (`typeAtom`), so the grouping is the one written:
   * `A -> (B -> C)` takes one argument and returns a function, `A -> B -> C` takes two.
   */
  private def typeTerm(implicit sourceId: Option[SourceId]): Parser[TypeTerm] =
    (arrowItem ~ (skipAllWs ~ sym("->") ~/ skipAllWs ~ arrowItem).rep(0))
      .flatSpanned(sourceId)
      .filter("a type after the last arrow", { case (first, others, _) => (first +: others).last.isRight })
      .map { case (first, others, sp) => arrowChain(first +: others, sp) }
      .named("a type")

  /** An arrow chain whose last item is a type (its parsers filter for it): that type alone, or `arrowPi`. */
  private def arrowChain(items: Vector[Either[Binder, TypeTerm]], span: Span): TypeTerm =
    if (items.length == 1) arrowOut(items) else arrowPi(items, span)

  /**
   * The function type of an arrow chain of at least two items whose last is a type: each earlier item a parameter, a
   * named binder as written or a type as the anonymous binder `_`.
   */
  private def arrowPi(items: Vector[Either[Binder, TypeTerm]], span: Span): Pi =
    Pi(items.init.map {
      case Left(binder)  => binder
      case Right(domain) => Binder("_", BinderType.TypePattern(TypePattern.Type(domain), domain.span), domain.span)
    }, arrowOut(items), span)

  private def arrowOut(items: Vector[Either[Binder, TypeTerm]]): TypeTerm =
    items.last.fold(binder => throw new IllegalStateException(s"arrow chain ending in binder ${binder.name}"), identity)

  /**
   * What may continue a type after a pattern application: an argument list, a projection or an arrow. A pattern
   * application is a whole binder type only when none follows, as in `List($A)`; otherwise the binder type is a type,
   * such as `R(x)(y, z)` or `List(Nat) -> Nat`, which holds no capture.
   */
  private val typeContinues: Parser[NoValue.type] =
    (skipWS ~ P('(')) | P('.') | (skipAllWs ~ P("->"))

  private val wholePattern = notFollowedBy(typeContinues, "the end of a type pattern")

  private def typePatternCapture(implicit sourceId: Option[SourceId]): Parser[TypePattern.Capture] =
    (symTight("$") ~/ ident ~ (kw("in") ~/ topLevelTypePattern).?).flatSpanned(sourceId).map {
      case (name, constraint, span) => TypePattern.Capture(name, span, constraint)
    }

  private def typePatternHead(implicit sourceId: Option[SourceId]): Parser[TypeTerm] =
    ((rootTypeTerm | identTypeTerm) ~ (P(".") ~/ identAtom).flatSpanned(sourceId).rep(0)).map { case (base, fields) =>
      fields.foldLeft(base) { case (cur, (field, span)) => TSelect(cur, field, span) }
    }

  /** A pattern application, `F(p, ...)`, where nothing continues it as a type (`typeContinues`). */
  private def typePatternApp(implicit sourceId: Option[SourceId]): Parser[TypePattern.App] =
    (typePatternHead ~ nonEmptyParenArgs(typePattern) ~ wholePattern).flatSpanned(sourceId).map(TypePattern.App.tupled)

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
    (sym('(') ~ argName ~ sym(':') ~/ skipAllWs ~ binderType ~ layoutSymTight(')')).flatSpanned(sourceId).map {
      case (name, ty, span) =>
        Binder(name, ty, span)
    }

  private def instanceParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('[') ~ argName ~ sym(':') ~/ skipAllWs ~ binderType ~ layoutSymTight(']')).flatSpanned(sourceId).map {
      case (name, ty, span) =>
        Binder(name, ty, span, isInstance = true)
    }

  private def erasedParam(implicit sourceId: Option[SourceId]): Parser[Binder] =
    (sym('{') ~ argName ~ sym(':') ~/ skipAllWs ~ binderType ~ layoutSymTight('}')).flatSpanned(sourceId).map {
      case (name, ty, span) =>
        Binder(name, ty, span)
    }

  private def param(implicit sourceId: Option[SourceId]): Parser[Binder] = normalParam | instanceParam
  private def layoutParam(implicit sourceId: Option[SourceId]): Parser[Binder] = skipAllWs ~ param
  private def layoutErasedParam(implicit sourceId: Option[SourceId]): Parser[Binder] = skipAllWs ~ erasedParam

  private def bindingPattern(implicit sourceId: Option[SourceId]): Parser[BindingPattern] = {
    val unpack =
      (sym('(') ~/ skipAllWs ~ bindingPattern.rep(0, layoutSym(',')) ~ layoutSymTight(')'))
        .flatSpanned(sourceId)
        .map { case (fields, span) => BindingPattern.Unpack(fields, span) }
    val leaf = argName.flatSpanned(sourceId).map { case (name, span) =>
      if (name == "_") BindingPattern.Discard(span) else BindingPattern.Bind(name, span)
    }
    unpack | leaf
  }

  private def let(implicit sourceId: Option[SourceId]): Parser[Let] = {
    val head: Parser[Either[String, BindingPattern]] =
      (kw("instance") ~/ ident).map(Left(_)) | bindingPattern.map(Right(_))
    (kw("let") ~/ head ~ (sym(':') ~ skipAllWs ~ typeTerm).? ~ sym(":=") ~/ skipAllWs ~ term)
      .flatSpanned(sourceId)
      .map { case (binding, ty, value, span) =>
        binding match {
          case Left(name)     => Let.Instance(name, ty, value, span)
          case Right(pattern) => Let.Binding(pattern, ty, value, span)
        }
      }
  }

  private def useStmt(implicit sourceId: Option[SourceId]): Parser[Use] =
    (kw("use") ~/ term).flatSpanned(sourceId).map(Use.tupled)

  private def bodyStmt(implicit sourceId: Option[SourceId]): Parser[BodyStmt] =
    useStmt.map(UseStmt.apply) | openP.map(OpenStmt.apply) | let.map(LetStmt.apply)

  /** A block: statements, one per line, and its result, among which blank and comment-only lines may stand. */
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
  }

  // no longer support `using normalizer` in parser; replaced by `use` statements

  /** `fun (x: A)...: B => body`. A lambda binds at least one parameter. */
  private def lambda(implicit sourceId: Option[SourceId]): Parser[Lam] = {
    val header =
      (layoutParam.rep(1).named("a lambda's parameter") ~ skipAllWs ~ sym(':') ~/ skipAllWs ~ typeTerm)
        .flatSpanned(sourceId)
        .map(FuncHeader.tupled)
    (kw("fun") ~/ header ~ sym("=>") ~/ skipAllWs ~ term)
      .flatSpanned(sourceId)
      .map { case (header, body, span) => Lam(header, body, span) }
  }

  private def caseHead: Parser[(Vector[String], Boolean)] = {
    val shortName = (symTight(".") ~/ ident).map(name => (Vector(name), true))
    val globalPath = pathP.map(path => (path, false))
    shortName | globalPath
  }

  private def matchCase(implicit sourceId: Option[SourceId]): Parser[Case] =
    (sym("|") ~/ caseHead ~ (wsSep ~ argName).rep(0) ~ sym("=>") ~/ skipAllWs ~ term ~ lineEnd)
      .flatSpanned(sourceId)
      .map { case (ctorPath, useShortName, argNames, body, span) =>
        Case(ctorPath, useShortName, argNames, body, span)
      }

  /**
   * `| _ => e`, a wildcard case: it binds no fields. It is tried before `matchCase`, which commits to a constructor
   * once it has read `|`.
   */
  private def wildcardCase(implicit sourceId: Option[SourceId]): Parser[Wildcard] =
    (sym("|") ~ P("_") ~ (wsSep ~ argName.spanned(sourceId)).rep(0) ~ sym("=>") ~/ skipAllWs ~ term ~ lineEnd)
      .flatSpanned(sourceId)
      .map { case (fields, body, span) =>
        fields.headOption.foreach { field =>
          throw ParseError(field.span.start, field.span.start, "A wildcard case binds no fields")
        }
        Wildcard(body, span)
      }

  /** `h :` in `match h : e`, the equation the match names. */
  private def matchEquation(implicit sourceId: Option[SourceId]): Parser[MatchEquation] =
    (ident.flatSpanned(sourceId) ~ sym(':')).map { case (name, span) => MatchEquation(name, span) }

  /**
   * `match h : e returning M with`, then its cases, each on lines of its own. `returning` continues the header, so it
   * may start the next line. A wildcard case is the last case of its match, so a match has at most one.
   */
  private def matchP(implicit sourceId: Option[SourceId]): Parser[Match] = {
    val anyCase = wildcardCase.map[Either[Wildcard, Case]](Left(_)) | matchCase.map(Right(_))
    (kw("match") ~/ matchEquation.? ~ term ~ (skipAllWs ~ kw("returning") ~/ typeTerm).? ~
      kwTight("with") ~/ lineEnd ~ (lineSep ~ anyCase).rep(0))
      .flatSpanned(sourceId)
      .map { case (equation, scrut, motive, written, sp) =>
        written.dropRight(1).collectFirst { case Left(wildcard) => wildcard }.foreach { wildcard =>
          throw ParseError(
            wildcard.span.start,
            wildcard.span.start,
            "A wildcard case is the last case of its match; a nested match takes every case after it, so brace it"
          )
        }
        val cases = written.collect { case Right(c) => c }
        Match(scrut, motive, cases, written.lastOption.flatMap(_.left.toOption), equation, sp)
      }
  }

  sealed trait TermTrailer
  case class TermDot(name: String, span: Span) extends TermTrailer
  case class TermApp(args: Vector[Term], span: Span) extends TermTrailer

  private def termTrailers(implicit sourceId: Option[SourceId]): Parser[Vector[TermTrailer]] =
    ((P(".") ~/ identAtom).flatSpanned(sourceId).map(TermDot.tupled) |
      parenArgs(term).flatSpanned(sourceId).map(TermApp.tupled)).rep(0)

  /**
   * A term, which an arrow chain may continue: `A -> B` and `(x: A) -> B` are terms, function types, as they are types
   * (`typeTerm`). A named binder heads a chain only; alone it is no term.
   */
  private def term(implicit sourceId: Option[SourceId]): Parser[Term] =
    ((param.map[Either[Binder, Term]](Left(_)) | termExpr.map[Either[Binder, Term]](Right(_))).spanned(sourceId) ~
      (skipAllWs ~ sym("->") ~/ skipAllWs ~ arrowItem).rep(0))
      .flatSpanned(sourceId)
      .filter("a type after the last arrow", { case (head, rest, _) => rest.lastOption.fold(head.value.isRight)(_.isRight) })
      .map {
        case (head, rest, _) if rest.isEmpty => head.value.fold(binder => throw new IllegalStateException(s"lone binder ${binder.name}"), identity)
        case (head, rest, sp)                => arrowPi(head.value.map(asType(_, head.span)) +: rest, sp)
      }
      .named("a term")

  private def termExpr(implicit sourceId: Option[SourceId]): Parser[Term] =
    ((lambda | matchP | body | termAtom) ~ termTrailers).map { case (base, trailers) =>
      trailers.foldLeft(base) {
        case (cur, TermDot(name, sp)) => Select(cur, name, sp)
        case (cur, TermApp(args, sp)) => App(cur, args, sp)
      }
    }

  /**
   * A term written as an arrow's domain, as the type it is: every form but a block or a match is one. `span` is the
   * term's whole span, where a block or a match is refused.
   */
  private def asType(term: Term, span: Span): TypeTerm =
    term match {
      case t: Ident                => t
      case t: NatLit               => t
      case t: StrLit               => t
      case t: Pi                   => t
      case t: Derive               => t
      case t: Lam                  => t
      case Select(base, field, sp) => TSelect(asType(base, span), field, sp)
      case App(fn, args, sp) =>
        if (args.isEmpty) throw ParseError(span.start, span.start, "A function type's domain applies to no arguments")
        TApp(asType(fn, span), args.map(asType(_, span)), sp)
      case _: Match | _: Body => throw ParseError(span.start, span.start, "A function type's domain must be a type")
    }

  private def funcHeader(implicit sourceId: Option[SourceId]): Parser[FuncHeader] =
    (layoutParam.rep(0) ~ skipAllWs ~ sym(':') ~/ skipAllWs ~ typeTerm).flatSpanned(sourceId).map(FuncHeader.tupled)

  /** A declaration and the namespace its dotted name puts it in: `def A.b` declares `b` in `A`. */
  private final case class InNamespace[+A](prefix: Vector[String], value: A)

  /** A declaration's name, which may be dotted: its last segment is the name, and the others its namespace's path. */
  private def declName(implicit sourceId: Option[SourceId]): Parser[InNamespace[Spanned[String]]] =
    ident.spanned(sourceId).rep(min = 1, sep = P('.')).map(names => InNamespace(names.init.map(_.value), names.last))

  private def declHeader(implicit sourceId: Option[SourceId]): Parser[InNamespace[DeclHeader]] =
    (declName ~ funcHeader).flatSpanned(sourceId).map { case (name, header, span) =>
      InNamespace(name.prefix, DeclHeader(name.value.value, header, span, name.value.span))
    }

  // New inductive-specific parsers
  private def inductiveHeader(implicit sourceId: Option[SourceId]): Parser[InNamespace[InductiveHeader]] = {
    val paramsP = layoutParam.rep(0)
    val indicesP = (kw("indices") ~/ layoutParam.rep(0)).?.map(_.getOrElse(Vector.empty))
    (declName ~ paramsP ~ indicesP ~ skipAllWs ~ sym(':') ~/ skipAllWs ~ typeTerm)
      .flatSpanned(sourceId)
      .map { case (name, params, indices, ty, sp) =>
        InNamespace(name.prefix, InductiveHeader(name.value.value, params, indices, ty, sp, name.value.span))
      }
  }

  private def ctorDecl(implicit sourceId: Option[SourceId]): Parser[ConstructorDecl] = {
    (sym("|") ~/ ident.spanned(sourceId) ~ layoutErasedParam.rep(0) ~ layoutParam.rep(0) ~ skipAllWs ~ sym(':') ~/
      skipAllWs ~ typeTerm ~ lineEnd)
      .flatSpanned(sourceId)
      .map { case (name, erasedBinders, fields, resTy, sp) =>
        ConstructorDecl(name.value, erasedBinders, fields, resTy, sp, name.span)
      }
  }

  private def constBody(implicit sourceId: Option[SourceId]): Parser[ConstBody] =
    kwTight("builtin").!.flatSpanned(sourceId).map { case (_, span) => ConstBody.Builtin(span) } |
      term.map(ConstBody.TermBody.apply)

  private def decreasesP(implicit sourceId: Option[SourceId]): Parser[DecreaseSpec] = {
    val param = ident.flatSpanned(sourceId).map { case (name, span) => MetricComponent.Param(name, span) }

    // The keyword is a whole word, so a parameter whose name starts with it, such as `measured`, is no measure.
    val measure =
      (kwTight("measure") ~ notFollowedBy(identChar, "the end of 'measure'") ~/ symTight("(") ~/ term ~ symTight(")"))
        .flatSpanned(sourceId)
        .map { case (measureTerm, span) => MetricComponent.Measure(measureTerm, span) }

    val structural =
      (kwTight("structural") ~/ symTight("(") ~/ param ~ symTight(")"))
        .flatSpanned(sourceId)
        .map { case (component, span) => DecreaseSpec(Vector(component), span) }

    val lexicographic =
      (kwTight("lexicographic") ~/ symTight("(") ~/ (measure | param).rep(1, sym(",")) ~ symTight(")"))
        .flatSpanned(sourceId)
        .map { case (components, span) => DecreaseSpec(components, span) }

    val oneMeasure = measure.map(component => DecreaseSpec(Vector(component), component.span))

    // The specification follows the keyword on its line or starts a later one.
    val keyword = (skipWS ~ P("decreases") ~ (lineSep | wsSep)).named("'decreases'")
    keyword ~/ (structural | lexicographic | oneMeasure).named("structural(x), lexicographic(x, ...) or measure(e)")
  }

  /**
   * `def instance? foo (a: A)[b: B](c : C): D := body`. A `decreases` clause continues the header, so it may start a
   * later line.
   */
  private def constP(implicit sourceId: Option[SourceId]): Parser[InNamespace[ConstDecl]] =
    (kw("def") ~/ kw("instance").!.? ~ declHeader ~ (skipAllWs ~ decreasesP).? ~
      (sym(":=") ~/ skipAllWs ~ constBody))
      .flatSpanned(sourceId)
      .map { case (instanceOpt, header, decreases, body, span) =>
        header.copy(value = ConstDecl(header.value, decreases, body, span, isInstance = instanceOpt.isDefined))
      }

  private def axiomP(implicit sourceId: Option[SourceId]): Parser[InNamespace[AxiomDecl]] =
    (kw("axiom") ~/ kw("instance").!.? ~ declHeader)
      .flatSpanned(sourceId)
      .map { case (instanceOpt, header, span) =>
        header.copy(value = AxiomDecl(header.value, span, isInstance = instanceOpt.isDefined))
      }

  private def inductiveP(implicit sourceId: Option[SourceId]): Parser[InNamespace[InductiveDecl]] =
    (kw("inductive") ~/ inductiveHeader ~ lineEnd ~ (lineSep ~ ctorDecl).rep(0))
      .flatSpanned(sourceId)
      .map { case (h, cs, sp) => h.copy(value = InductiveDecl(h.value, cs, sp)) }

  private def commandP(implicit sourceId: Option[SourceId]): Parser[Command] =
    declP | namespaceP | openP | mutualP | blockP

  /**
   * `mutual { declarations }`: only declarations, which the elaborator requires to be all families or all defs. They
   * are separated as commands are, by line breaks among which blank and comment lines may stand. A member's name is not
   * dotted: the block's members share one scope, so a block that declares into a namespace stands in its block.
   */
  private def mutualP(implicit sourceId: Option[SourceId]): Parser[Mutual] = {
    val member = (constP | axiomP | inductiveP).map { declared =>
      if (declared.prefix.nonEmpty)
        throw ParseError(
          declared.value.span.start,
          declared.value.span.start,
          "A mutual block's member has no dotted name; put the block in a namespace block"
        )
      declared.value
    }
    (kw("mutual") ~/ sym('{') ~/ skipAllWs ~ member.rep(0, lineSep) ~ skipAllWs ~ symTight('}'))
      .flatSpanned(sourceId)
      .map(Mutual.tupled)
  }

  private def commandsP(implicit sourceId: Option[SourceId]): Parser[Vector[Command]] =
    skipAllWs ~ commandP.rep(0, lineSep) ~ skipAllWs

  /** A declaration, which a dotted name puts in a namespace block of its own. */
  private def declP(implicit sourceId: Option[SourceId]): Parser[Command] =
    (constP | axiomP | inductiveP).map { declared =>
      if (declared.prefix.isEmpty) declared.value
      else Namespace(declared.prefix, Vector(declared.value), declared.value.span)
    }

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
    implicit val sourceId: Option[SourceId] = None
    tryParse(input, programP)
  }

  def parseProgram(input: String, id: SourceId): ParseResult[Program] = {
    implicit val sourceId: Option[SourceId] = Some(id)
    tryParse(input, programP)
  }

}
