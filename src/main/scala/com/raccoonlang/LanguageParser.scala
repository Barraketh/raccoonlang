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
  private val lineSep = (emptyLine ~ skipWS).named("LineSep")
  private val skipAllWs = (emptyLine.rep(0) ~ skipWS).named("AllWS")
  private val skipOneLine = emptyLine.? ~ skipWS

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
    (sym("(") ~/ skipAllWs ~ term ~ layoutSymTight(")")) | rootTerm | identTerm | sortFormer | natLitTerm | strLitTerm

  /** The fields a sort takes by name. */
  private val sortFieldNames: Set[String] = Set("level", "kind", "scope")

  private def sortField(implicit sourceId: Option[SourceId]): Parser[(String, Term, Span)] =
    (wordAtom ~ sym('=') ~/ skipAllWs ~ term).flatSpanned(sourceId)

  /** A sort's or closure's field list `{ name = e, ... }` as written, with its span. */
  private def fieldList(implicit sourceId: Option[SourceId]): Parser[(Vector[(String, Term, Span)], Span)] =
    (P('{') ~/ skipAllWs ~ sortField.rep(0, layoutSym(',')) ~ layoutSymTight('}'))
      .flatSpanned(sourceId)
      .named("FieldList")

  /**
   * A written field list's fields by name. An empty list, an unknown or repeated field, and a `level` field where none
   * belongs (`levelMisplaced` says why) are parse errors, the first in source order reported.
   */
  private def fieldsByName(
      written: (Vector[(String, Term, Span)], Span),
      levelMisplaced: Option[String]
  ): Map[String, Term] = {
    val (fields, span) = written
    if (fields.isEmpty) throw ParseError(span.start, span.start, "Empty field list")
    fields.foldLeft(Map.empty[String, Term]) { case (seen, (name, value, fieldSpan)) =>
      def reject(message: String): Nothing = throw ParseError(fieldSpan.start, fieldSpan.start, message)
      if (!sortFieldNames(name)) reject(s"Unknown field $name")
      if (name == "level") levelMisplaced.foreach(reason => reject(s"Misplaced field level: $reason"))
      if (seen.contains(name)) reject(s"Repeated field $name")
      seen + (name -> value)
    }
  }

  /**
   * The start of a closure, `{ name = ...` or an empty `{ }`, recognized without consuming it: the token after the
   * first name tells a closure from an implicit binder `{ name: ... }`, and an empty list is a closure's error to
   * report. It is tried at the start of every term and type and almost always fails at the first character, so that
   * failure is checked first and reported with a constant message.
   */
  private val closureStart: Parser[NoValue.type] = new Parser[NoValue.type] {
    private val fieldOrEnd = skipAllWs ~ ((wordAtom ~ skipWS ~ P('=')) | P('}'))

    override def parse(input: String, startIdx: Int): ParseResult[NoValue.type] =
      if (startIdx < input.length && input.charAt(startIdx) == '{')
        fieldOrEnd.parse(input, startIdx + 1) match {
          case _: Success[_] => Success(NoValue, startIdx, startIdx)
          case _: Failure    => fail(startIdx, startIdx)
        }
      else fail(startIdx, startIdx)

    override def toString: String = "closure"
  }

  /**
   * A closure `{ kind = k, scope = S }` (spec §1): a function type's or lambda's kind and scope, never a level. Callers
   * build it only once `closureStart` has recognized one, so ruling a closure out stays cheap.
   */
  private def closureFields(implicit sourceId: Option[SourceId]): Parser[Closure] =
    fieldList.map { written =>
      val fields = fieldsByName(written, levelMisplaced = Some("a closure has no level"))
      Closure(fields.get("kind"), fields.get("scope"))
    }

  /**
   * A closure where a domain of an unparenthesized chain begins. The closure prefixes the whole group, so it may stand
   * only before the chain's first domain; a nested group is parenthesized.
   */
  private def misplacedClosure(implicit sourceId: Option[SourceId]): Parser[Term] =
    closureStart.spanned(sourceId).map { closureAt =>
      throw ParseError(
        closureAt.span.start,
        closureAt.span.start,
        "A closure prefixes a whole function type; parenthesize a nested one"
      )
    }

  /**
   * The sort formers (spec §1), each with the level it fixes. `Sort` fixes none, so it requires a `level` field; `Type`
   * and `Prop` fix theirs, so a `level` field after either is misplaced.
   */
  private val sortFormers: Map[String, Option[SortLevel]] =
    Map("Sort" -> None, "Type" -> Some(SortLevel.One), "Prop" -> Some(SortLevel.Zero))

  /**
   * A sort former, as a whole word so that `Types` stays an identifier, and its field list if it has one. Its name
   * decides its level and whether a `level` field belongs. An omitted `kind` or `scope` is `Kind.unr` or
   * `Lifetime.empty`.
   */
  private def sortFormer(implicit sourceId: Option[SourceId]): Parser[Term] =
    (wordAtom.filter("SortFormer", sortFormers.contains) ~ (skipWS ~ fieldList).?).flatSpanned(sourceId).map {
      case (former, written, span) =>
        val fixed = sortFormers(former)
        val fields = written.fold(Map.empty[String, Term]) { list =>
          fieldsByName(list, levelMisplaced = fixed.map(_ => s"$former fixes the level"))
        }
        val level = fixed
          .orElse(fields.get("level").map(SortLevel.Written))
          .getOrElse(throw ParseError(span.start, span.start, s"$former requires a level field"))
        Sort(level, fields.get("kind"), fields.get("scope"), span)
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
      buildChain(Closure.omitted, named, body, rest, sp) match {
        case pi: Pi => pi
        case other  => at(other.span) { wtf("named binders always form a Pi") }
      }
    }

  /**
   * A function type written with its closure, in a type or a term position alike: nothing but a function type starts
   * with a closure, so the closure commits, and a closure prefixing no function type is a parse error.
   */
  private def closedPi(implicit sourceId: Option[SourceId]): Parser[Term] =
    (closureStart ~ (closureFields ~/ skipAllWs ~ namedSegment.rep(0) ~ typeExpr ~ chainRest))
      .flatSpanned(sourceId)
      .map { case (written, named, first, rest, sp) =>
        buildChain(written, named, first, rest, sp) match {
          case pi: Pi => pi
          case _      => throw ParseError(sp.start, sp.start, "A closure prefixes a function type")
        }
      }

  // Type positions have their own grammar (arrows, no lambdas/matches) but produce ordinary Terms.
  // A parenthesised type is an ATOM: `((b: B) -> C)` stays a nested Pi rather than merging into an
  // enclosing arrow chain, because grouping is part of a function type's identity.
  private def typeAtom(implicit sourceId: Option[SourceId]): Parser[Term] =
    sym('(') ~ skipAllWs ~ typeTerm ~ layoutSymTight(')') |
      rootTerm |
      identTerm |
      sortFormer |
      natLitTerm |
      strLitTerm |
      misplacedClosure

  /**
   * A trailer's term covers its base as well as the trailer: an application its head, and a selection the path it
   * extends. So a diagnostic about `Nat.add(…)` underlines the whole call, from `Nat`.
   */
  private def trailerSpan(base: Term, trailer: Span): Span = trailer.copy(start = base.span.start)

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
          case Dot(name, sp)        => Select(curTerm, name, trailerSpan(curTerm, sp))
          case AppTrailer(args, sp) => App(curTerm, args, trailerSpan(curTerm, sp))
        }
      }
    }

  /**
   * Named binder groups that open an arrow chain: `(a: A) ->`, `(a: A)(b: B) ->`. A binder commits once its `(name :`
   * or `{name :` is read, since nothing else in a type or term starts that way: a parenthesised type or term cannot be
   * a name followed by a colon, and a closure is `{name =`. So an error inside a binder's type is reported as itself.
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
      closure: Closure,
      named: Vector[Vector[Binder]],
      first: Term,
      rest: Vector[(Vector[Vector[Binder]], Term)],
      sp: Span
  ): Term = {
    val pieces = (named, first) +: rest
    val binders =
      pieces.init.flatMap { case (groups, domain) => groups.flatten :+ Binder("_", domain, domain.span) } ++
        pieces.last._1.flatten
    if (binders.isEmpty) pieces.last._2 else Pi(closure, binders, pieces.last._2, sp)
  }

  /**
   * An arrow chain is ONE binder group: `A -> B -> C` and `(a: A) -> (b: B) -> C` are 2-ary function types, not nested
   * 1-ary ones. Nesting is written with parentheses — `(a: A) -> ((b: B) -> C)` — where the body is a parenthesised
   * atom and stays its own Pi. Grouping is part of a function type's identity (docs/kernel.md#definitional-equality),
   * so this is the only place the grouping of a written type is decided. Each type in the chain is parsed exactly once:
   * the arrow is looked for only after a piece has been read, never by speculatively re-parsing it as a domain.
   */
  private def typeTerm(implicit sourceId: Option[SourceId]): Parser[Term] =
    closedPi | (namedSegment.rep(0) ~ typeExpr ~ chainRest).flatSpanned(sourceId).map { case (named, first, rest, sp) =>
      buildChain(Closure.omitted, named, first, rest, sp)
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
    (kw("fun") ~/ (closureStart ~ closureFields).? ~ funcHeader ~ sym("=>") ~/ skipAllWs ~ term)
      .flatSpanned(sourceId)
      .map[SurfaceAst.Term] { case (written, header, body, span) =>
        if (header.params.isEmpty) throw ParseError(header.span.start, header.span.start, "A lambda binds a parameter")
        Lam(written.getOrElse(Closure.omitted), header, body, span)
      }

  /**
   * `scope l => e` (spec §1). `scope` is a keyword only here, at the start of a term; in a field list it is a field
   * name, which the field parser reads as a plain word. The body extends as far to the right as a lambda body does.
   */
  private def scopeP(implicit sourceId: Option[SourceId]): Parser[Term] =
    (kw("scope") ~/ argName ~ sym("=>") ~/ skipAllWs ~ term).flatSpanned(sourceId).map { case (name, body, span) =>
      Scope(name, body, span)
    }

  private def caseHead: Parser[(Vector[String], Boolean)] = {
    val shortName = (symTight(".") ~/ ident).map(name => (Vector(name), true))
    val globalPath = pathP.map(path => (path, false))
    shortName | globalPath
  }

  private def matchCase(implicit sourceId: Option[SourceId]): Parser[Case] = {
    val patternVar = argName.spanned(sourceId).map(name => PatternVar(name.value, name.span))
    (sym("|") ~/ caseHead ~ (wsSep ~ patternVar).rep(0) ~ sym("=>") ~/ skipAllWs ~ term ~ lineSep)
      .flatSpanned(sourceId)
      .map { case (ctorPath, useShortName, patternVars, body, span) =>
        Case(ctorPath, useShortName, patternVars, body, span)
      }
      .named("Case")
  }

  /** `returning` continues the header, so it may start the next line, as an arrow or a parameter group may. */
  private def matchP(implicit sourceId: Option[SourceId]): Parser[Match] = {
    (kw("match") ~/ term ~ (skipAllWs ~ kw("returning") ~/ typeTerm).named("returning clause") ~
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
    ((lambda | scopeP | matchP | closedPi | body | simplePi | termAtom) ~ termTrailers).map { case (base, trailers) =>
      trailers.foldLeft(base) {
        case (cur, TermDot(name, sp)) => Select(cur, name, trailerSpan(cur, sp))
        case (cur, TermApp(args, sp)) => App(cur, args, trailerSpan(cur, sp))
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
          selectorOf = None,
          span
        )
      }

  private def axiomP(implicit sourceId: Option[SourceId]): Parser[AxiomDecl] =
    (kw("axiom") ~/ declHeader)
      .flatSpanned(sourceId)
      .map { case (header, span) =>
        AxiomDecl(header, span)
      }

  private def sealedP: Parser[Boolean] =
    kw("sealed").!.?.map(_.isDefined)

  private def inductiveP(implicit sourceId: Option[SourceId]): Parser[InductiveDecl] =
    (sealedP ~ kw("inductive") ~/ inductiveHeader ~ lineSep ~ ctorDecl.rep(0))
      .flatSpanned(sourceId)
      .map { case (isSealed, h, cs, sp) => InductiveDecl(h, cs, generateSelectors = false, isSealed, sp) }

  private def structP(implicit sourceId: Option[SourceId]): Parser[InductiveDecl] =
    (sealedP ~ kw("struct") ~/ inductiveHeader ~ lineSep ~ ctorDecl)
      .flatSpanned(sourceId)
      .map { case (isSealed, h, cs, sp) => InductiveDecl(h, Vector(cs), generateSelectors = true, isSealed, sp) }

  private def commandP(implicit sourceId: Option[SourceId]): Parser[Command] =
    declP | namespaceP | openP | mutualP | blockP

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

  /** Mutual groups use the ordinary command-block layout and are lowered atomically by the elaborator. */
  private def mutualP(implicit sourceId: Option[SourceId]): Parser[Mutual] =
    (kw("mutual") ~/ skipAllWs ~ sym("{") ~ commandsP ~ symTight("}"))
      .flatSpanned(sourceId)
      .map(Mutual.tupled)

  private def importP(implicit sourceId: Option[SourceId]): Parser[Import] =
    (kw("import") ~/ pathP ~/ emptyLine).flatSpanned(sourceId).map(Import.tupled)

  private def programP(implicit sourceId: Option[SourceId]): Parser[Program] = {
    (skipAllWs ~ importP.rep(0) ~ commandsP ~ term.? ~ skipAllWs ~/ End).map(Program.tupled)
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
