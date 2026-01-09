package com.raccoonlang

import com.raccoonlang.SurfaceAst._

// A hand-written recursive descent parser for RaccoonSurface per Parser-Spec.md
// Focuses on deterministic, whitespace-insensitive parsing with simple tokens.
// Exposes simple entry points via the companion object.
class SurfaceParserRec(input: String) {
  private val len = input.length
  private var i: Int = 0

  // ----------------- Utilities -----------------
  private def isIdentStart(c: Char): Boolean = c.isLetter || c == '_' || c == '$'
  private def isIdentPart(c: Char): Boolean = c.isLetterOrDigit || c == '_' || c == '$'

  private def skipWhitespace(): Unit = {
    while (i < len) {
      val c = input.charAt(i)
      if (c.isWhitespace) { i += 1 }
      else if (c == '/' && i + 1 < len && input.charAt(i + 1) == '/') {
        // line comment // ... to end of line
        i += 2
        while (i < len && input.charAt(i) != '\n') i += 1
      } else if (c == '/' && i + 1 < len && input.charAt(i + 1) == '*') {
        // block comment /* ... */
        i += 2
        while (i + 1 < len && !(input.charAt(i) == '*' && input.charAt(i + 1) == '/')) i += 1
        if (i + 1 < len) i += 2
      } else return
    }
  }

  private def eof: Boolean = { skipWhitespace(); i >= len }

  private def startsWith(s: String): Boolean = {
    skipWhitespace()
    input.regionMatches(i, s, 0, s.length)
  }

  private def expect(s: String): Unit = {
    skipWhitespace()
    if (!startsWith(s)) fail(s"expected '$s'")
    i += s.length
  }

  private def tryConsume(s: String): Boolean = {
    skipWhitespace();
    if (startsWith(s)) { i += s.length; true } else false
  }

  private def fail(msg: String): Nothing = throw new ParseError(s"$msg at index $i")

  private def pos: Int = { skipWhitespace(); i }

  // ----------------- Lexemes -----------------
  private val keywords = Set(
    "inline", "data", "where", "def", "theorem", "axiom",
    "forall", "let", "in", "match", "as", "returning", "with",
    "implicit", "Type"
  )

  private def peekIdentRaw(): Option[String] = {
    skipWhitespace()
    if (i < len && isIdentStart(input.charAt(i))) {
      val j0 = i
      i += 1
      while (i < len && isIdentPart(input.charAt(i))) i += 1
      val s = input.substring(j0, i)
      i = j0 // do not consume
      Some(s)
    } else None
  }

  private def readIdentRaw(): String = {
    skipWhitespace()
    if (i < len && isIdentStart(input.charAt(i))) {
      val j0 = i
      i += 1
      while (i < len && isIdentPart(input.charAt(i))) i += 1
      input.substring(j0, i)
    } else fail("expected identifier")
  }

  private def readName(): String = {
    val n = readIdentRaw()
    if (keywords.contains(n)) fail(s"identifier '$n' is a reserved keyword")
    n
  }

  private def readInt(): Int = {
    skipWhitespace()
    if (i < len && input.charAt(i).isDigit) {
      val j0 = i
      i += 1
      while (i < len && input.charAt(i).isDigit) i += 1
      input.substring(j0, i).toInt
    } else fail("expected integer literal")
  }

  // symbols with potential multi-char forms must be tried in order
  private def sym(s: String): Unit = expect(s)
  private def optSym(s: String): Boolean = tryConsume(s)

  // ----------------- Levels -----------------
  private def parseLevel(): SLevel = {
    skipWhitespace()
    // Nat lit
    val c = if (i < len) input.charAt(i) else '\u0000'
    if (c.isDigit) return SurfaceAst.SLevel.NatLit(readInt())

    // succ(level)
    if (startsWith("succ")) {
      expect("succ"); sym("("); val l = parseLevel(); sym(")"); return SurfaceAst.SLevel.Succ(l)
    }
    // max(a, b)
    if (startsWith("max")) {
      expect("max"); sym("("); val a = parseLevel(); sym(","); val b = parseLevel(); sym(")"); return SurfaceAst.SLevel.Max(a, b)
    }
    // ident
    SurfaceAst.SLevel.Ident(readName())
  }

  // ----------------- Types (Ty grammar) -----------------
  private def mkArrow(left: TypeTerm, right: TypeTerm): TypeTerm =
    Term.Forall(Binder(SRelevance.Rel, "_", left), right)

  private def parseType(): TypeTerm = {
    // ForallTy | ArrowTy
    if (optSym("forall")) {
      val b = parseSingleBinder(); sym("->"); val body = parseType(); Term.Forall(b, body)
    } else parseArrowType()
  }

  private def parseArrowType(): TypeTerm = {
    val left: TypeTerm = parseAppType()
    skipWhitespace()
    if (startsWith("->")) { sym("->"); val rhs = parseType(); mkArrow(left, rhs) }
    else left
  }

  private def parseAppType(): TypeTerm = {
    var head: TypeTerm = parseTypeAtom()
    var continue = true
    while (continue) {
      val save = pos
      try {
        val a = parseTypeAtom()
        head = Term.App(head, a)
      } catch {
        case _: ParseError =>
          i = save; continue = false
      }
    }
    head
  }

  private def parseTypeAtom(): TypeTerm = {
    skipWhitespace()
    if (startsWith("Type")) {
      expect("Type")
      if (optSym("_")) Term.TypeHole
      else { val l = parseLevel(); Term.Type(l) }
    } else if (optSym("(")) {
      val t = parseType(); sym(")"); t
    } else {
      Term.Ident(readName())
    }
  }

  // ----------------- Binders and params -----------------
  private def parseNameColonTy(): (List[String], TypeTerm) = {
    // Support grouped binders: x y z : T
    val names = scala.collection.mutable.ListBuffer.empty[String]
    names += readName()
    // consume additional names until ':'
    var cont = true
    while (cont) {
      val save = pos
      try {
        // if next token is ':', stop reading names
        skipWhitespace();
        if (startsWith(":")) cont = false
        else names += readName()
      } catch {
        case _: ParseError => i = save; cont = false
      }
    }
    sym(":"); val t = parseType(); (names.toList, t)
  }

  private def parseBinderGroup(): List[Binder] = {
    skipWhitespace();
    if (!optSym("(")) fail("expected '('")
    val irr = optSym(".")
    val (ns, t) = parseNameColonTy()
    sym(")")
    val rel = if (irr) SRelevance.Irr else SRelevance.Rel
    ns.map(n => Binder(rel, n, t))
  }

  private def parseParams(): List[Binder] = {
    val buf = scala.collection.mutable.ListBuffer.empty[Binder]
    var keep = true
    while (keep) {
      val save = pos
      try { buf ++= parseBinderGroup() }
      catch { case _: ParseError => i = save; keep = false }
    }
    buf.toList
  }

  // ----------------- Terms -----------------
  private def parseTerm(): Term = {
    // let ... | \\ binder => term | forall binder -> term | match ... | implicit[...] | ?hole | ascription | application
    if (startsWith("let")) return parseLet()
    if (startsWith("\\")) return parseLam()
    if (startsWith("forall")) {
      expect("forall"); val b = parseSingleBinder(); sym("->"); val body = parseTerm(); return Term.Forall(b, body.asInstanceOf[TypeTerm])
    }
    if (startsWith("match")) return parseMatch()
    if (startsWith("implicit")) return parseImplicitSite()
    if (startsWith("?")) { sym("?"); val n = readName(); return Term.Hole(n) }
    parseAppTerm()
  }

  private def parseLet(): Term = {
    expect("let"); val n = readName(); sym(":"); val ty = parseType(); sym(":="); val v = parseTerm(); expect("in"); val body = parseTerm();
    Term.Let(n, ty, v, body)
  }

  private def parseLam(): Term = {
    sym("\\"); val b = parseSingleBinder(); sym("=>"); val body = parseTerm(); Term.Lam(b, body)
  }

  private def parseSingleBinder(): Binder = {
    val bs = parseBinderGroup()
    if (bs.lengthCompare(1) != 0) fail("expected a single binder")
    bs.head
  }

  private def parseMatch(): Term = {
    expect("match"); val scrut = parseTerm(); expect("as"); val w = readName(); expect("returning"); val mot = parseType(); expect("with"); sym("{")
    val cases = scala.collection.mutable.ListBuffer.empty[Case]
    while (!optSym("}")) {
      sym("|"); val pat = parsePattern(); sym("=>"); val body = parseTerm(); cases += Case(pat, body)
    }
    Term.Match(scrut, w, mot, cases.toList)
  }

  private def parseImplicitSite(): Term = {
    expect("implicit"); sym("["); val t = parseTerm(); sym("]"); Term.ImplicitSite(t)
  }

  private def parseAscribedOrParenedOrAtomTerm(): Term = {
    skipWhitespace()
    if (optSym("(")) {
      // Could be (term : type) or parenthesized term. Spec only lists ascription; allow both.
      val save = pos
      val t = parseTerm()
      if (optSym(":")) { val ty = parseType(); sym(")"); Term.Ascribe(t, ty) }
      else { sym(")"); t }
    } else if (startsWith("Type")) {
      expect("Type")
      if (optSym("_")) Term.TypeHole else { val l = parseLevel(); Term.Type(l) }
    } else {
      Term.Ident(readName())
    }
  }

  private def parseAppTerm(): Term = {
    var head: Term = parseAscribedOrParenedOrAtomTerm()
    var continue = true
    while (continue) {
      val save = pos
      try {
        val a = parseAscribedOrParenedOrAtomTerm()
        head = Term.App(head, a)
      } catch {
        case _: ParseError => i = save; continue = false
      }
    }
    head
  }

  private def parsePattern(): Pattern = {
    val name = readName()
    val binders = scala.collection.mutable.ListBuffer.empty[String]
    var cont = true
    while (cont) {
      val save = pos
      try { binders += readName() } catch { case _: ParseError => i = save; cont = false }
    }
    Pattern.Ctor(name, binders.toList)
  }

  // ----------------- Declarations -----------------
  private def parseLevelParamsOpt(): List[String] = {
    // .{ ident (, ident)* }
    skipWhitespace()
    if (!optSym(".")) return Nil
    sym("{")
    val names = scala.collection.mutable.ListBuffer.empty[String]
    names += readName()
    while (optSym(",")) { names += readName() }
    sym("}")
    names.toList
  }

  private def parseDataDecl(): Decl.Data = {
    expect("data"); val nm = readName(); val lps = parseLevelParamsOpt(); val ps = parseParams(); sym(":"); val resTy = parseType(); expect("where"); sym("{")
    val ctors = scala.collection.mutable.ListBuffer.empty[Ctor]
    while (!optSym("}")) {
      sym("|"); val cn = readName(); val bs = parseParams(); sym(":"); val cty = parseType(); ctors += Ctor(cn, bs, cty)
    }
    Decl.Data(nm, lps, ps, resTy, ctors.toList)
  }

  private def parseDefDecl(isInline: Boolean): Decl.Def = {
    expect("def"); val nm = readName(); val lps = parseLevelParamsOpt(); val ps = parseParams(); sym(":"); val ty = parseType(); sym(":="); val body = parseTerm()
    Decl.Def(isInline, nm, lps, ps, ty, body)
  }

  private def parseTheoremDecl(): Decl.Theorem = {
    expect("theorem"); val nm = readName(); val lps = parseLevelParamsOpt(); val ps = parseParams(); sym(":"); val ty = parseType(); sym(":="); val body = parseTerm()
    Decl.Theorem(nm, lps, ps, ty, body)
  }

  private def parseAxiomDecl(): Decl.Axiom = {
    expect("axiom"); val nm = readName(); val lps = parseLevelParamsOpt(); val ps = parseParams(); sym(":"); val ty = parseType()
    Decl.Axiom(nm, lps, ps, ty)
  }

  def parseDecl(): Decl = {
    skipWhitespace()
    if (startsWith("inline")) { expect("inline"); parseDefDecl(isInline = true) }
    else if (startsWith("data")) parseDataDecl()
    else if (startsWith("def")) parseDefDecl(isInline = false)
    else if (startsWith("theorem")) parseTheoremDecl()
    else if (startsWith("axiom")) parseAxiomDecl()
    else fail("expected a declaration")
  }

  def parseDecls(): List[Decl] = {
    val buf = scala.collection.mutable.ListBuffer.empty[Decl]
    while (!eof) { buf += parseDecl() }
    buf.toList
  }
}

object SurfaceParserRec {
  final case class Result[+A](value: A)
  final case class Error(msg: String) extends Exception(msg)

  private def run[A](src: String)(k: SurfaceParserRec => A): Either[String, A] = {
    try Right(k(new SurfaceParserRec(src)))
    catch { case e: ParseError => Left(e.getMessage) }
  }

  def parseDecl(src: String): Either[String, Decl] = run(src)(_.parseDecl())
  def parseDecls(src: String): Either[String, List[Decl]] = run(src)(_.parseDecls())
}

final class ParseError(msg: String) extends RuntimeException(msg)
