package com.raccoonlang

/**
 * A wildcard case (docs/implemented/WILDCARD_CASE.md): `| _ => e`, last in its match, stands for one case per reachable
 * constructor no other case names, each binding its fields anonymously and checking `e` under its own refinement. The
 * residual is that expansion.
 */
class WildcardCaseTests extends munit.FunSuite with TestSupport {

  /** A family of four constructors, one with a field. */
  private val color =
    """
      |inductive Color : Type
      | | red : Color
      | | green : Color
      | | blue : Color
      | | other (n: Nat) : Color
      |""".stripMargin

  /** `Shape(n)` has no constructor in common between index 0 and index 1. */
  private val shape =
    """
      |inductive Shape indices (n: Nat) : Type
      | | point : Shape(Nat.zero)
      | | line (a: Nat) : Shape(Nat.succ(Nat.zero))
      | | square (a: Nat) : Shape(Nat.succ(Nat.zero))
      |""".stripMargin

  private def parseError(source: String): (String, Int) =
    LanguageParser.parseProgram(source) match {
      case Failure(_, curIdx, message) => (message, curIdx)
      case _: Success[_]               => fail(s"expected a parse error in:\n$source")
    }

  private def evaluatesAlike(left: String, right: String)(implicit loc: munit.Location): Unit = {
    val (l, r) = (runProgram(left), runProgram(right))
    assert(ValueEquivalence.defEq(l, r), s"${PrettyPrinter.print(l)} vs ${PrettyPrinter.print(r)}")
  }

  test("a wildcard over the rest is accepted and evaluates as the written-out match") {
    // The body holds a lambda, one term in each case it is expanded into.
    val wildcard =
      color +
        """
          |def code (c: Color): Nat := match c returning Nat with
          | | Color.green => 1
          | | _ => (fun (x: Nat): Nat => Nat.add(x, 1))(4)
          |""".stripMargin
    val writtenOut =
      color +
        """
          |def code (c: Color): Nat := match c returning Nat with
          | | Color.green => 1
          | | Color.red => (fun (x: Nat): Nat => Nat.add(x, 1))(4)
          | | Color.blue => (fun (x: Nat): Nat => Nat.add(x, 1))(4)
          | | Color.other _ => (fun (x: Nat): Nat => Nat.add(x, 1))(4)
          |""".stripMargin
    Vector("Color.red", "Color.green", "Color.blue", "Color.other(7)").foreach { c =>
      evaluatesAlike(wildcard + s"{ code($c) }\n", writtenOut + s"{ code($c) }\n")
    }
    evaluatesAlike(wildcard + "{ code(Color.blue) }\n", "{ 5 }\n")
    evaluatesAlike(wildcard + "{ code(Color.green) }\n", "{ 1 }\n")
  }

  test("a wildcard after every constructor is RedundantCase, located at it") {
    val source =
      color +
        """
          |def code (c: Color): Nat := match c returning Nat with
          | | Color.red => 0
          | | Color.green => 0
          | | Color.blue => 0
          | | Color.other n => n
          | | _ => 1
          |""".stripMargin
    val diagnostic = interceptDiagnostic(typecheckDecls(source))
    assertEquals(diagnostic.error, RedundantCase)
    assertEquals(diagnostic.span.map(_.start), Some(source.indexOf("| _ =>")))
    // A scrutinee in constructor form needs its own constructor's case alone.
    val known = color + "def code : Nat := match Color.red returning Nat with\n | Color.red => 0\n | _ => 1\n"
    assertEquals(interceptError[RedundantCase.type](typecheckDecls(known)), RedundantCase)
    typecheckDecls(color + "def code : Nat := match Color.red returning Nat with\n | _ => 1\n")
  }

  test("a wildcard not last, twice, or binding fields is a parse error") {
    val lastOnly =
      "A wildcard case is the last case of its match; a nested match takes every case after it, so brace it"
    val notLast = color + "def f (c: Color): Nat := match c returning Nat with\n | _ => 1\n | Color.red => 0\n"
    assertEquals(parseError(notLast), (lastOnly, notLast.indexOf("| _")))
    val twice = color + "def f (c: Color): Nat := match c returning Nat with\n | Color.red => 0\n | _ => 1\n | _ => 2\n"
    assertEquals(parseError(twice), (lastOnly, twice.indexOf("| _")))
    val fields = color + "def f (c: Color): Nat := match c returning Nat with\n | Color.red => 0\n | _ n => 1\n"
    assertEquals(parseError(fields), ("A wildcard case binds no fields", fields.indexOf("n => 1")))
  }

  test("a wildcard does not stand for a constructor apart from the scrutinee's type") {
    val source =
      shape +
        """
          |def size (s: Shape(1)): Nat := match s returning Nat with
          | | Shape.line a => a
          | | _ => 0
          |""".stripMargin
    typecheckDecls(source)
    evaluatesAlike(source + "{ size(Shape.square(3)) }\n", "{ 0 }\n")
    // Its only other reachable constructor named, the wildcard stands for none, though `point` has no case.
    val redundant =
      shape +
        """
          |def size (s: Shape(1)): Nat := match s returning Nat with
          | | Shape.line a => a
          | | Shape.square a => a
          | | _ => 0
          |""".stripMargin
    assertEquals(interceptError[RedundantCase.type](typecheckDecls(redundant)), RedundantCase)
  }

  test("the wildcard's body is checked under each constructor's refinement, and a failure names the constructor") {
    // `Out(c)` is stuck on a variable and computes only once a case refines `c`.
    def program(blue: String): String =
      color +
        s"""
           |def Out (c: Color): Type := match c returning Type with
           | | Color.red => Bool
           | | Color.green => Nat
           | | Color.blue => $blue
           | | Color.other _ => Nat
           |
           |def pick (c: Color): Out(c) := match c returning Out(c) with
           | | Color.red => Bool.true
           | | _ => 3
           |""".stripMargin
    typecheckDecls(program("Nat"))
    evaluatesAlike(program("Nat") + "{ pick(Color.other(9)) }\n", "{ 3 }\n")
    val source = program("Bool")
    val diagnostic = interceptDiagnostic(typecheckDecls(source))
    assert(diagnostic.error.isInstanceOf[TypeMismatch], diagnostic.error.toString)
    assert(diagnostic.frames.contains(Frame.InWildcard("Color.blue")), diagnostic.frames.toString)
    assertEquals(diagnostic.span.map(_.start), Some(source.indexOf("3\n")))
    assert(
      ErrorReporter
        .pretty(diagnostic, ErrorReporter.Source(source), None)
        .contains("in the wildcard case for Color.blue")
    )
  }

  test("a wildcard over a constructor with a linear field is LinearUnused at the wildcard") {
    val families =
      """
        |inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
        | | mk : Tok(l)
        |
        |def eat {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with
        | | Tok.mk => 0
        |
        |inductive Bag (l: Lifetime) : Type { kind = lin, scope = l }
        | | empty : Bag(l)
        | | one (t: Tok(l)) : Bag(l)
        |""".stripMargin
    val unused =
      families + "def f {l: Lifetime}(b: Bag(l)): Nat := match b returning Nat with\n | Bag.empty => 0\n | _ => 1\n"
    val diagnostic = interceptDiagnostic(typecheckDecls(unused))
    assertEquals(diagnostic.error, LinearUnused("_"))
    assertEquals(diagnostic.span.map(_.start), Some(unused.indexOf("| _ =>")))
    // A linear local the body uses is used once on the path through each case the wildcard stands for.
    typecheckDecls(
      families + color +
        "def g {l: Lifetime}(t: Tok(l))(c: Color): Nat := match c returning Nat with\n" +
        " | Color.red => eat(t)\n | _ => eat(t)\n"
    )
  }

  test("a recursive call in a wildcard's body is checked in each case it stands for") {
    // `proj(t)` reduces to a field of `t` under `T.a`'s refinement but to `t` itself under `T.b`'s, so the call
    // decreases in one expansion and not in the other.
    val source =
      """
        |inductive T : Type
        | | a (x: T) : T
        | | b (x: T) : T
        | | leaf : T
        |
        |def proj (t: T): T := match t returning T with
        | | T.a x => x
        | | T.b x => t
        | | T.leaf => t
        |
        |def f (t: T): Nat decreases structural(t) := match t returning Nat with
        | | T.leaf => 0
        | | _ => f(proj(t))
        |""".stripMargin
    val diagnostic = interceptDiagnostic(typecheckDecls(source))
    assert(diagnostic.error.isInstanceOf[NonDecreasingRecursiveCall], diagnostic.error.toString)
    assert(diagnostic.frames.contains(Frame.InWildcard("T.b")), diagnostic.frames.toString)
    assert(!diagnostic.frames.contains(Frame.InWildcard("T.a")), diagnostic.frames.toString)
    // A call on a smaller argument the wildcard's body sees is admitted in each case.
    val decreasing =
      color +
        """
          |def walk (n: Nat)(c: Color): Nat decreases structural(n) := match n returning Nat with
          | | Nat.zero => 0
          | | Nat.succ m => match c returning Nat with
          |   | Color.red => walk(m, c)
          |   | _ => Nat.add(walk(m, Color.red), 1)
          |""".stripMargin
    evaluatesAlike(decreasing + "{ walk(3, Color.blue) }\n", "{ 1 }\n")
  }

  test("a stuck match's residual prints the expansion") {
    val prelude = TestSupport.preludeAssuming(TestSupport.bundledPreludeSource, color + "\naxiom c : Color\n")
    val source = "{ match c returning Nat with\n | Color.red => 1\n | _ => 0\n}\n"
    assertEquals(
      PrettyPrinter.print(runProgram(source, prelude)),
      "match c returning Nat with | Color.red => 1 | Color.green => 0 | Color.blue => 0 | Color.other _ => 0"
    )
  }

  // Each case the wildcard stands for has its own copy of the body, as the written-out match has: a `scope` in it opens
  // a different atom in each case, so the closures two cases return are different functions.
  test("each case a wildcard stands for has a body of its own") {
    val prelude = TestSupport.preludeAssuming(TestSupport.bundledPreludeSource, "axiom stuckL (l: Lifetime) : Nat\n")
    def program(cases: String, name: String): String =
      color +
        s"def $name (c: Color): Nat -> Nat := match c returning Nat -> Nat with\n" +
        " | Color.red => fun (x: Nat): Nat => x\n" +
        s"$cases\n\n" +
        s"def same : Eq(Nat -> Nat, $name(Color.green), $name(Color.blue)) := Eq.refl($name(Color.green))\n"
    val body =
      "fun (x: Nat): Nat => scope l => {\n   match x returning Nat with\n   | Nat.zero => stuckL(l)\n   | Nat.succ _ => 0\n }"
    val wildcard = program(s" | _ => $body", "wild")
    val writtenOut =
      program(
        Vector("Color.green", "Color.blue", "Color.other _").map(c => s" | $c => $body").mkString("\n"),
        "written"
      )
    interceptError[TypeMismatch](typecheckDecls(writtenOut, prelude))
    interceptError[TypeMismatch](typecheckDecls(wildcard, prelude))
  }

  // The residual lists its cases in declaration order, so a wildcard match converts with the match written out in
  // that order, whatever order its own cases are written in.
  test("a wildcard's residual converts with the match written out in declaration order") {
    val source =
      color +
        """
          |def wild (c: Color): Nat := match c returning Nat with
          | | Color.blue => 1
          | | _ => 0
          |
          |def declOrder (c: Color): Nat := match c returning Nat with
          | | Color.red => 0
          | | Color.green => 0
          | | Color.blue => 1
          | | Color.other _ => 0
          |
          |def same (c: Color): Eq(Nat, wild(c), declOrder(c)) := Eq.refl(wild(c))
          |""".stripMargin
    typecheckDecls(source)
  }
}
