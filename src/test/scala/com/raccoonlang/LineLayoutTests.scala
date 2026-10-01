package com.raccoonlang

/**
 * Wherever a line break separates two items, any number of blank lines and comment-only lines may stand in its place:
 * between a block's statements and around them, between a match's cases, between an inductive's constructors and after
 * the last one, between imports, around a definition's `decreases` keyword. Cases and constructors still begin on their
 * own lines (ParseErrorTests).
 *
 * Each program is a vector of lines. It is run once with every separating line break single, then once for each line
 * break and each gap standing in its place, and must mean the same every time.
 */
class LineLayoutTests extends munit.FunSuite with TestSupport {

  /** What may stand in place of one line break: blank lines, comment-only lines, or both. */
  private val gaps = Vector("\n\n", "\n  // a comment\n", "\n\n  // one\n\n// two\n\n")

  /** `lines` joined by single line breaks, except the break before `lines(at)`, which `gap` replaces. */
  private def joined(lines: Vector[String], at: Int, gap: String): String =
    lines.head + lines.indices.tail.map(i => (if (i == at) gap else "\n") + lines(i)).mkString

  /** `lines` evaluates to `expected` joined by single line breaks, and with each gap at each line break. */
  private def everyGap(lines: Vector[String], expected: String)(implicit loc: munit.Location): Unit = {
    assertEquals(PrettyPrinter.print(runProgram(lines.mkString("\n"))), expected)
    for (at <- lines.indices.tail; gap <- gaps) {
      val source = joined(lines, at, gap)
      assertEquals(PrettyPrinter.print(runProgram(source)), expected, source)
    }
  }

  test("a block's statements, result and braces may be separated by blank and comment lines") {
    everyGap(
      Vector(
        "def f (n: Nat): Nat := {",
        "  let a := Nat.succ(n)",
        "  let b := Nat.succ(a)",
        "  Nat.succ(b)",
        "}",
        "{ f(0) }"
      ),
      "3"
    )
  }

  test("a match's cases may be separated by blank and comment lines") {
    everyGap(
      Vector(
        "def f (n: Nat): Nat := match n returning Nat with",
        "  | .zero => 7",
        "  | .succ k => k",
        "def g (n: Nat): Nat := {",
        "  match n returning Nat with",
        "  | .zero => 7",
        "  | .succ k => k",
        "}",
        "{ Nat.add(f(0), g(2)) }"
      ),
      "8"
    )
  }

  // The line after the last case ends the match: it is the block's next statement or its result.
  test("a match used as a let value ends at the first line that is not a case") {
    val lines = Vector(
      "def f (n: Nat): Nat := {",
      "  let m := match n returning Nat with",
      "    | .zero => 7",
      "    | .succ k => k",
      "  let r := Nat.succ(m)",
      "  Nat.succ(r)",
      "}"
    )
    everyGap(lines :+ "{ f(0) }", "9")
    everyGap(lines :+ "{ f(3) }", "4")
    everyGap(
      Vector(
        "def f (n: Nat): Nat := {",
        "  let m := match n returning Nat with",
        "    | .zero => 7",
        "    | .succ k => k",
        "  m",
        "}",
        "{ f(0) }"
      ),
      "7"
    )
  }

  test(
    "constructors, and what follows an inductive or a match without any, may be separated by blank and comment lines"
  ) {
    everyGap(
      Vector(
        "inductive Color : Type",
        "  | red : Color",
        "  | green : Color",
        "  | blue : Color",
        "struct Point : Type",
        "  | mk (x: Nat)(y: Nat) : Point",
        "inductive Void : Type",
        "def fromVoid (v: Void): Nat := match v returning Nat with",
        "def pick (c: Color): Nat := match c returning Nat with",
        "  | .red => 1",
        "  | .green => 2",
        "  | .blue => Point.mk(3, 4).y",
        "{ pick(Color.blue) }"
      ),
      "4"
    )
  }

  test("a declaration may stand on the line right after an inductive's last constructor") {
    val program = "inductive Color : Type\n  | red : Color\n  | green : Color\ndef c : Color := Color.green\n{ c }\n"
    assertEquals(ctorName(runProgram(program)), "Color.green")
  }

  test("a comment may end the line of a block's brace, a statement, a match header, a case and a constructor") {
    val program =
      """inductive Color : Type // colors
        |  | red : Color // the first
        |  | green : Color // the last
        |def f (c: Color): Nat := { // a block
        |  let m := match c returning Nat with // a match
        |    | .red => 1 // a case
        |    | .green => 2 // the other
        |  m // the result
        |} // done
        |{ f(Color.green) } // the body
        |""".stripMargin
    assertEquals(PrettyPrinter.print(runProgram(program)), "2")
  }

  // A case after a nested match's cases is the nested match's, however many lines stand between them, leaving the
  // outer match without it.
  test("a blank line does not end a nested match; a block around it does") {
    def program(inner: String, gap: String): String =
      s"def f (a: Bool)(b: Bool): Nat := match a returning Nat with\n  | .true => $inner$gap  | .false => 3\n" +
        "{ f(Bool.false, Bool.true) }\n"
    val nested = "match b returning Nat with\n    | .true => 1\n    | .false => 2"
    ("\n" +: gaps).foreach { gap =>
      assertEquals(expectTypeError[MissingCase](program(nested, gap)), MissingCase("Bool.false"))
      assertEquals(PrettyPrinter.print(runProgram(program(s"{\n    $nested\n  }", gap))), "3")
    }
  }

  // Without its clause a recursive definition is rejected, so each layout that runs has read the clause.
  test("a decreases clause may start a line after the result type, its specification too, in a mutual group too") {
    def lines(header: String => String): Vector[String] =
      Vector(
        header("def f (n: Nat): Nat"),
        "  match n returning Nat with",
        "  | .zero => 0",
        "  | .succ m => f(m)",
        "}",
        "mutual {",
        header("  def even (n: Nat): Bool"),
        "    match n returning Bool with",
        "    | .zero => Bool.true",
        "    | .succ m => odd(m)",
        "  }",
        header("  def odd (n: Nat): Bool"),
        "    match n returning Bool with",
        "    | .zero => Bool.false",
        "    | .succ m => even(m)",
        "  }",
        "}",
        "{ Bool.cond(even(4), Nat, Nat.succ(f(3)), 7) }"
      )
    everyGap(lines(head => s"$head decreases structural(n) := {"), "1")
    everyGap(lines(head => s"$head\n      decreases structural(n) := {").flatMap(_.split('\n')), "1")
    everyGap(lines(head => s"$head decreases\n      structural(n) := {").flatMap(_.split('\n')), "1")
  }

  test("imports may be separated by blank and comment lines") {
    val program = "import A\n\n// the other\nimport B\n\n{ 0 }\n"
    assert(LanguageParser.parseProgram(program).isInstanceOf[Success[_]], program)
  }
}
