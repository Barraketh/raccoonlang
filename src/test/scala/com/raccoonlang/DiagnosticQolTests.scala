package com.raccoonlang

class DiagnosticQolTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.default

  private def missing(source: String, name: String, written: String)(implicit loc: munit.Location): Unit = {
    val diagnostic = interceptDiagnostic(typecheckDecls(source))
    assertEquals(diagnostic.error, NotFound(name))
    assertEquals(diagnostic.span.map(span => source.substring(span.start, span.end)), Some(written))
  }

  private def arityMessage(source: String)(implicit loc: munit.Location): String =
    ErrorRendering.render(expectTypeError[ArityMismatch](source))

  test("unknown qualified names report the selected name in terms and types") {
    missing("{ Nat.missing }", "Nat.missing", "Nat.missing")
    missing("{ List.missing }", "List.missing", "List.missing")
    missing("def f (n: Nat.Missing): Nat := 0", "Nat.Missing", "Nat.Missing")
  }

  test("a named function's arity error gives its explicit parameter names") {
    val source = "def choose (first: Nat)(second: Nat): Nat := first\n{ choose(Nat.zero) }\n"
    assertEquals(
      arityMessage(source),
      "Cannot apply choose - expected 2 params (first, second), got 1"
    )
  }

  test("a constructor's arity error names explicit parameters and implicit family parameters") {
    val source =
      """struct Cell (A: Type)(n: Nat) : Type
        | | mk (value: A)(index: Nat) : Cell(A, n)
        |
        |{ Cell.mk(Nat.zero, Nat.zero) }
        |""".stripMargin
    assertEquals(
      arityMessage(source),
      "Cannot apply Cell.mk - expected 3 params (n, value, index), got 2; " +
        "family parameter A is implicit, determined by the other arguments"
    )
    assertEquals(
      arityMessage("{ List.nil() }"),
      "Cannot apply List.nil - expected 1 params (A), got 0; " +
        "family parameter u is implicit, determined by the other arguments"
    )
  }

  test("an anonymous function uses a generic name and retains its parameter names") {
    assertEquals(
      arityMessage("{ (fun (n: Nat): Nat => n)(Nat.zero, Nat.zero) }"),
      "Cannot apply function - expected 1 params (n), got 2"
    )
  }
}
