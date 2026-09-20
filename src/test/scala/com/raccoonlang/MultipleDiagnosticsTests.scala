package com.raccoonlang

import java.nio.file.Paths

/**
 * Reporting every independent mistake a program has, and nothing else.
 *
 * What is asserted here is the driver's judgment about which declarations are worth checking at all: a second mistake
 * is reported, a consequence of the first is not, and a block is one decision rather than several.
 */
class MultipleDiagnosticsTests extends munit.FunSuite with TestSupport {
  override protected def suitePrelude: Prelude.Config = Prelude.default

  private def diagnosticsOf(source: String): Vector[Diagnostic] =
    interceptDiagnostics(TypeChecker.check(Elaborator.elaborate(parseSurface(source), suitePrelude)))

  private def definitionsNamed(diagnostics: Vector[Diagnostic]): Vector[String] =
    diagnostics.map(_.frames.collect { case Frame.InDefinition(name) => name }.mkString)

  test("two independent errors are both reported, in source order") {
    val diagnostics = diagnosticsOf(
      """
        |def first : Nat := Bool.true
        |def second : Nat := Bool.false
        |""".stripMargin
    )
    assertEquals(diagnostics.length, 2)
    assertEquals(definitionsNamed(diagnostics), Vector("first", "second"))
    assert(diagnostics.forall(_.error.isInstanceOf[TypeMismatch]))
    // Source order, which for these two is also the order their spans appear in the file.
    assert(diagnostics(0).span.get.start < diagnostics(1).span.get.start)
  }

  test("a declaration that uses a failed one is skipped rather than reported again") {
    val diagnostics = diagnosticsOf(
      """
        |def broken : Nat := Bool.true
        |def usesBroken : Nat := broken
        |""".stripMargin
    )
    assertEquals(definitionsNamed(diagnostics), Vector("broken"))
    // The cascade the skip exists to prevent: `broken` was never published, so checking `usesBroken`
    // could only have produced a NotFound about a name the program does define.
    assert(!diagnostics.exists(_.error.isInstanceOf[NotFound]))
  }

  test("skipping is transitive") {
    val diagnostics = diagnosticsOf(
      """
        |def broken : Nat := Bool.true
        |def middle : Nat := broken
        |def outer : Nat := middle
        |""".stripMargin
    )
    assertEquals(definitionsNamed(diagnostics), Vector("broken"))
  }

  test("a later independent error is still reported after a skipped declaration") {
    val diagnostics = diagnosticsOf(
      """
        |def broken : Nat := Bool.true
        |def usesBroken : Nat := broken
        |def alsoBroken : Nat := Bool.false
        |""".stripMargin
    )
    assertEquals(definitionsNamed(diagnostics), Vector("broken", "alsoBroken"))
  }

  test("an inductive block fails as one unit, and its constructors count as unavailable") {
    val diagnostics = diagnosticsOf(
      """
        |inductive Bad : Type
        | | good : Bad
        | | wrong : Nat
        |
        |def usesCtor : Bad := Bad.good
        |
        |def independent : Nat := Bool.true
        |""".stripMargin
    )
    // One report for the whole family, named after the family rather than the constructor that broke it,
    // and nothing for the declaration that names a constructor the family never published.
    assertEquals(definitionsNamed(diagnostics), Vector("Bad", "independent"))
    assertEquals(diagnostics.head.error.getClass.getSimpleName, "InvalidConstructorResult")
  }

  test("a mutual recursive block fails as one unit") {
    val diagnostics = diagnosticsOf(
      """
        |mutual {
        |  def even (n: Nat): Bool decreases structural(n) := odd(n)
        |  def odd (n: Nat): Bool decreases structural(n) := Bool.true
        |}
        |
        |def independent : Nat := Bool.true
        |""".stripMargin
    )
    assertEquals(diagnostics.length, 2)
    assertEquals(definitionsNamed(diagnostics), Vector("even, odd", "independent"))
  }

  test("the final expression is not evaluated when a declaration failed") {
    // `good` checks, so without the zero-error rule the body would evaluate and this would not fail at all.
    val diagnostics = diagnosticsOf(
      """
        |def broken : Nat := Bool.true
        |def good : Nat := Nat.zero
        |{ good }
        |""".stripMargin
    )
    assertEquals(definitionsNamed(diagnostics), Vector("broken"))
  }

  test("a failure in the final expression alone still leaves as a CheckFailure") {
    // The checked stage has exactly one failure shape, so a body-only rejection is not a special case.
    val failure = intercept[Execution.CheckFailure] {
      TypeChecker.check(Elaborator.elaborate(parseSurface("{ Nat.add(Nat.zero) }\n"), suitePrelude))
    }
    assertEquals(failure.diagnostics.length, 1)
    assert(failure.diagnostics.head.error.isInstanceOf[ArityMismatch])
  }

  test("the trusted prelude still fails fast, on the first bad declaration") {
    // A prelude is the bootstrap: the rest of it is checked against what its earlier declarations published,
    // so continuing past a failure would check the remainder against an environment that is not the prelude.
    // This one has two bad declarations and must report only the first.
    val bad =
      Prelude.fromSource(
        "two-bad-decls",
        """
          |inductive Box : Type
          | | unit : Box
          |
          |def first : Box := Type
          |
          |def second : Box := Type
          |""".stripMargin,
        Set.empty
      )
    val diagnostic = intercept[Diagnostic](bad.checkedEnv)
    assertEquals(diagnostic.frames.collect { case Frame.InDefinition(name) => name }, Vector("first"))
  }

  test("a clean program still runs") {
    assertEquals(
      ctorName(runProgram("def a : Nat := Nat.zero\ndef b : Nat := a\n{ b }\n")),
      "Nat.zero"
    )
  }

  test("the JSON report names each diagnostic's position, kind, message and notes") {
    val source = "def first : Nat := Bool.true\ndef second : Nat := Bool.false\n"
    val sources = Vector(ModuleLoader.LoadedSource(SourceId.fresh(), Paths.get("main.rac"), source))
    // The diagnostics must name that source, as a real load would: the encoder resolves a span's source id.
    val located =
      diagnosticsOf(source).map(diagnostic =>
        diagnostic.copy(span = diagnostic.span.map(_.copy(source = Some(sources.head.sourceId))))
      )
    val json = DiagnosticJson.render(located, sources)

    assert(json.startsWith("[\n"), json)
    assert(json.endsWith("\n]"), json)
    assertEquals(json.linesIterator.count(_.trim.startsWith("{")), 2)
    assert(json.contains("\"path\": \"main.rac\""), json)
    assert(json.contains("\"startLine\": 1, \"startColumn\": 20"), json)
    assert(json.contains("\"severity\": \"error\""), json)
    assert(json.contains("\"kind\": \"TypeMismatch\""), json)
    // The message is the same text the human report prints, with its newlines escaped rather than emitted.
    assert(json.contains("""\n  expected: Nat\n  actual:   Bool"""), json)
    assert(json.contains("""["in definition first"]"""), json)
    assert(!json.contains("\n  expected"), "a raw newline escaped into the JSON")
  }

  test("a run that found nothing still renders an array") {
    // Empty stdout would leave a tool unable to tell a clean check from a run that printed nothing at all.
    assertEquals(DiagnosticJson.render(Vector.empty, Vector.empty), "[]")
  }
}
