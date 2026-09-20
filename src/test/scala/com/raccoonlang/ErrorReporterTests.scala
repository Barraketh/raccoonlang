package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

/**
 * The report's mechanics, exercised directly on spans the language rarely produces.
 *
 * The snapshot corpus covers what real programs print; these cover the edges it cannot reach — a span that crosses a
 * line break, a zero-width span, a position past the end of the file — where getting the arithmetic wrong would either
 * throw or silently point at nothing.
 */
class ErrorReporterTests extends munit.FunSuite {
  private def report(source: String, span: Span): String = report(source, span, Vector.empty)

  private def report(source: String, span: Span, frames: Vector[Frame]): String =
    ErrorReporter.pretty(Diagnostic(NotFound("x"), Some(span), frames), Source(source))

  private def lines(report: String): Vector[String] = report.linesIterator.toVector

  test("positions are 1-based in both coordinates") {
    // "b" is at offset 2: the second line's first character.
    val out = lines(report("a\nb\n", Span(2, 3)))
    assertEquals(out(1), "2:1: error: x not found")
    assertEquals(out(2), "b")
    assertEquals(out(3), "^")
  }

  test("the underline spans the whole range") {
    val out = lines(report("def x := abc\n", Span(9, 12)))
    assertEquals(out(2), "def x := abc")
    assertEquals(out(3), "         ^^^")
  }

  test("a zero-width span still underlines one column") {
    val out = lines(report("abc\n", Span(1, 1)))
    assertEquals(out(3), " ^")
  }

  test("a span crossing a line break is clamped to the first line") {
    val out = lines(report("abc\ndefgh\n", Span(1, 7)))
    assertEquals(out(1), "1:2: error: x not found")
    assertEquals(out(2), "abc")
    // Two columns remain on the first line after column 2; the underline stops there rather than
    // running into characters the excerpt does not show.
    assertEquals(out(3), " ^^")
  }

  test("a span past the end of the source is clamped rather than throwing") {
    val out = lines(report("abc\n", Span(99, 120)))
    assert(out.exists(_.contains("error: x not found")), out.mkString("\n"))
  }

  test("an unlocated diagnostic still renders") {
    val out = lines(ErrorReporter.pretty(Diagnostic(NotFound("x"), None, Vector.empty), Source("abc\n")))
    assertEquals(out(1), "1:1: error: x not found")
  }

  test("frames print as note lines, innermost first") {
    val frames =
      Vector(
        Frame.InArgument(2, "b", "f"),
        Frame.InBranch("Nat.succ", Vector("p")),
        Frame.InDefinition("g")
      )
    val out = lines(report("abc\n", Span(0, 3), frames))
    assertEquals(
      out.drop(4),
      Vector("note: in argument 2 (b) of f", "note: in branch Nat.succ p", "note: in definition g")
    )
  }

  test("a branch that binds nothing does not print a trailing space") {
    assertEquals(ErrorReporter.renderFrame(Frame.InBranch("Bool.true", Vector.empty)), "branch Bool.true")
  }

  test("the caret's prefix reproduces tabs so it stays aligned") {
    val out = lines(report("\t\tabc\n", Span(2, 5)))
    assertEquals(out(3), "\t\t^^^")
  }

  test("several diagnostics are separated by exactly one blank line") {
    val source = ModuleLoader.LoadedSource(SourceId.fresh(), java.nio.file.Paths.get("m.rac"), "abc\ndef\n")
    val span = Span(0, 3, Some(source.sourceId))
    val out =
      ErrorReporter.pretty(
        Vector(
          Diagnostic(NotFound("a"), Some(span), Vector.empty),
          Diagnostic(NotFound("b"), Some(span), Vector.empty)
        ),
        Vector(source)
      )
    assert(!out.contains("\n\n\n"), s"doubled blank line:\n$out")
    assertEquals(out.linesIterator.count(_.contains("error:")), 2)
  }
}
