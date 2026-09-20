package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}
import scala.jdk.CollectionConverters._
import scala.util.control.NonFatal

/**
 * End-to-end snapshots of what a failing program actually prints.
 *
 * Each case is a directory under `src/test/resources/diagnostics` holding `main.rac` (the entry), any modules it
 * imports, and `expected.txt` — the full rendered report, with the source root replaced by `<root>` so the file is
 * machine independent. A case whose program is expected to fail but does not, or that fails somewhere the reporter
 * cannot render, is itself a snapshot: the harness records that outcome verbatim rather than hiding it.
 *
 * Regenerate every expectation with `sbt -batch -Draccoon.diagnostics.regenerate=true test`, then read the diff: it is
 * the review artifact for any change to error reporting.
 */
class DiagnosticSnapshotTests extends munit.FunSuite {
  private val casesRoot: Path = Paths.get("src", "test", "resources", "diagnostics").toAbsolutePath.normalize
  private val regenerate: Boolean = sys.props.get("raccoon.diagnostics.regenerate").contains("true")

  private def caseDirs: Vector[Path] =
    Files
      .list(casesRoot)
      .iterator()
      .asScala
      .filter(Files.isDirectory(_))
      .toVector
      .sortBy(_.getFileName.toString)

  /** The rendered report, or the description of an outcome that produced no report. */
  private def render(entry: Path): String = {
    val prelude = Prelude.default
    val config = ModuleLoader.LoadConfig(Vector(entry.getParent), prelude)
    try {
      val loaded = ModuleLoader.load(entry, config)
      try {
        val checked = TypeChecker.check(Elaborator.elaborate(loaded.program, prelude))
        Interpreter.run(checked) match {
          case Some(value) => s"NO ERROR: program evaluated to ${PrettyPrinter.print(value)}"
          case None        => "NO ERROR: program has no body"
        }
      } catch {
        case Execution.CheckFailure(diagnostics) => ErrorReporter.pretty(diagnostics, loaded.sources)
        case diagnostic: Diagnostic              => ErrorReporter.pretty(diagnostic, loaded)
        case internal: InternalError             => ErrorReporter.pretty(internal, loaded.sources)
      }
    } catch {
      case ModuleLoader.LoadFailure(diagnostic, sources) => ErrorReporter.pretty(diagnostic, sources)
      case internal: InternalError                       => ErrorReporter.pretty(internal, Vector.empty)
      case NonFatal(error)                               => s"UNREPORTED ${error.getClass.getName}: ${error.getMessage}"
    }
  }

  /**
   * Machine- and run-independent form of a report.
   *
   * Fresh-var and source ids come from allocators that keep counting across a whole test run, so the number a report
   * happens to print depends on which suites ran before it. Only the numbers are masked, never the surrounding text: an
   * id leaking into a user-facing message is itself part of what these snapshots record.
   */
  private def normalize(report: String, caseDir: Path): String =
    report
      .replace(caseDir.toRealPath().toString, "<root>")
      .replace(caseDir.toString, "<root>")
      .replaceAll("""#\d+""", "#N")
      .replaceAll("""SourceId\(\d+\)""", "SourceId(N)")

  caseDirs.foreach { caseDir =>
    val name = caseDir.getFileName.toString
    test(s"diagnostic snapshot: $name") {
      val expectedFile = caseDir.resolve("expected.txt")
      val actual = normalize(render(caseDir.resolve("main.rac")), caseDir)
      if (regenerate) Files.write(expectedFile, actual.getBytes(StandardCharsets.UTF_8))
      else {
        assert(Files.isRegularFile(expectedFile), s"missing expectation $expectedFile; regenerate the snapshots")
        assertNoDiff(actual, Files.readString(expectedFile))
      }
    }
  }

  test("every snapshot case reports a diagnostic") {
    val unreported =
      caseDirs.filter { caseDir =>
        val expected = caseDir.resolve("expected.txt")
        Files.isRegularFile(expected) && {
          val text = Files.readString(expected)
          text.startsWith("NO ERROR") || text.startsWith("UNREPORTED") || text.startsWith("internal kernel error")
        }
      }
    assertEquals(unreported.map(_.getFileName.toString), Vector.empty[String])
  }
}
