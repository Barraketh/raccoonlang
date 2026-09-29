package com.raccoonlang

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
 * Each `expected.txt` is a golden (`Goldens`), so its diff is the review artifact for any change to error reporting.
 */
class DiagnosticSnapshotTests extends munit.FunSuite with Goldens {
  private val casesRoot: Path = Paths.get("src", "test", "resources", "diagnostics").toAbsolutePath.normalize

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
      assertGolden(caseDir.resolve("expected.txt"), normalize(render(caseDir.resolve("main.rac")), caseDir))
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

  /** The error classes a case's program is rejected with, in source order; none when it is accepted. */
  private def reportedErrors(entry: Path): Vector[String] = {
    val prelude = Prelude.default
    val diagnostics =
      try {
        val loaded = ModuleLoader.load(entry, ModuleLoader.LoadConfig(Vector(entry.getParent), prelude))
        TypeChecker.check(Elaborator.elaborate(loaded.program, prelude))
        Vector.empty
      } catch {
        case Execution.CheckFailure(diagnostics)     => diagnostics
        case diagnostic: Diagnostic                  => Vector(diagnostic)
        case ModuleLoader.LoadFailure(diagnostic, _) => Vector(diagnostic)
      }
    diagnostics.map(_.error.getClass.getSimpleName)
  }

  /**
   * Spec §9's diagnostics, which are every diagnostic the lifetimes, linearity and sealing design added: each has a
   * snapshot case named after it that reports it and nothing else, and some test expects it as a program's only error.
   */
  test("every diagnostic spec §9 lists has its own snapshot case and a test that expects it alone") {
    val spec = Files.readString(Paths.get("docs", "LEMUR_ON_RACCOON.md"))
    val section = spec.substring(spec.indexOf("## 9. Diagnostics"))
    val block = section.substring(section.indexOf("```text") + "```text".length)
    val listed = block.substring(0, block.indexOf("```")).split("[,\\s]+").filter(_.nonEmpty).toVector
    assert(listed.length >= 10, listed)
    val tests =
      Files
        .walk(Paths.get("src", "test", "scala"))
        .iterator()
        .asScala
        .filter(_.toString.endsWith(".scala"))
        .map(Files.readString(_))
        .mkString
    val gaps = listed.flatMap { name =>
      val caseDir = casesRoot.resolve(name.replaceAll("([a-z])([A-Z])", "$1-$2").toLowerCase)
      val snapshot =
        if (!Files.isDirectory(caseDir)) Some(s"$name: no snapshot case ${caseDir.getFileName}")
        else {
          val reported = reportedErrors(caseDir.resolve("main.rac"))
          Option.when(reported.isEmpty || reported.exists(_ != name))(
            s"$name: snapshot case ${caseDir.getFileName} reports ${reported.mkString("[", ", ", "]")}"
          )
        }
      snapshot ++ Option.when(!tests.contains(s"expectOnly[$name]"))(s"$name: no expectOnly[$name] test")
    }
    assertEquals(gaps, Vector.empty[String])
  }
}
