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

  /**
   * The rendered report, or the description of an outcome that produced no report. The program is checked and run on
   * `TestSupport.FixtureStack`, and the prelude built before, on the test's own thread.
   */
  private def render(entry: Path): String = {
    val prelude = Prelude.default
    prelude.checkedEnv
    val config = ModuleLoader.LoadConfig(Vector(entry.getParent), prelude)
    try {
      val loaded = ModuleLoader.load(entry, config)
      try {
        val elaborated = Elaborator.elaborate(loaded.program, prelude)
        Execution.onStack(TestSupport.FixtureStack)(Interpreter.run(TypeChecker.check(elaborated))) match {
          case Some(value) => s"NO ERROR: program evaluated to ${PrettyPrinter.print(value)}"
          case None        => "NO ERROR: program has no body"
        }
      } catch {
        case Execution.CheckFailure(diagnostics, strings) => ErrorReporter.pretty(diagnostics, loaded.sources, strings)
        case diagnostic: Diagnostic                       => ErrorReporter.pretty(diagnostic, loaded, None)
        case internal: InternalError                      => ErrorReporter.pretty(internal, loaded.sources)
      }
    } catch {
      case ModuleLoader.LoadFailure(diagnostic, sources) => ErrorReporter.pretty(diagnostic, sources, None)
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
        case Execution.CheckFailure(diagnostics, _)  => diagnostics
        case diagnostic: Diagnostic                  => Vector(diagnostic)
        case ModuleLoader.LoadFailure(diagnostic, _) => Vector(diagnostic)
      }
    diagnostics.map(_.error.productPrefix)
  }

  /** Retained kind and linearity diagnostics still have localized source snapshots and direct unit coverage. */
  test("retained kind and linearity diagnostics have focused snapshots and direct tests") {
    val retained = Vector(
      "kind-exceeded" -> "KindExceeded",
      "kind-exceeded-lambda" -> "KindExceeded",
      "linear-in-type" -> "LinearInType",
      "linear-unused" -> "LinearUnused",
      "linear-unused-pattern-field" -> "LinearUnused",
      "linear-unused-wildcard" -> "LinearUnused",
      "linear-reused" -> "LinearReused",
      "linear-global" -> "LinearGlobal"
    )
    val tests =
      Files
        .walk(Paths.get("src", "test", "scala"))
        .iterator()
        .asScala
        .filter(_.toString.endsWith(".scala"))
        .map(Files.readString(_))
        .mkString
    val gaps = retained.flatMap { case (caseName, errorName) =>
      val caseDir = casesRoot.resolve(caseName)
      val snapshot =
        if (!Files.isDirectory(caseDir)) Some(s"$errorName: no snapshot case $caseName")
        else {
          val reported = reportedErrors(caseDir.resolve("main.rac"))
          Option.when(reported != Vector(errorName))(
            s"$errorName: snapshot case $caseName reports ${reported.mkString("[", ", ", "]")}"
          )
        }
      snapshot
    }
    val directlyCovered = retained.map(_._2).distinct.filterNot(name => tests.contains(s"expectOnly[$name]"))
    assertEquals(gaps ++ directlyCovered.map(name => s"$name: no expectOnly[$name] test"), Vector.empty[String])
  }
}
