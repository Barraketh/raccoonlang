package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

import CliTests.Run

/** The command line, run as its own process, since it prints to stdout and exits. */
class CliTests extends munit.FunSuite {
  private lazy val dir: Path = Files.createTempDirectory("raccoon-cli")

  /** The bundled prelude with a String layout. */
  private lazy val stringPrelude: Path =
    Files.writeString(
      dir.resolve("Prelude.rac"),
      TestSupport.bundledPreludeSource + TestSupport.stringLayoutSource("Char.mk(value)")
    )

  /**
   * Starts the CLI on `program` under the String prelude, in a locale whose encoding is ASCII, with stdin closed and
   * stdout and stderr sent where `stdout` and `stderr` say.
   */
  private def start(
      flags: Vector[String],
      program: String,
      stdout: ProcessBuilder.Redirect,
      stderr: ProcessBuilder.Redirect
  ): Process = {
    val entry = Files.createTempFile(dir, "main", ".rac")
    Files.writeString(entry, program)
    val java = Paths.get(System.getProperty("java.home"), "bin", "java").toString
    val command =
      Vector(java, "-cp", System.getProperty("java.class.path"), "com.raccoonlang.Main", "--prelude") ++
        Vector(stringPrelude.toString) ++ flags :+ entry.toString
    val builder = new ProcessBuilder(command: _*).redirectOutput(stdout).redirectError(stderr)
    builder.environment().put("LANG", "C")
    builder.environment().put("LC_ALL", "C")
    val process = builder.start()
    process.getOutputStream.close()
    process
  }

  /** Runs the CLI on `program` with `flags`, and reads its stdout. */
  private def run(flags: Vector[String], program: String): Run = {
    val process = start(flags, program, ProcessBuilder.Redirect.PIPE, ProcessBuilder.Redirect.DISCARD)
    val stdout = new String(process.getInputStream.readAllBytes(), StandardCharsets.UTF_8)
    Run(process.waitFor(), stdout)
  }

  /** Runs the CLI on `program`, which it rejects, and reads its text report from stderr. */
  private def textReport(program: String): String = {
    val process = start(Vector.empty, program, ProcessBuilder.Redirect.DISCARD, ProcessBuilder.Redirect.PIPE)
    val stderr = new String(process.getErrorStream.readAllBytes(), StandardCharsets.UTF_8)
    assertEquals(process.waitFor(), 1)
    stderr
  }

  /** stdout without the progress log's timestamped lines. */
  private def withoutLog(stdout: String): String =
    stdout.linesWithSeparators.filterNot(_.matches("""(?s)\d\d:\d\d:\d\d\.\d{3}: .*""")).mkString

  test("--raw prints a String result as its characters in UTF-8, and nothing else") {
    // A written part and a computed part, with characters a literal escapes and characters ASCII lacks.
    def program(computed: String): String = {
      val chars =
        computed
          .codePoints()
          .toArray
          .foldRight("List.nil(Char)")((scalar, rest) => s"List.cons(Char.ofNat($scalar), $rest)")
      "{ String.append(\"q\\\"b\\\\\\n\\t\", String.mk(" + chars + ")) }\n"
    }
    assertEquals(run(Vector("--raw"), program("λ😀")), Run(0, "q\"b\\\n\tλ😀"))
    // Without it, the String prints as a literal, after the progress log.
    val plain = run(Vector.empty, program("ok"))
    assertEquals(plain.exitCode, 0)
    assertNotEquals(withoutLog(plain.stdout), plain.stdout)
    assertEquals(withoutLog(plain.stdout), "\"q\\\"b\\\\\\n\\tok\"\n")
  }

  test("--raw prints a result that is not a String as usual, and nothing else") {
    assertEquals(run(Vector("--raw"), "{ Nat.add(2, 3) }\n"), Run(0, "5\n"))
    assertEquals(
      run(Vector("--raw"), "{ List.cons(\"a\", List.nil(String)) }\n"),
      Run(0, "List.cons(\"a\", List.nil)\n")
    )
  }

  test("--raw prints a String with a character it does not know as usual") {
    assertEquals(
      run(Vector("--raw"), "{ String.mk(List.cons(Char.ofNat(97), List.cons(someChar, List.nil(Char)))) }\n"),
      Run(0, "String.mk(List.cons(Char.mk(97), List.cons(someChar, List.nil)))\n")
    )
  }

  test("a diagnostic prints a computed String as a literal, in the text report and under --json") {
    val program =
      "def needs (s: String)[ok: Eq(String, s, \"ok\")]: Nat := 0\n" +
        "{ needs(String.mk(List.cons(Char.ofNat(110), List.cons(Char.ofNat(111), List.nil(Char))))) }\n"
    val json = run(Vector("--json"), program)
    assertEquals(json.exitCode, 1)
    assert(json.stdout.contains("its proposition is Eq(String, \\\"no\\\", \\\"ok\\\"), "), json.stdout)
    val text = textReport(program)
    assert(text.contains("its proposition is Eq(String, \"no\", \"ok\"), "), text)
  }

  test("--stack bounds host-recursive checking while explicit Core frames run deeply") {
    val shallow = run(Vector("--json", "--stack", "1m"), CliTests.hostDeepProgram)
    assertEquals(shallow.exitCode, 1)
    assert(shallow.stdout.startsWith("[\n  {"), shallow.stdout)
    // At the declaration, on line 7.
    assert(shallow.stdout.contains("\"startLine\": 7, \"startColumn\": 1,"), shallow.stdout)
    assert(shallow.stdout.contains("\"kind\": \"EvaluationTooDeep\""), shallow.stdout)
    assertEquals(run(Vector("--raw", "--stack", "1m"), CliTests.deepProgram), Run(0, "20000\n"))
    assertEquals(run(Vector("--raw", "--stack", "256m"), CliTests.deepProgram), Run(0, "20000\n"))
    // 256MB is the default.
    assertEquals(run(Vector("--raw"), CliTests.deepProgram), Run(0, "20000\n"))
  }

  test("--stack takes a number of bytes, or of KiB, MiB or GiB by its suffix") {
    Vector("268435456", "262144K", "1g").foreach { size =>
      assertEquals(run(Vector("--raw", "--stack", size), "{ Nat.add(2, 3) }\n"), Run(0, "5\n"), size)
    }
  }

  test("a --stack that is not a positive size is a usage error") {
    val sizes = Vector("0", "-1m", "1.5m", "1mb", "m", "", "99999999999999999999", "8589934592g")
    sizes.foreach(size => assertEquals(run(Vector("--stack", size), "{ 0 }\n"), Run(2, ""), size))
  }

  test("--wait-for-enter waits before the pipeline starts, which then runs as usual") {
    assertEquals(run(Vector("--raw", "--wait-for-enter"), "{ Nat.add(2, 3) }\n"), Run(0, "5\n"))
  }
}

object CliTests {

  /** A program whose Core non-tail calls now run in explicit frames. */
  private val deepProgram =
    """def count (n: Nat): Nat decreases structural(n) := {
      |  match n returning Nat with
      |  | Nat.zero => Nat.zero
      |  | Nat.succ k => Nat.succ(count(k))
      |}
      |
      |{ count(20000) }
      |""".stripMargin

  /** A declaration whose Pi classification still recurses through the checker and semantic helpers. */
  private val hostDeepProgram =
    """def nest (n: Nat): Type decreases structural(n) := {
      |  match n returning Type with
      |  | Nat.zero => Nat
      |  | Nat.succ k => (x: Nat) -> nest(k)
      |}
      |
      |def deep : Type := nest(100000)
      |{ 0 }
      |""".stripMargin

  private final case class Run(exitCode: Int, stdout: String)
}
