package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

/** The command line runs in its own process because it owns stdout, stderr, and the exit code. */
class CliTests extends munit.FunSuite {
  private type Run = (Int, String, String)

  private lazy val dir: Path = Files.createTempDirectory("raccoon-cli")

  private def run(flags: Vector[String], program: String): Run = {
    val entry = Files.createTempFile(dir, "main", ".rac")
    Files.writeString(entry, program)
    val java = Paths.get(System.getProperty("java.home"), "bin", "java").toString
    val command =
      Vector(java, "-cp", System.getProperty("java.class.path"), "com.raccoonlang.Main") ++ flags :+ entry.toString
    val process = new ProcessBuilder(command: _*).start()
    process.getOutputStream.close()
    val stdout = new String(process.getInputStream.readAllBytes(), StandardCharsets.UTF_8)
    val stderr = new String(process.getErrorStream.readAllBytes(), StandardCharsets.UTF_8)
    (process.waitFor(), stdout, stderr)
  }

  test("--stack runs the pipeline on an explicit stack and JSON output is only a diagnostics array") {
    assertEquals(run(Vector("--json", "--stack", "4m"), "{ Nat.add(2, 3) }\n"), (0, "[]\n", ""))
  }

  test("--json reports a failed check as a diagnostics array with no progress log") {
    val result = run(Vector("--json", "--stack", "4m"), "{ Nat.add(Bool.true, 2) }\n")
    assertEquals(result._1, 1)
    assert(result._2.startsWith("[\n  {"), result._2)
    assert(result._2.trim.endsWith("]"), result._2)
    assert(result._2.contains("\"kind\": \"TypeMismatch\""), result._2)
    assertEquals(result._3, "")
  }

  test("--stack rejects non-positive, malformed, and overflowing sizes as usage errors") {
    val invalid = Vector("0", "-1m", "1.5m", "1mb", "m", "999999999999999999999999999")
    invalid.foreach { size =>
      val result = run(Vector("--stack", size), "{ Nat.zero }\n")
      assertEquals(result._1, 2, size)
      assert(result._3.startsWith("Usage: raccoon-lang"), result._3)
      assertEquals(result._2, "")
    }
  }
}
