package com.raccoonlang

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets
import java.security.MessageDigest

class GpuEvaluatorSpikeTests extends munit.FunSuite {
  private val TinyCudaSha256 = "7dc6a52123c1a5b8bc1145fcc7083c61a792a3a13b1a2e441d28a31e2bccefa0"
  private val root = Paths.get("").toAbsolutePath.normalize
  private val gpuRoot = root.resolve("gpu")
  private lazy val prelude = Prelude.fromPath(gpuRoot.resolve("Prelude.rac"))

  private def checked(relative: String): EvaluatorSpikeBenchmark.Prepared =
    Execution.onStack(256L << 20) {
      EvaluatorSpikeBenchmark.checkedEntry(gpuRoot.resolve(relative), gpuRoot, prelude)
    }

  test("the source-level memory and ring foundation fixture is checked by normal Scala validation") {
    assert(Files.isRegularFile(gpuRoot.resolve("evaluator/checks/foundation.rac")))
    val result = checked("evaluator/checks/FoundationEntry.rac").value
    assert(Sorts.isProposition(result.tpe))
  }

  test("TinyGEMM exports a checked immutable kernel AST and the original render wrapper") {
    val kernel = checked("evaluator/TinyKernel.rac").value
    EvaluatorSpikeBenchmark.requireTinyKernel(kernel)

    val rendered = checked("encoding/examples/tinygemm.rac")
    val text = PrettyPrinter
      .rawString(rendered.value, rendered.strings)
      .getOrElse(fail("TinyGEMM render result is not a String"))
    assertEquals(sha256(text), TinyCudaSha256)
  }

  test("the Raccoon buffer workload matches an independent bounded reference and allocates fresh state per call") {
    val prepared = checked("evaluator/BenchmarkEntry.rac")
    val natType = prelude.checkedEnv("Nat")
    val function = prepared.value

    Vector(0, 1, 2, 17, 64).foreach { iterations =>
      val argument = Value.VPacked.nat(BigInt(iterations), natType)
      val first = EvaluatorSpikeBenchmark.invoke(function, argument)._2
      val actual = EvaluatorSpikeBenchmark.natOf(first)
      assertEquals(actual, EvaluatorSpikeBenchmark.expectedResult(iterations))
    }

    val two = Value.VPacked.nat(BigInt(2), natType)
    val afterOtherInvocation = EvaluatorSpikeBenchmark.natOf(EvaluatorSpikeBenchmark.invoke(function, two)._2)
    assertEquals(afterOtherInvocation, EvaluatorSpikeBenchmark.expectedResult(2))
  }

  private def sha256(text: String): String =
    MessageDigest
      .getInstance("SHA-256")
      .digest(text.getBytes(StandardCharsets.UTF_8))
      .map(byte => f"${byte & 0xff}%02x")
      .mkString
}
