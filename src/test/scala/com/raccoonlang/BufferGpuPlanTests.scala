package com.raccoonlang

import java.nio.file.Paths

class BufferGpuPlanTests extends munit.FunSuite {
  private val root = Paths.get("").toAbsolutePath.normalize
  private val gpuRoot = root.resolve("gpu")
  private lazy val prelude = Prelude.fromPath(gpuRoot.resolve("Prelude.rac"))

  test("the checked TinyGemm AST expands across all eight finite warp lists") {
    val prepared = Execution.onStack(256L << 20) {
      EvaluatorSpikeBenchmark.checkedEntry(
        gpuRoot.resolve("evaluator/checks/BufferGpuPlanProbe.rac"),
        gpuRoot,
        prelude
      )
    }
    val encoded = EvaluatorSpikeBenchmark.natOf(prepared.value)
    assert(encoded >= BigInt(1000000000000L) && encoded < BigInt(2000000000000L),
      s"checked AST expansion rejected with diagnostic code $encoded")
    val snapshots = (encoded - BigInt(1000000000000L)) / BigInt(1000000000L)
    assertEquals(snapshots, BigInt(64), s"encoded expansion summary $encoded")
  }
}
