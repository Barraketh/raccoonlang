package com.raccoonlang

import java.nio.file.Paths

class BufferPlanTests extends munit.FunSuite {
  private val root = Paths.get("").toAbsolutePath.normalize
  private val gpuRoot = root.resolve("gpu")
  private lazy val prelude = Prelude.fromPath(gpuRoot.resolve("Prelude.rac"))

  test("the GPU planner preserves masked expressions and rejects malformed warp vectors") {
    val prepared = Execution.onStack(256L << 20) {
      EvaluatorSpikeBenchmark.checkedEntry(
        gpuRoot.resolve("evaluator/checks/BufferPlanProbe.rac"),
        gpuRoot,
        prelude
      )
    }
    assertEquals(EvaluatorSpikeBenchmark.natOf(prepared.value), BigInt(8))
  }

  test("finite control expansion accepts checked declarations, branches, and scopes") {
    val prepared = Execution.onStack(256L << 20) {
      EvaluatorSpikeBenchmark.checkedEntry(
        gpuRoot.resolve("evaluator/checks/BufferControlProbe.rac"),
        gpuRoot,
        prelude
      )
    }
    assertEquals(EvaluatorSpikeBenchmark.natOf(prepared.value), BigInt(1))
  }

  test("shared allocator-slot zero reads reject overlapping shared writes") {
    val prepared = Execution.onStack(256L << 20) {
      EvaluatorSpikeBenchmark.checkedEntry(
        gpuRoot.resolve("evaluator/checks/BufferSlotZeroProbe.rac"),
        gpuRoot,
        prelude
      )
    }
    assertEquals(EvaluatorSpikeBenchmark.natOf(prepared.value), BigInt(2000000000040L))
  }
}
