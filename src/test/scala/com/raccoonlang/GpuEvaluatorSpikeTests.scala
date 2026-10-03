package com.raccoonlang

import java.nio.file.{Files, Paths}
import java.nio.charset.StandardCharsets
import java.security.MessageDigest
import scala.concurrent.duration.Duration

class GpuEvaluatorSpikeTests extends munit.FunSuite {
  override val munitTimeout = Duration(5, "minutes")

  private val TinyCudaSha256 = "7dc6a52123c1a5b8bc1145fcc7083c61a792a3a13b1a2e441d28a31e2bccefa0"
  private val root = Paths.get("").toAbsolutePath.normalize
  private val gpuRoot = root.resolve("gpu")
  private lazy val prelude = Prelude.fromPath(gpuRoot.resolve("Prelude.rac"))

  private val nativeMaps = (
    NativeGpuAst.MapEncoding(
      "A_map",
      NativeGpuAst.MapUse.Load,
      NativeGpuAst.Param.Input(NativeGpuAst.DType.BF16, "A"),
      "M",
      "K",
      64,
      128
    ),
    NativeGpuAst.MapEncoding(
      "B_map",
      NativeGpuAst.MapUse.Load,
      NativeGpuAst.Param.Input(NativeGpuAst.DType.BF16, "B"),
      "N",
      "K",
      64,
      128
    ),
    NativeGpuAst.MapEncoding(
      "C_map",
      NativeGpuAst.MapUse.Store,
      NativeGpuAst.Param.Output(NativeGpuAst.DType.F32, "C"),
      "M",
      "N",
      32,
      32
    )
  )

  private def nativePlan(body: NativeGpuAst.Block): NativeGpuBackend.Plan = {
    val (aMap, bMap, cMap) = nativeMaps
    val metadata = NativeGpuAst.InputMetadata(128, 128, 64, 8, aMap, bMap, cMap)
    val kernel = NativeGpuAst.Kernel("control-test", Vector.empty, 8, body, None)
    new NativeGpuBackend.Plan(kernel, metadata)
  }

  private def nativeInput: NativeGpuBackend.Inputs = NativeGpuBackend.Inputs(Vector.fill(8192)(0), Vector.fill(8192)(0))

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

  test("TinyGEMM source and native evaluation match every Z/257 output for two asymmetric seeds") {
    val stats = TinyGemmSpikeBenchmark.verifySeeds(gpuRoot, prelude, Vector(17, 83))
    assertEquals(stats.length, 2)
    stats.foreach { sample =>
      assertEquals(sample.scalarMuls, 1048576L)
      assertEquals(sample.scalarAdds, 1048576L)
      assertEquals(sample.mmaInstructions, 4L)
      assertEquals(sample.asyncCompletions, 88L)
      assertEquals(sample.tmaBytes, 98304L)
      assertEquals(sample.tmemLoads, 64L)
      assertEquals(sample.tmaStores, 16L)
      assertEquals(sample.warpSteps, 1251L)
    }
  }

  test("native plans validate their launch subset and isolate repeated, changed, and concurrent inputs") {
    TinyGemmSpikeBenchmark.verifyNativeBoundaryAndOwnership(gpuRoot, prelude)
  }

  test("native warp control preserves divergent lanes, exclusive bounds, strides, and unreachable AST nodes") {
    import NativeGpuAst._
    import NativeGpuAst.BinOp._
    import NativeGpuAst.Expr._
    import NativeGpuAst.Stmt._

    val body = Block(
      Vector(
        DeclOut(DType.U32, 1),
        IfElse(
          Bin(Eq, Special(Builtin.Lane), Lit(0)),
          Block(Vector(Assign(1, Lit(1)))),
          Block(Vector(Assign(1, Lit(0))))
        ),
        IfElse(
          Bin(Eq, Var(1), Bin(Eq, Special(Builtin.Lane), Lit(0))),
          Block(Vector.empty),
          Block(Vector(Error("branch merge failed")))
        ),
        IfElse(Bin(Eq, Lit(0), Lit(1)), Block(Vector(Error("unreachable unsupported node ran"))), Block(Vector.empty)),
        ForLoop(2, Lit(1), Lit(1), Block(Vector(Error("exclusive stop was ignored")))),
        Decl(DType.U32, 3, Lit(0), mutable = true),
        ForStride(4, Lit(0), Lit(5), Lit(2), Block(Vector(Assign(3, Bin(Add, Var(3), Lit(1)))))),
        IfElse(
          Bin(Eq, Var(3), Lit(3)),
          Block(Vector.empty),
          Block(Vector(Error("stride loop had wrong iteration count")))
        )
      )
    )
    val result = NativeGpuBackend.run(nativePlan(body), nativeInput)
    assertEquals(result.failure, Some(NativeGpuBackend.IncompleteOutput))
    assertEquals(result.stats.warpSteps, BigInt(104))
    assertEquals(result.outputs, Vector.empty)
  }

  test("native repeated loop declarations reset lane initialization and negative fuel is rejected") {
    import NativeGpuAst._
    import NativeGpuAst.Expr._
    import NativeGpuAst.Stmt._

    val loop = Block(
      Vector(
        IfElse(
          Bin(BinOp.Lt, Special(Builtin.Lane), Lit(3)),
          Block(
            Vector(
              DeclOut(DType.U32, 3),
              ForStride(
                1,
                Special(Builtin.Lane),
                Lit(3),
                Lit(1),
                Block(Vector(Decl(DType.U32, 2, Lit(1), mutable = false)))
              ),
              Assign(3, Var(2))
            )
          ),
          Block(Vector.empty)
        )
      )
    )
    val loopResult = NativeGpuBackend.run(nativePlan(loop), nativeInput)
    assertEquals(loopResult.failure.map(_.category), Some("invalid-state"))
    assert(loopResult.errors.contains("uninitialized active lane"), loopResult.errors)
    val noOpPlan = nativePlan(Block(Vector.empty))
    assertEquals(NativeGpuBackend.run(noOpPlan, nativeInput, BigInt(-1)).failure.map(_.category), Some("invalid-state"))
  }

  test("native shared stores evaluate later words through earlier writes and preserve bf16/u32 aliasing") {
    import NativeGpuAst._
    import NativeGpuAst.BinOp._
    import NativeGpuAst.Expr._
    import NativeGpuAst.Instr._
    import NativeGpuAst.Scope._
    import NativeGpuAst.Stmt._

    val aliasBody = Block(
      Vector(
        Instruction(StShared(SharedAddr(0), Vector(Lit(7), Index(SharedPtr(DType.F32, 0), Lit(0))))),
        Instruction(LdRelaxed(Cta, 1, SharedAddr(4))),
        IfElse(Bin(Eq, Var(1), Lit(7)), Block(Vector.empty), Block(Vector(Error("shared alias read failed"))))
      )
    )
    val aliasResult = NativeGpuBackend.run(nativePlan(aliasBody), nativeInput)
    assertEquals(aliasResult.failure, Some(NativeGpuBackend.IncompleteOutput))

    val malformedValue = Block(Vector(Instruction(StShared(SharedAddr(0), Vector(Lit(7), Var(999))))))
    val failedStore = NativeGpuBackend.run(nativePlan(malformedValue), nativeInput)
    assertEquals(failedStore.failure.map(_.category), Some("device-fault"))
    assert(failedStore.errors.contains("st.shared vector access is outside dynamic shared memory"), failedStore.errors)

    val device = new NativeGpuDevice(nativePlan(Block(Vector.empty)), nativeInput)
    val fullMask = (BigInt(1) << 32) - 1
    assert(device.writeSharedLanes(Vector.fill(32)(BigInt(0)), Vector.fill(32)(BigInt(0x1234)), fullMask, DType.BF16))
    assert(device.writeSharedLanes(Vector.fill(32)(BigInt(2)), Vector.fill(32)(BigInt(0xabcd)), fullMask, DType.BF16))
    val originalWord = BigInt(0xabcd1234L)
    assertEquals(device.readShared(BigInt(0), DType.U32), Some(originalWord))
    val bf16Rollback = device.beginSharedTransaction(1)
    assert(
      device.writeSharedLanes(
        Vector.fill(32)(BigInt(2)),
        Vector.fill(32)(BigInt(0x5678)),
        BigInt(1),
        DType.BF16,
        bf16Rollback
      )
    )
    assertEquals(device.readShared(BigInt(0), DType.U32), Some(BigInt(0x56781234L)))
    device.rollbackSharedTransaction(bf16Rollback)
    assertEquals(device.readShared(BigInt(0), DType.U32), Some(originalWord))

    val rollback = device.beginSharedTransaction(1)
    assert(
      device.writeSharedLanes(
        Vector.fill(32)(BigInt(0)),
        Vector.tabulate(32)(lane => BigInt(lane + 1)),
        fullMask,
        DType.U32,
        rollback
      )
    )
    assertEquals(device.readShared(BigInt(0), DType.U32), Some(BigInt(32)))
    assert(
      device.writeSharedLanes(
        Vector.fill(32)(BigInt(0)),
        Vector.tabulate(32)(lane => BigInt(lane + 100)),
        fullMask,
        DType.U32,
        rollback
      )
    )
    assertEquals(device.readShared(BigInt(0), DType.U32), Some(BigInt(131)))
    device.rollbackSharedTransaction(rollback)
    assertEquals(device.readShared(BigInt(0), DType.U32), Some(originalWord))

    val commit = device.beginSharedTransaction(1)
    assert(
      device.writeSharedLanes(
        Vector.fill(32)(BigInt(0)),
        Vector.fill(32)(BigInt(55)),
        BigInt(1),
        DType.U32,
        commit
      )
    )
    device.commitSharedTransaction(commit)
    assertEquals(device.readShared(BigInt(0), DType.U32), Some(BigInt(55)))
  }

  test("TinyGEMM source AST mutations expose matching native K-slice and failure-category behavior") {
    val cases = TinyGemmSpikeBenchmark.verifyMutants(gpuRoot, prelude)
    assertEquals(
      cases.map(result => result.name -> result.category).toMap,
      Map(
        "wrong-k-slice" -> "complete-mismatch",
        "descriptor" -> "device-fault",
        "output-offset" -> "device-fault",
        "out-of-bounds" -> "device-fault",
        "partial-aligned" -> "invalid-state",
        "partial-wait" -> "invalid-state",
        "unsupported" -> "unsupported",
        "unsupported-regpool" -> "unsupported",
        "missing-commit" -> "deadlocked",
        "missing-tma-completion" -> "deadlocked",
        "fuel" -> "fuel-exhausted",
        "not-quiescent" -> "not-quiescent",
        "overlapping-tmem-load" -> "complete-match"
      )
    )
    val byName = cases.map(result => result.name -> result).toMap
    assertEquals(byName("wrong-k-slice").stats.warpSteps, 1251L)
    assert(byName("fuel").stats.warpSteps <= 1L)
    assert(byName("missing-commit").stats.warpSteps > 0L)
    assert(byName("missing-commit").stats.asyncCompletions < 88L)
    assert(byName("missing-tma-completion").stats.asyncCompletions < 88L)
    assert(byName("missing-tma-completion").stats.tmaBytes < 98304L)
    assertEquals(byName("missing-tma-completion").stats.mmaInstructions, 0L)
    assertEquals(byName("overlapping-tmem-load").stats.warpSteps, 1267L)
    assertEquals(byName("overlapping-tmem-load").stats.asyncCompletions, 104L)
    assertEquals(byName("overlapping-tmem-load").stats.tmemLoads, 80L)
  }

  private def sha256(text: String): String =
    MessageDigest
      .getInstance("SHA-256")
      .digest(text.getBytes(StandardCharsets.UTF_8))
      .map(byte => f"${byte & 0xff}%02x")
      .mkString
}
