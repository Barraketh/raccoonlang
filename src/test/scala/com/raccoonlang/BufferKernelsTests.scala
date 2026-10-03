package com.raccoonlang

import java.nio.file.{Files, Paths}
import scala.concurrent.duration.Duration

class BufferKernelsTests extends munit.FunSuite {
  override val munitTimeout: Duration = Duration(5, "minutes")

  private val root = Paths.get("").toAbsolutePath.normalize
  private val gpuRoot = root.resolve("gpu")
  private lazy val prelude = Prelude.fromPath(gpuRoot.resolve("Prelude.rac"))

  private def nat(value: Value): BigInt = value match {
    case packed: Value.VPacked if packed.codec eq Value.NatCodec           => packed.natValue.get
    case Value.VCtor(head, Vector(), _) if head.name == "Nat.zero"         => BigInt(0)
    case Value.VCtor(head, Vector(previous), _) if head.name == "Nat.succ" => BigInt(1) + nat(previous)
    case other                                                             => fail(s"Expected a Nat, got $other")
  }

  private def list(value: Value): Vector[Value] = {
    val result = Vector.newBuilder[Value]
    var rest = value
    var done = false
    while (!done) {
      rest match {
        case Value.VCtor(head, Vector(), _) if head.name == "List.nil" => done = true
        case Value.VCtor(head, Vector(item, tail), _) if head.name == "List.cons" =>
          result += item
          rest = tail
        case other => fail(s"Expected a List, got $other")
      }
    }
    result.result()
  }

  private def outputBytes(value: Value): Vector[BigInt] = value match {
    case Value.VCtor(head, Vector(outputs), _) if head.name == "Buffer.Result.success" =>
      val rows = list(outputs)
      assertEquals(rows.length, 1)
      list(rows.head).map(nat)
    case other => fail(s"Expected Buffer.Result.success, got $other")
  }

  private def runProbe(): Value = {
    val probePath = gpuRoot.resolve("evaluator/checks/BufferKernelsProbe.rac")
    val probeSource = Files.readString(probePath)
    LanguageParser.parseProgram(probeSource) match {
      case Success(_, _, _) => ()
      case Failure(_, at, message) =>
        fail(s"BufferKernelsProbe did not parse at $at: $message near ${probeSource.substring(at)}")
    }
    val moduleSource = Files.readString(gpuRoot.resolve("evaluator/BufferKernels.rac"))
    LanguageParser.parseProgram(moduleSource) match {
      case Success(_, _, _) => ()
      case Failure(_, at, message) =>
        fail(s"BufferKernels.rac did not parse at $at: $message near ${moduleSource.substring(at)}")
    }
    Execution.onStack(512L << 20) {
      val loaded = ModuleLoader.load(probePath, ModuleLoader.LoadConfig(Vector(gpuRoot, root), prelude))
      val checked =
        try Execution.check(Execution.elaborate(loaded.program, prelude))
        catch { case failure: Execution.CheckFailure => fail(failure.getMessage) }
      Interpreter.run(checked).getOrElse(fail("BufferKernelsProbe has no result"))
    }
  }

  private def expectedA(row: Int, k: Int): Int = (row * 3 + k * 5 + 7) % 257
  private def expectedB(row: Int, k: Int): Int = (row * 11 + k * 13 + 9) % 257

  private def dot(row: Int, col: Int, kStart: Int, kEnd: Int): BigInt =
    (kStart until kEnd).foldLeft(BigInt(0)) { (sum, k) =>
      (sum + expectedA(row, k) * expectedB(col, k)) % 257
    }

  private def cell(bytes: Vector[BigInt], row: Int, col: Int): BigInt = {
    val offset = (row * 128 + col) * 4
    bytes(offset) | (bytes(offset + 1) << 8) | (bytes(offset + 2) << 16) | (bytes(offset + 3) << 24)
  }

  test("buffer fragments execute swizzled K16 MMA, retain completion snapshots, and copy a nonzero output tile") {
    val result = runProbe() match {
      case Value.VCtor(head, Vector(bufferResult, accepted), _) if head.name == "Pair.mk" =>
        assertEquals(
          nat(accepted),
          BigInt(17),
          "all supported fragments should emit and all five invalid requests reject"
        )
        outputBytes(bufferResult)
      case other => fail(s"Expected BufferKernelsProbe's result pair, got $other")
    }

    assertEquals(result.length, 128 * 128 * 4)
    assertEquals(cell(result, 32, 64), dot(0, 0, 32, 48), "nonaccumulating descriptor step 2 snapshot")
    assertEquals(cell(result, 32, 65), dot(0, 0, 32, 64), "accumulating descriptor step 3 snapshot")
    assertEquals(cell(result, 32, 66), dot(3, 4, 32, 48), "older SoA snapshot remains durable")
    assertEquals(cell(result, 32, 67), dot(3, 4, 32, 64), "new SoA snapshot and output swizzle")
    assertEquals(cell(result, 33, 64), dot(0, 0, 32, 64), "snapshot replay uses the shared swizzle on output row 1")
    assertEquals(cell(result, 32, 63), BigInt(0), "output TMA respects its nonzero x origin")
  }
}
