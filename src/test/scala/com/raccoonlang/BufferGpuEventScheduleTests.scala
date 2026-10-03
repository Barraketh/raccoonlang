package com.raccoonlang

import java.nio.file.{Files, Paths}
import scala.concurrent.duration.Duration

class BufferGpuEventScheduleTests extends munit.FunSuite {
  override val munitTimeout: Duration = Duration(2, "minutes")

  private val root = Paths.get("").toAbsolutePath.normalize
  private val gpuRoot = root.resolve("gpu")
  private lazy val prelude = Prelude.fromPath(gpuRoot.resolve("Prelude.rac"))

  private def runProbe(): Value = {
    val probePath = gpuRoot.resolve("evaluator/checks/BufferGpuEventScheduleProbe.rac")
    val probeSource = Files.readString(probePath)
    LanguageParser.parseProgram(probeSource) match {
      case Success(_, _, _) => ()
      case Failure(_, at, message) =>
        fail(s"BufferGpuEventScheduleProbe did not parse at $at: $message near ${probeSource.substring(at)}")
    }
    Execution.onStack(512L << 20) {
      val loaded = ModuleLoader.load(probePath, ModuleLoader.LoadConfig(Vector(gpuRoot, root), prelude))
      val checked =
        try Execution.check(Execution.elaborate(loaded.program, prelude))
        catch { case failure: Execution.CheckFailure => fail(failure.getMessage) }
      Interpreter.run(checked).getOrElse(fail("BufferGpuEventScheduleProbe has no result"))
    }
  }

  private def bool(value: Value, label: String): Boolean = value match {
    case Value.VCtor(head, Vector(), _) if head.name == "Bool.true"  => true
    case Value.VCtor(head, Vector(), _) if head.name == "Bool.false" => false
    case other                                                       => fail(s"Expected Bool for $label, got $other")
  }

  test("empty-tail gate cursor and TMEM event-completion initialization invariants") {
    runProbe() match {
      case Value.VCtor(head, Vector(gate, tmem), _) if head.name == "Pair.mk" =>
        assert(bool(gate, "empty-tail gate/cursor"))
        assert(bool(tmem, "TMEM completion initialization"))
      case other => fail(s"Expected event scheduler probe pair, got $other")
    }
  }
}
