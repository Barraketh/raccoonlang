package com.raccoonlang

import java.nio.file.Paths
import java.nio.file.Files

class BufferGpuDecodeTests extends munit.FunSuite {
  private val root = Paths.get("").toAbsolutePath.normalize
  private val gpuRoot = root.resolve("gpu")
  private lazy val prelude = Prelude.fromPath(gpuRoot.resolve("Prelude.rac"))

  test("decoder preserves actual launcher maps, typed event fields, and ordered shared writes") {
    val source = Files.readString(gpuRoot.resolve("evaluator/checks/BufferGpuDecodeProbe.rac"))
    LanguageParser.parseProgram(source) match {
      case Success(_, _, _)        => ()
      case Failure(_, at, message) => fail(s"decoder probe did not parse at $at: $message near ${source.substring(at)}")
    }
    val moduleSource = Files.readString(gpuRoot.resolve("evaluator/BufferGpuDecode.rac"))
    LanguageParser.parseProgram(moduleSource) match {
      case Success(_, _, _) => ()
      case Failure(_, at, message) =>
        fail(s"BufferGpuDecode.rac did not parse at $at: $message near ${moduleSource.substring(at)}")
    }
    val prepared = Execution.onStack(256L << 20) {
      val probePath = gpuRoot.resolve("evaluator/checks/BufferGpuDecodeProbe.rac")
      val loaded = ModuleLoader.load(probePath, ModuleLoader.LoadConfig(Vector(gpuRoot, root), prelude))
      val checked =
        try Execution.check(Execution.elaborate(loaded.program, prelude))
        catch {
          case error: Execution.CheckFailure =>
            fail(
              error.diagnostics
                .map { diagnostic =>
                  val location = diagnostic.span.flatMap(span =>
                    span.source.flatMap(id =>
                      loaded.sources
                        .find(_.sourceId == id)
                        .map(source => {
                          val prefix = source.source.take(span.start)
                          val line = prefix.count(_ == '\n') + 1
                          s"${source.path}:$line: ${source.source.slice(span.start, span.end)}"
                        })
                    )
                  )
                  s"${diagnostic.error} at ${diagnostic.span} $location"
                }
                .mkString("\n")
            )
        }
      Interpreter.run(checked).getOrElse(fail("BufferGpuDecodeProbe has no result"))
    }
    assertEquals(EvaluatorSpikeBenchmark.natOf(prepared), BigInt(1))
  }
}
