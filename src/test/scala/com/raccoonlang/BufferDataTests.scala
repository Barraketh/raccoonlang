package com.raccoonlang

import java.nio.file.{Files, Paths}

class BufferDataTests extends munit.FunSuite {
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

  test("finite data actions lower through Buffer.Program with typed loop slots and all six roles") {
    val probePath = gpuRoot.resolve("evaluator/checks/BufferDataProbe.rac")
    val probeSource = Files.readString(probePath)
    LanguageParser.parseProgram(probeSource) match {
      case Success(_, _, _) => ()
      case Failure(_, at, message) =>
        fail(s"BufferDataProbe did not parse at $at: $message near ${probeSource.substring(at)}")
    }
    val moduleSource = Files.readString(gpuRoot.resolve("evaluator/BufferData.rac"))
    LanguageParser.parseProgram(moduleSource) match {
      case Success(_, _, _) => ()
      case Failure(_, at, message) =>
        fail(s"BufferData.rac did not parse at $at: $message near ${moduleSource.substring(at)}")
    }
    val value = Execution.onStack(256L << 20) {
      val loaded = ModuleLoader.load(probePath, ModuleLoader.LoadConfig(Vector(gpuRoot, root), prelude))
      val checked = Execution.check(Execution.elaborate(loaded.program, prelude))
      Interpreter.run(checked).getOrElse(fail("BufferDataProbe has no result"))
    }

    value match {
      case Value.VCtor(pair, Vector(result, rejection), _) if pair.name == "Pair.mk" =>
        result match {
          case Value.VCtor(success, Vector(outputs), _) if success.name == "Buffer.Result.success" =>
            val rows = list(outputs).map(row => list(row).map(nat))
            assertEquals(
              rows,
              Vector(
                Vector(
                  BigInt(7),
                  BigInt(0),
                  BigInt(0),
                  BigInt(0),
                  BigInt(13),
                  BigInt(0),
                  BigInt(0),
                  BigInt(0),
                  BigInt(17),
                  BigInt(0),
                  BigInt(0),
                  BigInt(0)
                )
              )
            )
          case other => fail(s"Expected Buffer.Result.success, got $other")
        }
        rejection match {
          case Value.VCtor(rejected, Vector(error), _) if rejected.name == "BufferData.LowerResult.rejected" =>
            error match {
              case Value.VCtor(inputWrite, _, _) => assertEquals(inputWrite.name, "BufferData.LowerError.inputWrite")
              case other                         => fail(s"Expected immutable-input store rejection, got $other")
            }
          case other => fail(s"Expected LowerResult.rejected, got $other")
        }
      case other => fail(s"Expected BufferDataProbe's result pair, got $other")
    }
  }
}
