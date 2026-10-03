package com.raccoonlang

import java.nio.file.{Files, Paths}

class BufferIOTests extends munit.FunSuite {
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

  private def optionList(value: Value): Option[Vector[BigInt]] = value match {
    case Value.VCtor(head, Vector(items), _) if head.name == "Option.some" => Some(list(items).map(nat))
    case Value.VCtor(head, Vector(), _) if head.name == "Option.none"      => None
    case other => fail(s"Expected an Option(List(Nat)), got $other")
  }

  test("Z/257 byte codecs enforce exact lengths and field bounds") {
    val probePath = gpuRoot.resolve("evaluator/checks/BufferIOProbe.rac")
    val probeSource = Files.readString(probePath)
    LanguageParser.parseProgram(probeSource) match {
      case Success(_, _, _) => ()
      case Failure(_, at, message) =>
        fail(s"BufferIOProbe did not parse at $at: $message near ${probeSource.substring(at)}")
    }
    val moduleSource = Files.readString(gpuRoot.resolve("evaluator/BufferIO.rac"))
    LanguageParser.parseProgram(moduleSource) match {
      case Success(_, _, _) => ()
      case Failure(_, at, message) =>
        fail(s"BufferIO.rac did not parse at $at: $message near ${moduleSource.substring(at)}")
    }
    val value = Execution.onStack(256L << 20) {
      val loaded = ModuleLoader.load(probePath, ModuleLoader.LoadConfig(Vector(gpuRoot, root), prelude))
      val checked = Execution.check(Execution.elaborate(loaded.program, prelude))
      Interpreter.run(checked).getOrElse(fail("BufferIOProbe has no result"))
    }
    val results = list(value).map(optionList)
    assertEquals(results.length, 13)
    assertEquals(
      results(0),
      Some(Vector(BigInt(0), BigInt(0), BigInt(1), BigInt(0), BigInt(255), BigInt(0), BigInt(0), BigInt(1)))
    )
    assertEquals(results(4), Some(Vector.empty))
    assertEquals(results(6), Some(Vector(BigInt(0), BigInt(1), BigInt(255), BigInt(256))))
    assertEquals(results(11), Some(Vector.empty))
    Vector(1, 2, 3, 5, 7, 8, 9, 10, 12).foreach(index => assertEquals(results(index), None))
  }
}
