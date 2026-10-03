package com.raccoonlang

class NativeBufferProgramTests extends munit.FunSuite {
  import NativeBufferProgram._

  private def encoded(
      u32: Int,
      u64: Int,
      inputs: Vector[Int],
      scratch: Vector[Int],
      outputs: Vector[Int],
      instructions: Vector[BigInt]
  ): Vector[BigInt] = encodedSpecs(
    u32,
    u64,
    inputs.map(BufferRole.Input -> _) ++ scratch.map(BufferRole.Scratch -> _) ++ outputs.map(BufferRole.Output -> _),
    instructions
  )

  private def encodedSpecs(
      u32: Int,
      u64: Int,
      buffers: Vector[(Int, Int)],
      instructions: Vector[BigInt]
  ): Vector[BigInt] =
    Vector[BigInt](
      Magic,
      Version,
      BigInt(u32),
      BigInt(u64),
      BigInt(buffers.length),
      BigInt(instructionCount(instructions))
    ) ++ buffers.flatMap { case (role, size) => Vector(BigInt(role), BigInt(size)) } ++ instructions

  private def instructionCount(words: Vector[BigInt]): Int = {
    var pc = 0
    var count = 0
    while (pc < words.length) {
      val opcode = words(pc).toInt
      pc += 1
      pc += (opcode match {
        case Op.Halt | Op.Else | Op.EndIf | Op.EndRepeat                       => 0
        case Op.If32                                                           => 1
        case Op.Repeat32 | Op.Repeat64                                         => 2
        case Op.Const32 | Op.Const64 | Op.Move32 | Op.Move64 | Op.Extend32To64 => 2
        case Op.Alu32 | Op.Alu64 | Op.Compare32 | Op.Compare64                 => 4
        case Op.Load8 | Op.Load16 | Op.Load32 | Op.Load64                      => 3
        case Op.Store8 | Op.Store16 | Op.Store32 | Op.Store64                  => 3
        case other => fail("Unknown instruction opcode in test fixture: " + other)
      })
      count += 1
    }
    count
  }

  private def prepared(words: Vector[BigInt]): Prepared =
    prepare(words).fold(error => fail("Program rejected: " + error.description), identity)

  private def resultBytes(result: RunResult): Vector[Vector[Int]] =
    result.outputs.map(_.map(_ & 0xff))

  test("generic bytecode performs checked little-endian copies into private output buffers") {
    val program = encoded(
      u32 = 1,
      u64 = 2,
      inputs = Vector(4),
      scratch = Vector(4),
      outputs = Vector(4),
      instructions = Vector(
        Op.Const64,
        0,
        0,
        Op.Load32,
        0,
        0,
        0,
        Op.Store32,
        2,
        0,
        0,
        Op.Halt
      ).map(BigInt(_))
    )
    val input = Vector(0x78.toByte, 0x56.toByte, 0x34.toByte, 0x12.toByte)
    val result = prepared(program).run(Vector(input))
    assertEquals(result.error, None)
    assertEquals(resultBytes(result), Vector(Vector(0x78, 0x56, 0x34, 0x12)))
    assertEquals(input.map(_ & 0xff), Vector(0x78, 0x56, 0x34, 0x12))
  }

  test("buffer IDs follow nested allocation order rather than role partitions") {
    val program = encodedSpecs(
      u32 = 1,
      u64 = 1,
      buffers = Vector(BufferRole.Output -> 1, BufferRole.Scratch -> 1, BufferRole.Input -> 1),
      instructions = Vector(
        Op.Const32,
        0,
        0x5a,
        Op.Const64,
        0,
        0,
        Op.Store8,
        0,
        0,
        0,
        Op.Halt
      ).map(BigInt(_))
    )
    val result = prepared(program).run(Vector(Vector(0x11.toByte)))
    assertEquals(result.error, None)
    assertEquals(resultBytes(result), Vector(Vector(0x5a)))
  }

  test("U32 and U64 arithmetic wraps at word width and uses unsigned division and shifts") {
    val maxU64 = (BigInt(1) << 64) - 1
    val program = encoded(
      u32 = 3,
      u64 = 6,
      inputs = Vector.empty,
      scratch = Vector.empty,
      outputs = Vector(28),
      instructions = Vector(
        Op.Const32,
        0,
        0xffff_ffffL,
        Op.Const32,
        1,
        1,
        Op.Alu32,
        2,
        0,
        1,
        Alu.Add,
        Op.Const64,
        0,
        maxU64,
        Op.Const64,
        1,
        1,
        Op.Alu64,
        2,
        0,
        1,
        Alu.Add,
        Op.Const64,
        3,
        BigInt(1) << 63,
        Op.Const64,
        4,
        2,
        Op.Alu64,
        3,
        3,
        4,
        Alu.UDiv,
        Op.Const64,
        4,
        8,
        Op.Alu64,
        4,
        3,
        4,
        Alu.LShr,
        Op.Const64,
        5,
        0,
        Op.Store32,
        0,
        5,
        2,
        Op.Const64,
        5,
        4,
        Op.Store64,
        0,
        5,
        2,
        Op.Const64,
        5,
        12,
        Op.Store64,
        0,
        5,
        3,
        Op.Const64,
        5,
        20,
        Op.Store64,
        0,
        5,
        4,
        Op.Halt
      ).map {
        case b: BigInt => b
        case n: Int    => BigInt(n)
        case n: Long   => BigInt(n)
      }
    )
    val result = prepared(program).run(Vector.empty)
    assertEquals(result.error, None)
    assertEquals(
      resultBytes(result),
      Vector(
        Vector(0, 0, 0, 0) ++ Vector.fill(8)(0) ++
          Vector(0, 0, 0, 0, 0, 0, 0, 0x40) ++ Vector(0, 0, 0, 0, 0, 0, 0x40, 0)
      )
    )
  }

  test("structured if selects one arm and permits a missing else") {
    val withElse = encoded(
      2,
      1,
      Vector.empty,
      Vector.empty,
      Vector(4),
      Vector(
        Op.Const32,
        0,
        1,
        Op.Const32,
        1,
        7,
        Op.If32,
        0,
        Op.Const32,
        1,
        9,
        Op.Else,
        Op.Const32,
        1,
        11,
        Op.EndIf,
        Op.Const64,
        0,
        0,
        Op.Store32,
        0,
        0,
        1,
        Op.Halt
      ).map(BigInt(_))
    )
    val noElse = encoded(
      1,
      0,
      Vector.empty,
      Vector.empty,
      Vector.empty,
      Vector(
        Op.Const32,
        0,
        0,
        Op.If32,
        0,
        Op.EndIf,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(resultBytes(prepared(withElse).run(Vector.empty)), Vector(Vector(9, 0, 0, 0)))
    assertEquals(prepared(noElse).run(Vector.empty).error, None)
  }

  test("zero, one, nested, and count-mutating repeats terminate with entry-snapshotted counts") {
    def incrementProgram(count: Int): Vector[BigInt] = encoded(
      4,
      1,
      Vector.empty,
      Vector.empty,
      Vector(4),
      Vector(
        Op.Const32,
        0,
        count,
        Op.Const32,
        1,
        1,
        Op.Const32,
        2,
        0,
        Op.Const64,
        0,
        0,
        Op.Repeat32,
        0,
        3,
        Op.Alu32,
        2,
        2,
        1,
        Alu.Add,
        Op.EndRepeat,
        Op.Store32,
        0,
        0,
        2,
        Op.Halt
      ).map(BigInt(_))
    )

    def outputCount(count: Int): Int = {
      val bytes = resultBytes(prepared(incrementProgram(count)).run(Vector.empty)).head
      bytes(0)
    }
    assertEquals(outputCount(0), 0)
    assertEquals(outputCount(1), 1)

    val nested = encoded(
      6,
      1,
      Vector.empty,
      Vector.empty,
      Vector(4),
      Vector(
        Op.Const32,
        0,
        2,
        Op.Const32,
        1,
        3,
        Op.Const32,
        2,
        1,
        Op.Const32,
        3,
        0,
        Op.Const64,
        0,
        0,
        Op.Repeat32,
        0,
        5,
        Op.Repeat32,
        1,
        4,
        Op.Alu32,
        3,
        3,
        2,
        Alu.Add,
        Op.EndRepeat,
        Op.EndRepeat,
        Op.Store32,
        0,
        0,
        3,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(resultBytes(prepared(nested).run(Vector.empty)), Vector(Vector(6, 0, 0, 0)))

    val countChangedByBody = encoded(
      4,
      1,
      Vector.empty,
      Vector.empty,
      Vector(4),
      Vector(
        Op.Const32,
        0,
        3,
        Op.Const32,
        1,
        1,
        Op.Const32,
        2,
        0,
        Op.Const64,
        0,
        0,
        Op.Repeat32,
        0,
        3,
        Op.Const32,
        0,
        0,
        Op.Alu32,
        2,
        2,
        1,
        Alu.Add,
        Op.EndRepeat,
        Op.Store32,
        0,
        0,
        2,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(resultBytes(prepared(countChangedByBody).run(Vector.empty)), Vector(Vector(3, 0, 0, 0)))

    val laterZeroTrip = encoded(
      6,
      1,
      Vector.empty,
      Vector.empty,
      Vector(4),
      Vector(
        Op.Const32,
        0,
        2,
        Op.Const32,
        1,
        2,
        Op.Const32,
        2,
        2,
        Op.Const32,
        3,
        0,
        Op.Const64,
        0,
        0,
        Op.Repeat32,
        0,
        5,
        Op.If32,
        5,
        Op.Const32,
        1,
        0,
        Op.Else,
        Op.Const32,
        1,
        2,
        Op.EndIf,
        Op.Repeat32,
        1,
        4,
        Op.EndRepeat,
        Op.Move32,
        3,
        4,
        Op.EndRepeat,
        Op.Store32,
        0,
        0,
        3,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(resultBytes(prepared(laterZeroTrip).run(Vector.empty)), Vector(Vector(0, 0, 0, 0)))
  }

  test("loop indices are read-only and unsigned high-bit counts fail on the first body operation") {
    val indexSum = encoded(
      4,
      1,
      Vector.empty,
      Vector.empty,
      Vector(4),
      Vector(
        Op.Const32,
        0,
        3,
        Op.Const32,
        1,
        0,
        Op.Const64,
        0,
        0,
        Op.Repeat32,
        0,
        2,
        Op.Alu32,
        1,
        1,
        2,
        Alu.Add,
        Op.EndRepeat,
        Op.Store32,
        0,
        0,
        1,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(resultBytes(prepared(indexSum).run(Vector.empty)), Vector(Vector(3, 0, 0, 0)))

    val writeIndex = encoded(
      2,
      1,
      Vector.empty,
      Vector.empty,
      Vector.empty,
      Vector(
        Op.Const32,
        0,
        1,
        Op.Repeat32,
        0,
        1,
        Op.Const32,
        1,
        0,
        Op.EndRepeat,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(prepare(writeIndex).left.toOption, Some(MalformedProgram))

    val highCount = BigInt(1) << 63
    val finiteError = encoded(
      1,
      2,
      Vector(1),
      Vector.empty,
      Vector.empty,
      Vector(
        Op.Const64,
        0,
        highCount,
        Op.Repeat64,
        0,
        1,
        Op.Load32,
        0,
        0,
        0,
        Op.EndRepeat,
        Op.Halt
      ).map {
        case b: BigInt => b
        case n: Int    => BigInt(n)
      }
    )
    val run = prepared(finiteError).run(Vector(Vector(0.toByte)))
    assertEquals(run.error, Some(OutOfBounds))
  }

  test("unbalanced, crossed, and malformed control markers are rejected before execution") {
    val cases = Vector(
      Vector(Op.If32, 0, Op.EndRepeat, Op.Halt),
      Vector(Op.If32, 0, Op.Else, Op.Else, Op.EndIf, Op.Halt),
      Vector(Op.Repeat32, 0, 1, Op.EndIf, Op.Halt),
      Vector(Op.If32, 0, Op.Repeat32, 1, 2, Op.EndIf, Op.EndRepeat, Op.Halt),
      Vector(Op.If32, 0, Op.Halt),
      Vector(Op.Else, Op.Halt)
    )
    cases.foreach { code =>
      val program = encoded(3, 3, Vector.empty, Vector.empty, Vector.empty, code.map(BigInt(_)))
      assertEquals(prepare(program).left.toOption, Some(MalformedProgram), code.toString)
    }
  }

  test("register and buffer schemas are checked, with zero-initialized scalar banks") {
    val badRegister = encoded(
      1,
      0,
      Vector.empty,
      Vector.empty,
      Vector.empty,
      Vector(
        Op.Const32,
        1,
        0,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(prepare(badRegister).left.toOption, Some(MalformedProgram))

    val inputWrite = encoded(
      1,
      1,
      Vector(1),
      Vector.empty,
      Vector.empty,
      Vector(
        Op.Const64,
        0,
        0,
        Op.Const32,
        0,
        1,
        Op.Store8,
        0,
        0,
        0,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(prepare(inputWrite).left.toOption, Some(MalformedProgram))

    val defaultZero = encoded(
      0,
      1,
      Vector.empty,
      Vector.empty,
      Vector(8),
      Vector(
        Op.Const64,
        0,
        0,
        Op.Store64,
        0,
        0,
        0,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(resultBytes(prepared(defaultZero).run(Vector.empty)), Vector(Vector.fill(8)(0)))

    val malformedSchema =
      encoded(0, 0, Vector(MaxBufferBytes + 1), Vector.empty, Vector.empty, Vector(Op.Halt).map(BigInt(_)))
    assertEquals(prepare(malformedSchema).left.toOption, Some(MalformedProgram))
    val wrongInputExtent = prepared(encoded(0, 0, Vector(2), Vector.empty, Vector(1), Vector(Op.Halt).map(BigInt(_))))
    assertEquals(wrongInputExtent.run(Vector.empty).error, Some(InvalidArgument))
    assertEquals(wrongInputExtent.run(Vector(Vector(1.toByte))).error, Some(InvalidArgument))
  }

  test("bounds, arithmetic faults, word extensions, and overlapping views are exact") {
    val outOfBounds = encoded(
      1,
      1,
      Vector(1),
      Vector.empty,
      Vector.empty,
      Vector(
        Op.Const64,
        0,
        0,
        Op.Load32,
        0,
        0,
        0,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(prepared(outOfBounds).run(Vector(Vector(0.toByte))).error, Some(OutOfBounds))

    val divideByZero = encoded(
      3,
      0,
      Vector.empty,
      Vector.empty,
      Vector.empty,
      Vector(
        Op.Const32,
        0,
        7,
        Op.Const32,
        1,
        0,
        Op.Alu32,
        2,
        0,
        1,
        Alu.UDiv,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(prepared(divideByZero).run(Vector.empty).error, Some(ArithmeticFault))

    val extension = encoded(
      1,
      2,
      Vector.empty,
      Vector.empty,
      Vector(8),
      Vector(
        Op.Const32,
        0,
        0xffff_ffffL,
        Op.Extend32To64,
        1,
        0,
        Op.Const64,
        0,
        0,
        Op.Store64,
        0,
        0,
        1,
        Op.Halt
      ).map(n => BigInt(n))
    )
    assertEquals(resultBytes(prepared(extension).run(Vector.empty)), Vector(Vector(0xff, 0xff, 0xff, 0xff, 0, 0, 0, 0)))

    val alias = encoded(
      2,
      2,
      Vector.empty,
      Vector.empty,
      Vector(4),
      Vector(
        Op.Const64,
        0,
        0,
        Op.Const64,
        1,
        1,
        Op.Const32,
        0,
        0x44332211,
        Op.Store32,
        0,
        0,
        0,
        Op.Load16,
        1,
        0,
        1,
        Op.Const64,
        1,
        2,
        Op.Store16,
        0,
        1,
        1,
        Op.Halt
      ).map(BigInt(_))
    )
    assertEquals(resultBytes(prepared(alias).run(Vector.empty)), Vector(Vector(0x11, 0x22, 0x22, 0x33)))
  }

  test("each invocation copies inputs, freezes outputs, and supports concurrent reuse") {
    import scala.concurrent.duration._
    import scala.concurrent.{Await, ExecutionContext, Future}
    implicit val executionContext: ExecutionContext = ExecutionContext.global

    val program = prepared(
      encoded(
        1,
        1,
        Vector(1),
        Vector.empty,
        Vector(1),
        Vector(
          Op.Const64,
          0,
          0,
          Op.Load8,
          0,
          0,
          0,
          Op.Store8,
          1,
          0,
          0,
          Op.Halt
        ).map(BigInt(_))
      )
    )
    val runs = Future.traverse((0 until 16).toVector) { value => Future(program.run(Vector(Vector(value.toByte)))) }
    val results = Await.result(runs, 10.seconds)
    assertEquals(results.map(r => resultBytes(r).head.head), (0 until 16).toVector)
    assert(results.forall(_.error.isEmpty))

    val immutableInput = Vector(0x5a.toByte)
    val first = program.run(Vector(immutableInput))
    val frozen = first.outputs
    val failed = program.run(Vector.empty)
    val next = program.run(Vector(Vector(0x11.toByte)))
    assertEquals(failed.error, Some(InvalidArgument))
    assertEquals(first.outputs, frozen)
    assertEquals(resultBytes(first), Vector(Vector(0x5a)))
    assertEquals(immutableInput.map(_ & 0xff), Vector(0x5a))
    assertEquals(resultBytes(next), Vector(Vector(0x11)))
  }
}
