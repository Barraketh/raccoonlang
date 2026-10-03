package com.raccoonlang

import scala.collection.mutable

/** A bounded decoder and executor for immutable, GPU-independent buffer programs. */
private[raccoonlang] object NativeBufferProgram {
  val Magic: BigInt = BigInt("42554646", 16) // ASCII "BUFF"
  val Version: BigInt = 3

  val MaxProgramWords: Int = 1_000_000
  val MaxInstructions: Int = 200_000
  val MaxRegistersPerBank: Int = 65_536
  val MaxBuffers: Int = 256
  val MaxBufferBytes: Int = 64 * 1024 * 1024
  val MaxTotalBufferBytes: Long = 256L * 1024 * 1024
  val MaxMarshalledBytes: Long = 16L * 1024 * 1024
  // The ordinary source representation allocates one packed Nat and one List.cons per output byte.
  val MaxSourceOutputBytes: Long = 256L * 1024

  object BufferRole {
    val Input = 0
    val Scratch = 1
    val Output = 2
  }

  private val U32Mask = 0xffff_ffffL
  private val U8Max = 0xffL
  private val U16Max = 0xffffL
  private val U32Max = 0xffff_ffffL
  private val U64Max = (BigInt(1) << 64) - 1

  object Op {
    val Halt = 0
    val Const32 = 1
    val Const64 = 2
    val Move32 = 3
    val Move64 = 4
    val Alu32 = 5
    val Alu64 = 6
    val Compare32 = 7
    val Compare64 = 8
    val Load8 = 9
    val Load16 = 10
    val Load32 = 11
    val Load64 = 12
    val Store8 = 13
    val Store16 = 14
    val Store32 = 15
    val Store64 = 16
    val If32 = 17
    val Else = 18
    val EndIf = 19
    val Repeat32 = 20
    val Repeat64 = 21
    val EndRepeat = 22
    val Extend32To64 = 23
  }

  object Alu {
    val Add = 0
    val Sub = 1
    val Mul = 2
    val UDiv = 3
    val URem = 4
    val And = 5
    val Or = 6
    val Xor = 7
    val Shl = 8
    val LShr = 9
  }

  object Compare {
    val Eq = 0
    val ULess = 1
  }

  sealed abstract class Error(val code: Int, val description: String)
  case object MalformedProgram extends Error(1, "malformed program")
  case object OutOfBounds extends Error(3, "buffer access out of bounds")
  case object ArithmeticFault extends Error(4, "invalid arithmetic operation")
  case object ResourceLimit extends Error(5, "resource limit exceeded")
  case object InvalidArgument extends Error(6, "invalid run argument")

  final case class RunResult(error: Option[Error], outputs: Vector[Vector[Byte]]) {
    def succeeded: Boolean = error.isEmpty
  }

  private sealed trait Instruction
  private final case class NoArgs(op: Int) extends Instruction
  private final case class Const(dst: Int, value: Long, wide: Boolean) extends Instruction
  private final case class Move(dst: Int, src: Int, wide: Boolean) extends Instruction
  private final case class AluInst(dst: Int, left: Int, right: Int, op: Int, wide: Boolean) extends Instruction
  private final case class CompareInst(dst: Int, left: Int, right: Int, op: Int, wide: Boolean) extends Instruction
  private final case class Load(dst: Int, buffer: Int, offset: Int, bytes: Int, wide: Boolean) extends Instruction
  private final case class Store(buffer: Int, offset: Int, src: Int, bytes: Int, wide: Boolean) extends Instruction
  private final case class IfBegin(condition: Int, elsePc: Int, endPc: Int) extends Instruction
  private final case class ElseMarker(endPc: Int) extends Instruction
  private case object EndIfMarker extends Instruction
  private final case class RepeatBegin(count: Int, index: Int, wide: Boolean, endPc: Int) extends Instruction
  private final case class RepeatEnd(beginPc: Int) extends Instruction
  private final case class Extend32To64(dst: Int, src: Int) extends Instruction
  private final case class BufferSpec(role: Int, size: Int)

  final class Prepared private[NativeBufferProgram] (
      private[NativeBufferProgram] val u32Registers: Int,
      private[NativeBufferProgram] val u64Registers: Int,
      private[NativeBufferProgram] val buffers: Vector[BufferSpec],
      private[NativeBufferProgram] val inputBufferIds: Vector[Int],
      private[NativeBufferProgram] val outputBufferIds: Vector[Int],
      private[NativeBufferProgram] val instructions: Vector[Instruction],
      private[NativeBufferProgram] val maxLoopDepth: Int
  ) {
    def run(inputs: Vector[Vector[Byte]]): RunResult = execute(this, inputs)

    private[raccoonlang] def inputExtents: Vector[Int] =
      inputBufferIds.map(id => buffers(id).size)

    private[raccoonlang] def outputByteCount: Long =
      outputBufferIds.foldLeft(0L)((total, id) => total + buffers(id).size)
  }

  /** Decode and validate every structured region before any run allocates private buffers. */
  def prepare(words: Vector[BigInt]): Either[Error, Prepared] = {
    if (words.length < 6 || words.length > MaxProgramWords) return Left(MalformedProgram)
    if (words(0) != Magic || words(1) != Version) return Left(MalformedProgram)

    def count(at: Int, maximum: Int): Option[Int] =
      words.lift(at).filter(n => n >= 0 && n <= maximum).map(_.toInt)

    val u32Count = count(2, MaxRegistersPerBank)
    val u64Count = count(3, MaxRegistersPerBank)
    val bufferCount = count(4, MaxBuffers)
    val instructionCount = count(5, MaxInstructions)
    if (Vector(u32Count, u64Count, bufferCount, instructionCount).exists(_.isEmpty))
      return Left(MalformedProgram)
    val descriptorWords = bufferCount.get * 2
    if (words.length < 6 + descriptorWords) return Left(MalformedProgram)

    val buffersBuilder = Vector.newBuilder[BufferSpec]
    var totalBytes = 0L
    var marshalledBytes = 0L
    var index = 0
    while (index < bufferCount.get) {
      val roleAt = 6 + 2 * index
      val sizeAt = roleAt + 1
      val role = words(roleAt)
      val sizeWord = words(sizeAt)
      if (role < BufferRole.Input || role > BufferRole.Output) return Left(MalformedProgram)
      sizeWord match {
        case size if size >= 0 && size <= MaxBufferBytes =>
          val asInt = size.toInt
          totalBytes += asInt
          if (totalBytes > MaxTotalBufferBytes) return Left(ResourceLimit)
          if (role == BufferRole.Input || role == BufferRole.Output) {
            marshalledBytes += asInt
            if (marshalledBytes > MaxMarshalledBytes) return Left(ResourceLimit)
          }
          buffersBuilder += BufferSpec(role.toInt, asInt)
        case _ => return Left(MalformedProgram)
      }
      index += 1
    }

    val buffers = buffersBuilder.result()
    val rawCode = words.drop(6 + descriptorWords)
    decodeInstructions(rawCode, instructionCount.get, u32Count.get, u64Count.get, buffers) match {
      case Left(error) => Left(error)
      case Right((instructions, maxLoopDepth)) =>
        Right(
          new Prepared(
            u32Count.get,
            u64Count.get,
            buffers,
            buffers.indices.filter(i => buffers(i).role == BufferRole.Input).toVector,
            buffers.indices.filter(i => buffers(i).role == BufferRole.Output).toVector,
            instructions,
            maxLoopDepth
          )
        )
    }
  }

  private sealed trait Region
  private final case class IfRegion(begin: Int, var elseAt: Int) extends Region
  private final case class RepeatRegion(begin: Int, count: Int, index: Int, wide: Boolean) extends Region

  private def decodeInstructions(
      code: Vector[BigInt],
      instructionCount: Int,
      u32Count: Int,
      u64Count: Int,
      buffers: Vector[BufferSpec]
  ): Either[Error, (Vector[Instruction], Int)] = {
    val raw = mutable.ArrayBuffer.empty[Instruction]
    val regions = mutable.ArrayBuffer.empty[Region]
    val writtenU32 = new Array[Boolean](u32Count)
    val writtenU64 = new Array[Boolean](u64Count)
    val loopIndices32 = new Array[Boolean](u32Count)
    val loopIndices64 = new Array[Boolean](u64Count)
    var activeLoopDepth = 0
    var maxLoopDepth = 0
    var word = 0
    var instruction = 0

    def field(): Option[BigInt] =
      code.lift(word).map { value =>
        word += 1
        value
      }
    def small(max: Int): Option[Int] = field().filter(value => value >= 0 && value <= max).map(_.toInt)
    def buffer(index: Option[Int], writable: Boolean): Boolean =
      index.exists(i => i < buffers.length && (!writable || buffers(i).role != BufferRole.Input))

    while (instruction < instructionCount) {
      val before = word
      small(Int.MaxValue) match {
        case None => return Left(MalformedProgram)
        case Some(Op.Halt) =>
          if (instruction != instructionCount - 1 || regions.nonEmpty) return Left(MalformedProgram)
          raw += NoArgs(Op.Halt)
        case Some(Op.Const32) =>
          (small(Int.MaxValue), field()) match {
            case (Some(dst), Some(value)) if dst < u32Count && value >= 0 && value <= U32Max =>
              writtenU32(dst) = true
              raw += Const(dst, value.toLong, wide = false)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.Const64) =>
          (small(Int.MaxValue), field()) match {
            case (Some(dst), Some(value)) if dst < u64Count && value >= 0 && value <= U64Max =>
              writtenU64(dst) = true
              raw += Const(dst, value.toLong, wide = true)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.Move32) =>
          (small(Int.MaxValue), small(Int.MaxValue)) match {
            case (Some(dst), Some(src)) if dst < u32Count && src < u32Count =>
              writtenU32(dst) = true
              raw += Move(dst, src, wide = false)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.Move64) =>
          (small(Int.MaxValue), small(Int.MaxValue)) match {
            case (Some(dst), Some(src)) if dst < u64Count && src < u64Count =>
              writtenU64(dst) = true
              raw += Move(dst, src, wide = true)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.Alu32) =>
          (small(Int.MaxValue), small(Int.MaxValue), small(Int.MaxValue), small(Alu.LShr)) match {
            case (Some(dst), Some(left), Some(right), Some(op))
                if dst < u32Count && left < u32Count && right < u32Count =>
              writtenU32(dst) = true
              raw += AluInst(dst, left, right, op, wide = false)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.Alu64) =>
          (small(Int.MaxValue), small(Int.MaxValue), small(Int.MaxValue), small(Alu.LShr)) match {
            case (Some(dst), Some(left), Some(right), Some(op))
                if dst < u64Count && left < u64Count && right < u64Count =>
              writtenU64(dst) = true
              raw += AluInst(dst, left, right, op, wide = true)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.Compare32) =>
          (small(Int.MaxValue), small(Int.MaxValue), small(Int.MaxValue), small(Compare.ULess)) match {
            case (Some(dst), Some(left), Some(right), Some(op))
                if dst < u32Count && left < u32Count && right < u32Count =>
              writtenU32(dst) = true
              raw += CompareInst(dst, left, right, op, wide = false)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.Compare64) =>
          (small(Int.MaxValue), small(Int.MaxValue), small(Int.MaxValue), small(Compare.ULess)) match {
            case (Some(dst), Some(left), Some(right), Some(op))
                if dst < u32Count && left < u64Count && right < u64Count =>
              writtenU32(dst) = true
              raw += CompareInst(dst, left, right, op, wide = true)
            case _ => return Left(MalformedProgram)
          }
        case Some(op @ (Op.Load8 | Op.Load16 | Op.Load32)) =>
          (small(Int.MaxValue), small(Int.MaxValue), small(Int.MaxValue)) match {
            case (Some(dst), Some(bufferId), Some(offset))
                if dst < u32Count && buffer(Some(bufferId), writable = false) && offset < u64Count =>
              writtenU32(dst) = true
              val bytes = if (op == Op.Load8) 1 else if (op == Op.Load16) 2 else 4
              raw += Load(dst, bufferId, offset, bytes, wide = false)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.Load64) =>
          (small(Int.MaxValue), small(Int.MaxValue), small(Int.MaxValue)) match {
            case (Some(dst), Some(bufferId), Some(offset))
                if dst < u64Count && buffer(Some(bufferId), writable = false) && offset < u64Count =>
              writtenU64(dst) = true
              raw += Load(dst, bufferId, offset, 8, wide = true)
            case _ => return Left(MalformedProgram)
          }
        case Some(op @ (Op.Store8 | Op.Store16 | Op.Store32)) =>
          (small(Int.MaxValue), small(Int.MaxValue), small(Int.MaxValue)) match {
            case (Some(bufferId), Some(offset), Some(src))
                if buffer(Some(bufferId), writable = true) && offset < u64Count && src < u32Count =>
              val bytes = if (op == Op.Store8) 1 else if (op == Op.Store16) 2 else 4
              raw += Store(bufferId, offset, src, bytes, wide = false)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.Store64) =>
          (small(Int.MaxValue), small(Int.MaxValue), small(Int.MaxValue)) match {
            case (Some(bufferId), Some(offset), Some(src))
                if buffer(Some(bufferId), writable = true) && offset < u64Count && src < u64Count =>
              raw += Store(bufferId, offset, src, 8, wide = true)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.If32) =>
          small(Int.MaxValue) match {
            case Some(condition) if condition < u32Count =>
              val at = raw.length
              raw += IfBegin(condition, -1, -1)
              regions += IfRegion(at, -1)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.Else) =>
          if (regions.isEmpty) return Left(MalformedProgram)
          regions.last match {
            case region: IfRegion if region.elseAt < 0 =>
              region.elseAt = raw.length
              raw += ElseMarker(-1)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.EndIf) =>
          regions.lastOption match {
            case Some(region: IfRegion) =>
              regions.remove(regions.length - 1)
              val end = raw.length
              raw += EndIfMarker
              val begin = raw(region.begin).asInstanceOf[IfBegin]
              raw(region.begin) = begin.copy(elsePc = region.elseAt, endPc = end)
              if (region.elseAt >= 0) raw(region.elseAt) = ElseMarker(end)
            case _ => return Left(MalformedProgram)
          }
        case Some(op @ (Op.Repeat32 | Op.Repeat64)) =>
          (small(Int.MaxValue), small(Int.MaxValue)) match {
            case (Some(countReg), Some(indexReg)) =>
              val wide = op == Op.Repeat64
              val countLimit = if (wide) u64Count else u32Count
              val indexLimit = if (wide) u64Count else u32Count
              if (countReg >= countLimit || indexReg >= indexLimit || countReg == indexReg)
                return Left(MalformedProgram)
              val repeatedIndex = if (wide) loopIndices64(indexReg) else loopIndices32(indexReg)
              if (repeatedIndex) return Left(MalformedProgram)
              if (wide) loopIndices64(indexReg) = true else loopIndices32(indexReg) = true
              val at = raw.length
              raw += RepeatBegin(countReg, indexReg, wide, -1)
              regions += RepeatRegion(at, countReg, indexReg, wide)
              activeLoopDepth += 1
              maxLoopDepth = maxLoopDepth.max(activeLoopDepth)
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.EndRepeat) =>
          regions.lastOption match {
            case Some(region: RepeatRegion) =>
              regions.remove(regions.length - 1)
              val end = raw.length
              raw += RepeatEnd(region.begin)
              val begin = raw(region.begin).asInstanceOf[RepeatBegin]
              raw(region.begin) = begin.copy(endPc = end)
              activeLoopDepth -= 1
            case _ => return Left(MalformedProgram)
          }
        case Some(Op.Extend32To64) =>
          (small(Int.MaxValue), small(Int.MaxValue)) match {
            case (Some(dst), Some(src)) if dst < u64Count && src < u32Count =>
              writtenU64(dst) = true
              raw += Extend32To64(dst, src)
            case _ => return Left(MalformedProgram)
          }
        case _ => return Left(MalformedProgram)
      }
      if (word <= before) return Left(MalformedProgram)
      instruction += 1
    }

    if (word != code.length || regions.nonEmpty || raw.isEmpty || raw.last != NoArgs(Op.Halt))
      return Left(MalformedProgram)
    var reg = 0
    while (reg < u32Count) {
      if (loopIndices32(reg) && writtenU32(reg)) return Left(MalformedProgram)
      reg += 1
    }
    reg = 0
    while (reg < u64Count) {
      if (loopIndices64(reg) && writtenU64(reg)) return Left(MalformedProgram)
      reg += 1
    }
    Right((raw.toVector, maxLoopDepth))
  }

  private def execute(prepared: Prepared, inputs: Vector[Vector[Byte]]): RunResult = {
    if (
      inputs.length != prepared.inputBufferIds.length ||
      inputs.indices.exists(i => inputs(i).length != prepared.buffers(prepared.inputBufferIds(i)).size)
    )
      return RunResult(Some(InvalidArgument), Vector.empty)

    val allBuffers = new Array[Array[Byte]](prepared.buffers.length)
    var inputIndex = 0
    var bufferIndex = 0
    while (bufferIndex < prepared.buffers.length) {
      val spec = prepared.buffers(bufferIndex)
      allBuffers(bufferIndex) = if (spec.role == BufferRole.Input) {
        val copy = inputs(inputIndex).toArray
        inputIndex += 1
        copy
      } else new Array[Byte](spec.size)
      bufferIndex += 1
    }

    val u32 = new Array[Long](prepared.u32Registers)
    val u64 = new Array[Long](prepared.u64Registers)
    val loopBegins = new Array[Int](prepared.maxLoopDepth)
    val loopEnds = new Array[Int](prepared.maxLoopDepth)
    val loopIndices = new Array[Int](prepared.maxLoopDepth)
    val loopWidths = new Array[Boolean](prepared.maxLoopDepth)
    val loopRemaining = new Array[Long](prepared.maxLoopDepth)
    var loopDepth = 0
    var pc = 0
    var halted = false
    var error: Error = null

    def writeRegister(reg: Int, value: Long, wide: Boolean): Unit =
      if (wide) {
        u64(reg) = value
      } else {
        u32(reg) = value & U32Mask
      }

    while (!halted && (error eq null)) {
      if (pc < 0 || pc >= prepared.instructions.length) error = MalformedProgram
      else {
        val currentPc = pc
        val inst = prepared.instructions(pc)
        pc += 1
        inst match {
          case NoArgs(Op.Halt)         => halted = true
          case Const(dst, value, wide) => writeRegister(dst, value, wide)
          case Move(dst, src, wide) =>
            writeRegister(dst, if (wide) u64(src) else u32(src), wide)
          case AluInst(dst, left, right, op, wide) =>
            val bank = if (wide) u64 else u32
            val a = bank(left)
            val b = bank(right)
            var value = 0L
            op match {
              case Alu.Add  => value = a + b
              case Alu.Sub  => value = a - b
              case Alu.Mul  => value = a * b
              case Alu.UDiv => if (b == 0L) error = ArithmeticFault else value = java.lang.Long.divideUnsigned(a, b)
              case Alu.URem => if (b == 0L) error = ArithmeticFault else value = java.lang.Long.remainderUnsigned(a, b)
              case Alu.And  => value = a & b
              case Alu.Or   => value = a | b
              case Alu.Xor  => value = a ^ b
              case Alu.Shl =>
                value = if (java.lang.Long.compareUnsigned(b, if (wide) 64L else 32L) >= 0) 0L else a << b.toInt
              case Alu.LShr =>
                value = if (java.lang.Long.compareUnsigned(b, if (wide) 64L else 32L) >= 0) 0L else a >>> b.toInt
            }
            if (error eq null) writeRegister(dst, value, wide)
          case CompareInst(dst, left, right, op, wide) =>
            val bank = if (wide) u64 else u32
            val isTrue = op match {
              case Compare.Eq    => bank(left) == bank(right)
              case Compare.ULess => java.lang.Long.compareUnsigned(bank(left), bank(right)) < 0
            }
            writeRegister(dst, if (isTrue) 1L else 0L, wide = false)
          case Load(dst, bufferId, offsetReg, bytes, wide) =>
            val start = checkedRange(u64(offsetReg), bytes, allBuffers(bufferId).length)
            if (start < 0) error = OutOfBounds
            else writeRegister(dst, readUnsigned(allBuffers(bufferId), start, bytes), wide)
          case Store(bufferId, offsetReg, src, bytes, wide) =>
            val value = if (wide) u64(src) else u32(src)
            val maximum = bytes match {
              case 1 => U8Max
              case 2 => U16Max
              case 4 => U32Max
              case _ => Long.MaxValue
            }
            val tooWide =
              if (wide) bytes < 8 && java.lang.Long.compareUnsigned(value, maximum) > 0 else !wide && value > maximum
            if (tooWide) error = ArithmeticFault
            else {
              val start = checkedRange(u64(offsetReg), bytes, allBuffers(bufferId).length)
              if (start < 0) error = OutOfBounds else writeUnsigned(allBuffers(bufferId), start, bytes, value)
            }
          case IfBegin(condition, elsePc, endPc) =>
            if (u32(condition) == 0L)
              pc = if (elsePc >= 0) elsePc + 1 else endPc + 1
          case ElseMarker(endPc) => pc = endPc + 1
          case EndIfMarker       => ()
          case RepeatBegin(count, index, wide, endPc) =>
            val trips = if (wide) u64(count) else u32(count)
            writeRegister(index, 0L, wide)
            if (trips == 0L) pc = endPc + 1
            else {
              loopBegins(loopDepth) = currentPc
              loopEnds(loopDepth) = endPc
              loopIndices(loopDepth) = index
              loopWidths(loopDepth) = wide
              loopRemaining(loopDepth) = trips
              loopDepth += 1
            }
          case RepeatEnd(beginPc) =>
            val frame = loopDepth - 1
            if (frame < 0 || loopBegins(frame) != beginPc || loopEnds(frame) != currentPc) error = MalformedProgram
            else {
              if (loopRemaining(frame) == 1L) loopDepth -= 1
              else {
                loopRemaining(frame) -= 1L
                val indexValue =
                  if (loopWidths(frame)) u64(loopIndices(frame)) + 1L
                  else (u32(loopIndices(frame)) + 1L) & U32Mask
                writeRegister(loopIndices(frame), indexValue, loopWidths(frame))
                pc = loopBegins(frame) + 1
              }
            }
          case Extend32To64(dst, src) =>
            writeRegister(dst, u32(src), wide = true)
          case NoArgs(_) => error = MalformedProgram
        }
      }
    }

    if (error ne null) RunResult(Some(error), Vector.empty)
    else {
      val outputs = prepared.outputBufferIds.map(id => allBuffers(id).toVector)
      RunResult(None, outputs)
    }
  }

  private def checkedRange(offset: Long, bytes: Int, extent: Int): Int = {
    if (java.lang.Long.compareUnsigned(offset, extent.toLong) > 0) -1
    else {
      val start = offset.toInt
      if (bytes > extent - start) -1 else start
    }
  }

  private def readUnsigned(bytes: Array[Byte], start: Int, width: Int): Long = {
    var result = 0L
    var i = 0
    while (i < width) {
      result |= (bytes(start + i).toLong & 0xffL) << (8 * i)
      i += 1
    }
    result
  }

  private def writeUnsigned(bytes: Array[Byte], start: Int, width: Int, value: Long): Unit = {
    var i = 0
    while (i < width) {
      bytes(start + i) = (value >>> (8 * i)).toByte
      i += 1
    }
  }
}
