package com.raccoonlang

import NativeGpuAst._

/**
 * Mutable addressed buffers for one native invocation. Every instance owns fresh primitive arrays; no array is returned
 * to the caller and requests retain evaluated operands rather than rereading warp registers.
 */
private[raccoonlang] final class NativeGpuDevice(plan: NativeGpuBackend.Plan, inputs: NativeGpuBackend.Inputs) {
  import NativeGpuDevice._

  private val metadata = plan.metadata
  private val a = inputs.a.toArray
  private val b = inputs.b.toArray
  private val shared = new Array[Int](MaxSharedBytes / 4)
  private val output = Array.fill(OutputCells)(RingModulus)
  private val coverage = new Array[Byte](OutputCells)
  private val tmem = Array.fill(OutputCells)(RingModulus)

  private var tmemAddress = BigInt(0)
  private var tmemColumns = BigInt(0)
  private var tmemAllocated = false
  private var tmemInitialized = false
  private var outputWrites = 0

  val initializationFailure: Option[String] = {
    if (plan.kernel.dynamicShared != metadata.dynamicShared)
      Some("dynamic shared extent does not match checked inputs")
    else if (metadata.dynamicShared <= 0 || metadata.dynamicShared > MaxSharedBytes || metadata.dynamicShared % 4 != 0)
      Some("dynamic shared extent is outside the TinyDevice backing")
    else if (a.length != InputCells || b.length != InputCells)
      Some("prepared input arrays do not match the checked 128x64 maps")
    else if ((a.iterator ++ b.iterator).exists(value => value < 0 || value >= RingModulus))
      Some("prepared input value is outside Z/257")
    else None
  }

  def resolveMap(name: String): Option[ResolvedMap] =
    plan.kernel.launcher.flatMap(_.maps.find(_.param == name)).flatMap { encoding =>
      for {
        rows <- extent(encoding.rows)
        cols <- extent(encoding.cols)
      } yield ResolvedMap(encoding, rows, cols)
    }

  def sharedRange(address: BigInt, width: BigInt, alignment: BigInt): Boolean =
    address >= 0 && width >= 0 && alignment > 0 && address % alignment == 0 && address + width <= metadata.dynamicShared

  def readShared(address: BigInt, tpe: DType): Option[BigInt] = {
    val (width, alignment) = tpe match {
      case DType.BF16            => (BigInt(2), BigInt(2))
      case DType.F32 | DType.U32 => (BigInt(4), BigInt(4))
      case _                     => return None
    }
    if (!sharedRange(address, width, alignment)) return None
    val wordIndex = (address / 4).toInt
    val word = BigInt(shared(wordIndex) & 0xffffffffL)
    Some(tpe match {
      case DType.BF16 => if (address % 4 == 0) word & 0xffff else word >> 16
      case _          => word
    })
  }

  def readSharedLanes(addresses: Vector[BigInt], activeMask: BigInt, tpe: DType): Option[Vector[BigInt]] = {
    if (addresses.length != LaneWidth) return None
    val values = Vector.newBuilder[BigInt]
    var lane = 0
    while (lane < LaneWidth) {
      if (laneActive(activeMask, lane)) {
        readShared(addresses(lane), tpe) match {
          case None        => return None
          case Some(value) => values += value
        }
      } else values += BigInt(0)
      lane += 1
    }
    Some(values.result())
  }

  def writeSharedLanes(
      addresses: Vector[BigInt],
      values: Vector[BigInt],
      activeMask: BigInt,
      tpe: DType
  ): Boolean = writeSharedLanes(addresses, values, activeMask, tpe, null)

  def writeSharedLanes(
      addresses: Vector[BigInt],
      values: Vector[BigInt],
      activeMask: BigInt,
      tpe: DType,
      transaction: SharedWriteTransaction
  ): Boolean = {
    if (addresses.length != LaneWidth || values.length != LaneWidth) return false
    // Validate the whole vector before mutation. TinyDevice's persistent write sequence publishes only on success.
    var lane = 0
    var activeWrites = 0
    while (lane < LaneWidth) {
      if (laneActive(activeMask, lane)) {
        if (!sharedWriteValid(addresses(lane), values(lane), tpe)) return false
        activeWrites += 1
      }
      lane += 1
    }
    if (transaction != null && (!transaction.belongsTo(this) || !transaction.reserve(activeWrites))) return false
    lane = 0
    while (lane < LaneWidth) {
      if (laneActive(activeMask, lane)) {
        if (transaction != null) transaction.record((addresses(lane) / 4).toInt, shared((addresses(lane) / 4).toInt))
        writeSharedUnchecked(addresses(lane), values(lane), tpe)
      }
      lane += 1
    }
    true
  }

  def beginSharedTransaction(maxWrites: Int): SharedWriteTransaction = {
    require(maxWrites >= 0, "shared transaction capacity must be non-negative")
    new SharedWriteTransaction(maxWrites)
  }

  def commitSharedTransaction(transaction: SharedWriteTransaction): Unit = {
    require(transaction.belongsTo(this), "shared transaction belongs to another device")
    transaction.commit()
  }

  def rollbackSharedTransaction(transaction: SharedWriteTransaction): Unit = {
    require(transaction.belongsTo(this), "shared transaction belongs to another device")
    transaction.rollback()
  }

  def load(map: ResolvedMap, destination: BigInt, x: BigInt, y: BigInt): Either[String, Completion] = {
    if (!validInputLoad(map, destination, x, y))
      return Left("TinyDevice: unsupported TMA input map, coordinate, box, or shared destination")

    var wordOffset = 0
    while (wordOffset < 4096) {
      val chunk = wordOffset / 256
      val withinChunk = wordOffset % 256
      val relativeRow = chunk * 8 + withinChunk / 32
      val withinRow = withinChunk % 32
      val physicalGroup = withinRow / 4
      val wordInGroup = withinRow % 4
      val logicalGroup = physicalGroup ^ (relativeRow & 7)
      val col = x.toInt + logicalGroup * 8 + wordInGroup * 2
      val row = y.toInt + relativeRow
      val lower = inputScalar(map.encoding.source, row, col)
      val upper = inputScalar(map.encoding.source, row, col + 1)
      val packed = lower + (upper.toLong << 16)
      shared((destination.toInt / 4) + wordOffset) = packed.toInt
      wordOffset += 1
    }
    Right(Completion(Vector.empty, BigInt(16384), BigInt(0), BigInt(0)))
  }

  def store(map: ResolvedMap, x: BigInt, y: BigInt, source: BigInt): Either[String, Completion] = {
    if (!validOutputStore(map, x, y, source))
      return Left("TinyDevice: unsupported TMA output map, coordinate, box, or shared source")

    val staged = new Array[Int](StoreCells)
    var row = 0
    while (row < 32) {
      var col = 0
      while (col < 32) {
        val address = source.toInt + row * 128 + 16 * (col / 4 ^ (row & 7)) + 4 * (col & 3)
        val outputIndex = (y.toInt + row) * OutputSide + x.toInt + col
        if (coverage(outputIndex) != 0)
          return Left("TinyDevice: TMA output store overlapped, read invalid data, or exceeded output bounds")
        val value = readShared(address, DType.F32).getOrElse(BigInt(-1)).toInt
        if (value < 0 || value >= RingModulus)
          return Left("TinyDevice: TMA output store overlapped, read invalid data, or exceeded output bounds")
        staged(row * 32 + col) = value
        col += 1
      }
      row += 1
    }

    row = 0
    while (row < 32) {
      var col = 0
      while (col < 32) {
        val outputIndex = (y.toInt + row) * OutputSide + x.toInt + col
        output(outputIndex) = staged(row * 32 + col)
        coverage(outputIndex) = 1
        outputWrites += 1
        col += 1
      }
      row += 1
    }
    Right(Completion(Vector.empty, BigInt(4096), BigInt(0), BigInt(0)))
  }

  def allocate(group: Group, slot: BigInt, columns: BigInt, activeMask: BigInt): Option[String] = {
    if (activeMask != FullMask) return Some("tcgen05.alloc requires all 32 lanes of the issuing warp to participate")
    if (group != Group.One) return Some("two-CTA tensor-memory allocation")
    if (!sharedWriteValid(slot, BigInt(0), DType.U32))
      return Some("TinyDevice: tensor-memory allocation slot is not a valid shared u32")
    if (tmemAllocated || columns != OutputSide)
      return Some("TinyDevice: unsupported tensor-memory allocation address or columns")
    java.util.Arrays.fill(tmem, RingModulus)
    tmemAddress = 0
    tmemColumns = columns
    tmemAllocated = true
    tmemInitialized = false
    writeSharedUnchecked(slot, BigInt(0), DType.U32)
    None
  }

  def relinquish(group: Group, activeMask: BigInt): Option[String] = {
    if (group == Group.Two) Some("two-CTA tensor-memory permit relinquish")
    else if (activeMask != FullMask) Some("tcgen05.relinquish requires all 32 lanes of the issuing warp to participate")
    else None
  }

  def deallocate(group: Group, address: BigInt, columns: BigInt, activeMask: BigInt): Option[String] = {
    if (activeMask != FullMask) return Some("tcgen05.dealloc requires all 32 lanes of the issuing warp to participate")
    if (group != Group.One) return Some("two-CTA tensor-memory deallocation")
    if (!tmemAllocated || address != tmemAddress || columns != tmemColumns)
      return Some("TinyDevice: tensor-memory deallocation does not match the live allocation")
    tmemAllocated = false
    tmemInitialized = false
    None
  }

  def mma(desc: MmaDesc): Either[String, Completion] = {
    if (!validMma(desc))
      return Left("TinyDevice: unsupported MMA group, accumulator, descriptor, shape, or allocation")
    val (aDesc, bDesc, descriptor, accumulate) = desc.a match {
      case MmaSource.Shared(aValue) => (aValue, desc.b, desc.descriptor, desc.accumulate)
      case MmaSource.Tmem(_)        => return Left("TinyDevice: tensor-memory A operand is unsupported")
    }
    val aRows = new Array[Int](OutputSide * MmaWidth)
    val bRows = new Array[Int](OutputSide * MmaWidth)
    if (!readOperand(aDesc, aRows) || !readOperand(bDesc, bRows))
      return Left("TinyDevice: MMA operand descriptor addressed a non-ring shared value")

    val staged = new Array[Int](OutputCells)
    var row = 0
    while (row < OutputSide) {
      var col = 0
      while (col < OutputSide) {
        var acc = if (accumulate == 0) 0 else tmem(row * OutputSide + col)
        var k = 0
        while (k < MmaWidth) {
          acc = (acc + aRows(row * MmaWidth + k) * bRows(col * MmaWidth + k)) % RingModulus
          k += 1
        }
        staged(row * OutputSide + col) = acc
        col += 1
      }
      row += 1
    }
    System.arraycopy(staged, 0, tmem, 0, OutputCells)
    tmemInitialized = true
    Right(Completion(Vector.empty, BigInt(0), BigInt(262144), BigInt(262144)))
  }

  def tmemLoad(
      shape: TmemShape,
      destinations: Vector[BigInt],
      baseAddress: BigInt,
      warpGroupPosition: BigInt,
      activeMask: BigInt
  ): Either[String, Completion] = {
    if (
      shape != TmemShape.S32x32b || destinations.length != 8 || activeMask != FullMask ||
      baseAddress < 0 || baseAddress >= U32Limit || !tmemReady
    )
      return Left("TinyDevice: unsupported tensor-memory load shape, address, mask, or allocation")
    val quadrant = warpGroupPosition
    val firstColumn = baseAddress % TmemQuadrantBytes
    if (
      quadrant < 0 || quadrant >= 4 || baseAddress / TmemQuadrantBytes != quadrant * 32 ||
      firstColumn % 8 != 0 || firstColumn >= OutputSide || firstColumn + 8 > OutputSide
    )
      return Left("TinyDevice: unsupported tensor-memory load shape, address, mask, or allocation")

    val first = firstColumn.toInt
    val q = quadrant.toInt
    val writes = Vector.tabulate(8) { offset =>
      val lanes = Vector.tabulate(LaneWidth) { lane =>
        val value = tmem((q * 32 + lane) * OutputSide + first + offset)
        if (value >= RingModulus) return Left("TinyDevice: tensor-memory load addressed an unwritten cell")
        BigInt(value)
      }
      RegisterWrite(destinations(offset), lanes)
    }
    Right(Completion(writes, BigInt(0), BigInt(0), BigInt(0)))
  }

  def isTmemQuiescent: Boolean = !tmemAllocated
  def outputIsComplete: Boolean =
    outputWrites == OutputCells && coverage.forall(_ == 1) && output.forall(v => v >= 0 && v < RingModulus)
  def outputSnapshot: Vector[Int] = output.toVector

  private def extent(name: String): Option[BigInt] = name match {
    case "M" => Some(metadata.m)
    case "N" => Some(metadata.n)
    case "K" => Some(metadata.k)
    case _   => None
  }

  private def validInputLoad(map: ResolvedMap, destination: BigInt, x: BigInt, y: BigInt): Boolean = {
    val inputKind = mapKind(map).exists(kind => kind == "a" || kind == "b")
    inputKind && map.encoding.inner == 64 && map.encoding.outer == 128 && x == 0 && y == 0 &&
    map.rows == 128 && map.cols == 64 && destination % 1024 == 0 &&
    sharedRange(destination, BigInt(16384), BigInt(1024))
  }

  private def validOutputStore(map: ResolvedMap, x: BigInt, y: BigInt, source: BigInt): Boolean = {
    mapKind(map).contains("c") && map.encoding.inner == 32 && map.encoding.outer == 32 &&
    x >= 0 && y >= 0 && x % 32 == 0 && y % 32 == 0 &&
    x + 32 <= map.cols && y + 32 <= map.rows && source % 1024 == 0 &&
    sharedRange(source, BigInt(4096), BigInt(1024))
  }

  private def mapKind(map: ResolvedMap): Option[String] = {
    if (map.encoding == metadata.aMap && map.rows == metadata.m && map.cols == metadata.k) Some("a")
    else if (map.encoding == metadata.bMap && map.rows == metadata.n && map.cols == metadata.k) Some("b")
    else if (map.encoding == metadata.cMap && map.rows == metadata.m && map.cols == metadata.n) Some("c")
    else None
  }

  private def inputScalar(source: Param, row: Int, col: Int): Long = {
    val selected = source match {
      // decodePlan validates the exact typed map source before any load request reaches this device.
      case Param.Input(DType.BF16, "A") => a
      case Param.Input(DType.BF16, "B") => b
      case _                            => return RingModulus.toLong
    }
    if (row < 0 || row >= 128 || col < 0 || col >= 64) RingModulus.toLong
    else selected(row * 64 + col).toLong
  }

  private def sharedWriteValid(address: BigInt, value: BigInt, tpe: DType): Boolean = tpe match {
    case DType.BF16            => sharedRange(address, BigInt(2), BigInt(2)) && value >= 0 && value < 65536
    case DType.F32 | DType.U32 => sharedRange(address, BigInt(4), BigInt(4)) && value >= 0 && value < U32Limit
    case _                     => false
  }

  private def writeSharedUnchecked(address: BigInt, value: BigInt, tpe: DType): Unit = {
    val wordIndex = (address / 4).toInt
    val old = BigInt(shared(wordIndex) & 0xffffffffL)
    val next = tpe match {
      case DType.BF16 if address % 4 == 0 => (old & ~BigInt(0xffff)) | value
      case DType.BF16                     => (old & BigInt(0xffff)) | (value << 16)
      case _                              => value
    }
    shared(wordIndex) = next.toInt
  }

  private def readOperand(desc: OperandDesc, rows: Array[Int]): Boolean = {
    var row = 0
    while (row < OutputSide) {
      var localK = 0
      while (localK < MmaWidth) {
        val k = desc.step * 16 + localK
        val address = desc.baseByte + row * 128 + 16 * (k / 8 ^ row % 8) + 2 * (k % 8)
        readShared(address, DType.BF16) match {
          case Some(value) if value < RingModulus => rows(row * MmaWidth + localK) = value.toInt
          case _                                  => return false
        }
        localK += 1
      }
      row += 1
    }
    true
  }

  private def validMma(desc: MmaDesc): Boolean = {
    val accumulationValid = desc.accumulate == 0 || desc.accumulate == 1
    val ready = tmemAllocated && tmemAddress == 0 && tmemColumns == 128 &&
      (desc.accumulate == 0 || tmemInitialized)
    val descriptorValid = desc.group == Group.One && desc.accumulator == 0 && desc.descriptor.m == 128 &&
      desc.descriptor.n == 128 && !desc.descriptor.transposeB && accumulationValid && ready
    descriptorValid && ((desc.a, desc.b) match {
      case (MmaSource.Shared(aDesc), bDesc) =>
        val stage = aDesc.baseByte - 33792
        aDesc.lbo == 0 && bDesc.lbo == 0 && aDesc.step == bDesc.step && aDesc.step >= 0 && aDesc.step < 4 &&
        aDesc.baseByte >= 33792 && stage >= 0 && stage % 32768 == 0 &&
        aDesc.baseByte + 32768 <= 164864 && bDesc.baseByte == aDesc.baseByte + 16384
      case _ => false
    })
  }

  private def tmemReady: Boolean = tmemAllocated && tmemInitialized && tmemAddress == 0 && tmemColumns == 128

  private def laneActive(mask: BigInt, lane: Int): Boolean = ((mask >> lane) & 1) != 0

  final class SharedWriteTransaction private[NativeGpuDevice] (capacity: Int) {
    private var undo = new Array[Long](capacity)
    private var size = 0
    private var finished = false

    private[NativeGpuDevice] def belongsTo(device: NativeGpuDevice): Boolean = NativeGpuDevice.this eq device
    private[NativeGpuDevice] def reserve(count: Int): Boolean = {
      if (finished || count < 0) return false
      val required = size.toLong + count.toLong
      if (required > Int.MaxValue) return false
      if (required <= undo.length) true
      else {
        var capacity = math.max(4, undo.length)
        while (capacity < required) {
          capacity = math.min(Int.MaxValue.toLong, capacity.toLong * 2).toInt
        }
        undo = java.util.Arrays.copyOf(undo, capacity)
        true
      }
    }

    private[NativeGpuDevice] def record(wordIndex: Int, oldWord: Int): Unit = {
      require(reserve(1), "shared transaction undo journal is exhausted or closed")
      undo(size) = (wordIndex.toLong << 32) | (oldWord.toLong & 0xffffffffL)
      size += 1
    }

    private[NativeGpuDevice] def commit(): Unit = {
      require(!finished, "shared transaction is already closed")
      size = 0
      finished = true
    }

    private[NativeGpuDevice] def rollback(): Unit = {
      require(!finished, "shared transaction is already closed")
      while (size > 0) {
        size -= 1
        val entry = undo(size)
        shared((entry >>> 32).toInt) = entry.toInt
      }
      finished = true
    }
  }
}

private[raccoonlang] object NativeGpuDevice {
  private val LaneWidth = 32
  private val MaxSharedBytes = 262144
  private val InputCells = 8192
  private val OutputSide = 128
  private val OutputCells = OutputSide * OutputSide
  private val StoreCells = 32 * 32
  private val RingModulus = 257
  private val MmaWidth = 16
  private val U32Limit = BigInt(1) << 32
  private val TmemQuadrantBytes = BigInt(65536)
  private val FullMask = (BigInt(1) << LaneWidth) - 1

  final case class ResolvedMap(encoding: MapEncoding, rows: BigInt, cols: BigInt)
  final case class OperandDesc(baseByte: BigInt, lbo: BigInt, step: BigInt)
  sealed trait MmaSource
  object MmaSource {
    final case class Shared(desc: OperandDesc) extends MmaSource
    final case class Tmem(address: BigInt) extends MmaSource
  }
  final case class MmaDesc(
      group: Group,
      accumulator: BigInt,
      a: MmaSource,
      b: OperandDesc,
      descriptor: InstrDesc,
      accumulate: BigInt
  )
  final case class RegisterWrite(id: BigInt, lanes: Vector[BigInt])
  final case class Completion(
      registerWrites: Vector[RegisterWrite],
      transferBytes: BigInt,
      scalarMuls: BigInt,
      scalarAdds: BigInt
  )

  sealed trait Request
  object Request {
    final case class TmaLoad(map: ResolvedMap, destination: BigInt, x: BigInt, y: BigInt) extends Request
    final case class TmaStore(map: ResolvedMap, x: BigInt, y: BigInt, source: BigInt) extends Request
    final case class Mma(desc: MmaDesc) extends Request
    final case class TmemLoad(
        shape: TmemShape,
        destinations: Vector[BigInt],
        baseAddress: BigInt,
        warpGroupPosition: BigInt,
        activeMask: BigInt
    ) extends Request
  }
}
