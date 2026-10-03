package com.raccoonlang

import java.nio.file.Path

/** Shared checked-source and Value decoding helpers for the GPU-buffer integration test and benchmark. */
private[raccoonlang] object BufferGpuSpikeSupport {
  val StackBytes: Long = 256L << 20
  val RingModulus = 257
  val Rows = 128
  val Columns = 128
  val K = 64
  val InputCells = Rows * K
  val OutputCells = Rows * Columns

  final case class Api(
      kernel: Value,
      prepare: Value,
      inputs: Value,
      sourceRun: Value,
      sourceOutputs: Value,
      sourceStats: Value,
      sourceErrors: Value,
      mutantNames: Value,
      chooseMutant: Value,
      runMutant: Value,
      compile: Value,
      run: Value,
      planStats: Value,
      planProgram: Value,
      programWords: Value,
      renamedKernel: Value
  )
  final case class Loaded(api: Api, strings: Option[Value.ValidatedStringLayout], elapsedNs: Long)
  final case class Inputs(prepared: Value, aValue: Value, bValue: Value, a: Vector[Int], b: Vector[Int])
  final case class Stats(
      warpSteps: Long,
      asyncCompletions: Long,
      tmaBytes: Long,
      scalarMuls: Long,
      scalarAdds: Long,
      mmaInstructions: Long,
      tmemLoads: Long,
      tmaStores: Long
  ) {
    def scalarOps: Long = scalarMuls + scalarAdds
  }
  final case class Success(outputs: Vector[Int], stats: Stats)
  sealed trait RunError
  final case class InvalidInput(index: Int) extends RunError
  final case class BufferFailure(code: BigInt) extends RunError
  case object InvalidOutput extends RunError
  final case class UnknownError(value: Value) extends RunError
  sealed trait CompileResult
  final case class Ready(plan: Value) extends CompileResult
  final case class Rejected(code: BigInt) extends CompileResult
  sealed trait GpuResult
  final case class GpuSuccess(value: Success) extends GpuResult
  final case class GpuFailure(error: RunError) extends GpuResult

  val CanonicalStats: Stats = Stats(1251L, 88L, 98304L, 1048576L, 1048576L, 4L, 64L, 16L)
  val OverlapStats: Stats = Stats(1267L, 104L, 98304L, 1048576L, 1048576L, 4L, 80L, 16L)
  val NonfuelRejectNames: Vector[String] = Vector(
    "descriptor",
    "output-offset",
    "out-of-bounds",
    "partial-aligned",
    "partial-wait",
    "unsupported",
    "unsupported-regpool",
    "missing-commit",
    "missing-tma-completion",
    "not-quiescent"
  )

  def loadApi(entry: Path, gpuRoot: Path, repoRoot: Path, prelude: Prelude.Config): Loaded = {
    val start = System.nanoTime()
    val checkedValue = Execution.onStack(StackBytes) {
      val loaded = ModuleLoader.load(entry, ModuleLoader.LoadConfig(Vector(gpuRoot, repoRoot), prelude))
      val checked = Execution.check(Execution.elaborate(loaded.program, prelude))
      val result = Interpreter.run(checked).getOrElse(throw new IllegalStateException(s"$entry has no result"))
      (result, checked.strings)
    }
    val elapsed = System.nanoTime() - start
    val (value, strings) = checkedValue
    Loaded(decodeApi(value), strings, elapsed)
  }

  def decodeApi(value: Value): Api = {
    val (kernel, rest0) = pair(value, "BufferGpuApi")
    val (prepare, rest1) = pair(rest0, "BufferGpuApi")
    val (inputs, rest2) = pair(rest1, "BufferGpuApi")
    val (sourceRun, rest3) = pair(rest2, "BufferGpuApi")
    val (sourceOutputs, rest4) = pair(rest3, "BufferGpuApi")
    val (sourceStats, rest5) = pair(rest4, "BufferGpuApi")
    val (sourceErrors, rest6) = pair(rest5, "BufferGpuApi")
    val (mutantNames, rest7) = pair(rest6, "BufferGpuApi")
    val (chooseMutant, rest8) = pair(rest7, "BufferGpuApi")
    val (runMutant, rest9) = pair(rest8, "BufferGpuApi")
    val (compile, rest10) = pair(rest9, "BufferGpuApi")
    val (run, rest11) = pair(rest10, "BufferGpuApi")
    val (planStats, rest12) = pair(rest11, "BufferGpuApi")
    val (planProgram, rest13) = pair(rest12, "BufferGpuApi")
    val (programWords, renamedKernel) = pair(rest13, "BufferGpuApi")
    Api(
      kernel,
      prepare,
      inputs,
      sourceRun,
      sourceOutputs,
      sourceStats,
      sourceErrors,
      mutantNames,
      chooseMutant,
      runMutant,
      compile,
      run,
      planStats,
      planProgram,
      programWords,
      renamedKernel
    )
  }

  def applyOnStack(function: Value, arguments: Value*): Value =
    Execution.onStack(StackBytes) { Interpreter.evalApply(function, arguments.toVector) }

  def packedNat(value: BigInt, natType: Value): Value = Value.VPacked.nat(value, natType)

  def natOf(value: Value): BigInt = value match {
    case packed: Value.VPacked if packed.codec eq Value.NatCodec           => packed.natValue.get
    case Value.VCtor(head, Vector(), _) if head.name == "Nat.zero"         => BigInt(0)
    case Value.VCtor(head, Vector(previous), _) if head.name == "Nat.succ" => BigInt(1) + natOf(previous)
    case other => throw new IllegalArgumentException(s"Expected Nat, got $other")
  }

  def natLong(value: Value, label: String): Long = {
    val number = natOf(value)
    require(number.isValidLong, s"$label=$number does not fit Long")
    number.toLong
  }

  def pair(value: Value, label: String): (Value, Value) = value match {
    case Value.VCtor(head, Vector(left, right), _) if head.name == "Pair.mk" => (left, right)
    case other => throw new IllegalArgumentException(s"Expected Pair.mk for $label, got $other")
  }

  def list(value: Value, label: String): Vector[Value] = {
    val out = Vector.newBuilder[Value]
    var current = value
    var index = 0
    var done = false
    while (!done) {
      current match {
        case Value.VCtor(head, Vector(), _) if head.name == "List.nil" => done = true
        case Value.VCtor(head, Vector(item, rest), _) if head.name == "List.cons" =>
          out += item
          current = rest
          index += 1
        case other => throw new IllegalArgumentException(s"Malformed $label list at index $index: $other")
      }
    }
    out.result()
  }

  def natList(value: Value, label: String): Vector[Int] =
    list(value, label).zipWithIndex.map { case (item, index) =>
      val number = natOf(item)
      require(number.isValidInt, s"$label[$index]=$number does not fit Int")
      number.toInt
    }

  def sourceString(value: Value, strings: Option[Value.ValidatedStringLayout], label: String): String =
    PrettyPrinter.rawString(value, strings).getOrElse(throw new IllegalArgumentException(s"Malformed $label String"))

  def namedStrings(value: Value, strings: Option[Value.ValidatedStringLayout]): Vector[(String, Value)] =
    list(value, "mutant names").zipWithIndex.map { case (name, index) =>
      (sourceString(name, strings, s"mutantNames[$index]"), name)
    }

  def optionSome(value: Value, label: String): Value = value match {
    case Value.VCtor(head, Vector(result), _) if head.name == "Option.some" => result
    case Value.VCtor(head, Vector(), _) if head.name == "Option.none" =>
      throw new IllegalStateException(s"$label is None")
    case other => throw new IllegalArgumentException(s"Expected Option for $label, got $other")
  }

  def optionIsNone(value: Value): Boolean = value match {
    case Value.VCtor(head, Vector(), _) if head.name == "Option.none"  => true
    case Value.VCtor(head, Vector(_), _) if head.name == "Option.some" => false
    case other => throw new IllegalArgumentException(s"Expected Option, got $other")
  }

  def compileResult(value: Value): CompileResult = value match {
    case Value.VCtor(head, Vector(plan), _) if head.name == "Evaluator.BufferGpuPlan.CompileResult.ready" => Ready(plan)
    case Value.VCtor(head, Vector(code), _) if head.name == "Evaluator.BufferGpuPlan.CompileResult.rejected" =>
      Rejected(natOf(code))
    case other => throw new IllegalArgumentException(s"Unknown BufferGpuPlan CompileResult: $other")
  }

  def readyPlan(value: Value, label: String): Value = compileResult(value) match {
    case Ready(plan)    => plan
    case Rejected(code) => throw new IllegalStateException(s"$label compile rejected with code $code")
  }

  def gpuResult(value: Value): GpuResult = value match {
    case Value.VCtor(head, Vector(outputs, stats), _) if head.name == "Evaluator.BufferGpuPlan.RunResult.success" =>
      GpuSuccess(Success(natList(outputs, "GPU outputs"), decodeStats(stats)))
    case Value.VCtor(head, Vector(error), _) if head.name == "Evaluator.BufferGpuPlan.RunResult.failure" =>
      GpuFailure(decodeRunError(error))
    case other => throw new IllegalArgumentException(s"Unknown BufferGpuPlan RunResult: $other")
  }

  def successful(value: Value, label: String): Success = gpuResult(value) match {
    case GpuSuccess(result) => result
    case GpuFailure(error)  => throw new IllegalStateException(s"$label failed with $error")
  }

  def decodeRunError(value: Value): RunError = value match {
    case Value.VCtor(head, Vector(index), _) if head.name == "Evaluator.BufferGpuPlan.RunError.invalidInput" =>
      val number = natOf(index)
      require(number.isValidInt, s"input index $number does not fit Int")
      InvalidInput(number.toInt)
    case Value.VCtor(head, Vector(code), _) if head.name == "Evaluator.BufferGpuPlan.RunError.bufferFailure" =>
      BufferFailure(natOf(code))
    case Value.VCtor(head, Vector(), _) if head.name == "Evaluator.BufferGpuPlan.RunError.invalidOutput" =>
      InvalidOutput
    case other => UnknownError(other)
  }

  def decodeStats(value: Value): Stats = value match {
    case Value.VCtor(head, fields, _) if head.name == "Evaluator.WarpMachine.Stats.mk" && fields.length == 8 =>
      val values = fields.zipWithIndex.map { case (field, index) => natLong(field, s"Stats field $index") }
      Stats(values(0), values(1), values(2), values(3), values(4), values(5), values(6), values(7))
    case other => throw new IllegalArgumentException(s"Expected WarpMachine.Stats.mk, got $other")
  }

  def prepareInputs(api: Api, seed: Int, natType: Value): Inputs = {
    val prepared =
      optionSome(applyOnStack(api.prepare, api.kernel, packedNat(BigInt(seed), natType)), s"prepare($seed)")
    val (aValue, bValue) = pair(applyOnStack(api.inputs, prepared), s"inputs($seed)")
    val a = natList(aValue, s"A(seed=$seed)")
    val b = natList(bValue, s"B(seed=$seed)")
    require(
      a.length == InputCells && b.length == InputCells,
      s"seed $seed inputs have lengths A=${a.length} B=${b.length}, expected $InputCells each"
    )
    require(a.forall(value => value >= 0 && value < RingModulus), s"seed $seed A contains a value outside Z/257")
    require(b.forall(value => value >= 0 && value < RingModulus), s"seed $seed B contains a value outside Z/257")
    Inputs(prepared, aValue, bValue, a, b)
  }

  /** Independent row-major Z/257 oracle; the source evaluator is not used to produce any expected data. */
  def exactMatmul(a: Vector[Int], b: Vector[Int]): Vector[Int] = {
    require(a.length == InputCells && b.length == InputCells, "oracle input dimensions are invalid")
    val out = Array.ofDim[Int](OutputCells)
    var row = 0
    while (row < Rows) {
      var col = 0
      while (col < Columns) {
        var sum = 0
        var k = 0
        while (k < K) {
          sum = (sum + a(row * K + k) * b(col * K + k)) % RingModulus
          k += 1
        }
        out(row * Columns + col) = sum
        col += 1
      }
      row += 1
    }
    out.toVector
  }

  def rebuildNatListLike(original: Value, values: Vector[BigInt], natType: Value): Value = {
    var current = original
    var consHead: Value.ConstructorHead = null
    var listType: Value = null
    var nilValue: Value = null
    var done = false
    while (!done) {
      current match {
        case Value.VCtor(head, Vector(), _) if head.name == "List.nil" =>
          nilValue = current
          done = true
        case Value.VCtor(head, Vector(_, tail), tpe) if head.name == "List.cons" =>
          if (consHead == null) {
            consHead = head
            listType = tpe
          }
          current = tail
        case other => throw new IllegalArgumentException(s"Expected List(Nat) spine, got $other")
      }
    }
    require(consHead != null || values.isEmpty, "cannot infer List.cons shape from an empty original")
    if (consHead == null) nilValue
    else
      values.reverseIterator.foldLeft(nilValue) { (tail, value) =>
        Value.VCtor(consHead, Vector(packedNat(value, natType), tail), listType)
      }
  }

  def changedInput(original: Value, values: Vector[Int], index: Int, replacement: Int, natType: Value): Value = {
    require(index >= 0 && index < values.length)
    require(replacement >= 0 && replacement < RingModulus)
    val changed = values.updated(index, replacement).map(BigInt(_))
    rebuildNatListLike(original, changed, natType)
  }

  def invalidValueInput(original: Value, values: Vector[Int], index: Int, natType: Value): Value = {
    require(index >= 0 && index < values.length)
    rebuildNatListLike(original, values.updated(index, RingModulus).map(BigInt(_)), natType)
  }

  def u16le(values: Vector[Int]): Vector[Byte] = {
    val bytes = new Array[Byte](values.length * 2)
    var index = 0
    while (index < values.length) {
      val value = values(index)
      require(value >= 0 && value <= RingModulus - 1, s"invalid Z/257 scalar $value")
      bytes(index * 2) = (value & 0xff).toByte
      bytes(index * 2 + 1) = ((value >>> 8) & 0xff).toByte
      index += 1
    }
    bytes.toVector
  }

  def decodeU32le(bytes: Vector[Byte]): Vector[Int] = {
    require(bytes.length % 4 == 0, s"U32 byte length ${bytes.length} is not a multiple of four")
    Vector.tabulate(bytes.length / 4) { index =>
      val at = index * 4
      (bytes(at) & 0xff) | ((bytes(at + 1) & 0xff) << 8) |
        ((bytes(at + 2) & 0xff) << 16) | ((bytes(at + 3) & 0xff) << 24)
    }
  }

  def expectOutputs(actual: Vector[Int], expected: Vector[Int], label: String): Unit = {
    require(actual.length == OutputCells, s"$label produced ${actual.length} outputs, expected $OutputCells")
    require(actual.forall(value => value >= 0 && value < RingModulus), s"$label produced a value outside Z/257")
    val mismatch = expected.indices.find(index => actual(index) != expected(index))
    require(
      mismatch.isEmpty,
      mismatch.fold("")(index =>
        s"$label mismatch at C[${index / Columns},${index % Columns}]: expected ${expected(index)}, got ${actual(index)}"
      )
    )
  }
}
