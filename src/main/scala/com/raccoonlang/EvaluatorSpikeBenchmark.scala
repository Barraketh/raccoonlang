package com.raccoonlang

import java.nio.file.{Path, Paths}

/** Opt-in invocation benchmark for the first evaluator-spike foundation checkpoint. */
object EvaluatorSpikeBenchmark {
  private val StackBytes = 256L << 20
  private val BufferCapacity = 1 << 14
  private val RingModulus = 257
  private val DefaultIterations = 128
  private val MaxIterations = 16384
  private val DefaultWarmups = 1
  private val DefaultSamples = 3

  private final case class Options(iterations: Int, warmups: Int, samples: Int)

  private[raccoonlang] final case class Prepared(value: Value, strings: Option[Value.ValidatedStringLayout])

  def main(args: Array[String]): Unit = {
    val options = parseArgs(args)
    val root = Paths.get(sys.props.getOrElse("raccoon.repoRoot", ".")).toAbsolutePath.normalize
    val gpuRoot = root.resolve("gpu")
    val prelude = Prelude.fromPath(gpuRoot.resolve("Prelude.rac"))

    val tinyStart = System.nanoTime()
    val tiny = Execution.onStack(StackBytes) {
      checkedEntry(gpuRoot.resolve("evaluator/TinyKernel.rac"), gpuRoot, prelude)
    }
    requireTinyKernel(tiny.value)
    val tinyNs = System.nanoTime() - tinyStart

    val workloadStart = System.nanoTime()
    val workload = Execution.onStack(StackBytes) {
      checkedEntry(gpuRoot.resolve("evaluator/BenchmarkEntry.rac"), gpuRoot, prelude)
    }
    val workloadNs = System.nanoTime() - workloadStart

    val natType = prelude.checkedEnv("Nat")
    val argument = Value.VPacked.nat(BigInt(options.iterations), natType)
    val expected = expectedResult(options.iterations)
    val function = workload.value

    println("evaluator_spike=foundation-checkpoint")
    println(s"tiny_checked_kernel_ast=present (load_check_ns=$tinyNs)")
    println(s"benchmark_closure_load_check_ns=$workloadNs")
    println(s"buffer_capacity=$BufferCapacity")
    println(s"iterations=${options.iterations}")
    println(s"buffer_operations_per_iteration=3 (two writes, one read; not warp steps)")
    val operationCount = options.iterations.toLong * 3L
    println(s"total_buffer_operations=$operationCount")

    (0 until options.warmups).foreach { _ =>
      val result = invoke(function, argument)._2
      require(natOf(result) == expected, s"warmup checksum mismatch: expected $expected, got ${natOf(result)}")
    }

    val samples = Vector.tabulate(options.samples) { index =>
      val (elapsedNs, result) = invoke(function, argument)
      val checksum = natOf(result)
      require(checksum == expected, s"sample $index checksum mismatch: expected $expected, got $checksum")
      println(s"sample_${index + 1}_invocation_ns=$elapsedNs")
      elapsedNs
    }
    val sorted = samples.sorted
    val medianNs =
      if (sorted.length % 2 == 1) sorted(sorted.length / 2).toDouble
      else (sorted(sorted.length / 2 - 1).toDouble + sorted(sorted.length / 2).toDouble) / 2.0
    val operationsPerSecond = if (operationCount == 0L) 0.0 else operationCount.toDouble * 1.0e9 / medianNs
    println(s"median_invocation_ns=$medianNs")
    println(f"buffer_operations_per_second=$operationsPerSecond%.2f (not warp steps)")
    println(s"checksum=$expected")
  }

  private def parseArgs(args: Array[String]): Options = {
    var iterations = DefaultIterations
    var warmups = DefaultWarmups
    var samples = DefaultSamples
    var index = 0
    while (index < args.length) {
      val flag = args(index)
      if (index + 1 >= args.length) usage(s"missing value after $flag")
      val value = args(index + 1).toIntOption.getOrElse(usage(s"invalid integer for $flag: ${args(index + 1)}"))
      flag match {
        case "--iterations" => iterations = value
        case "--warmups"    => warmups = value
        case "--samples"    => samples = value
        case other          => usage(s"unknown argument: $other")
      }
      index += 2
    }
    if (iterations < 0 || iterations > MaxIterations)
      usage(s"--iterations must be between 0 and $MaxIterations")
    if (warmups < 0) usage("--warmups must be non-negative")
    if (samples < 1) usage("--samples must be positive")
    Options(iterations, warmups, samples)
  }

  private def usage(message: String): Nothing =
    throw new IllegalArgumentException(
      s"$message\nUsage: EvaluatorSpikeBenchmark [--iterations N] [--warmups N] [--samples N]"
    )

  private[raccoonlang] def checkedEntry(entry: Path, gpuRoot: Path, prelude: Prelude.Config): Prepared = {
    val loaded = ModuleLoader.load(entry, ModuleLoader.LoadConfig(Vector(gpuRoot), prelude))
    val checked = Execution.check(Execution.elaborate(loaded.program, prelude))
    val result = Interpreter.run(checked).getOrElse(throw new IllegalStateException(s"${entry.toString} has no body"))
    Prepared(result, checked.strings)
  }

  private[raccoonlang] def requireTinyKernel(value: Value): Unit =
    value match {
      case Value.VCtor(head, fields, tpe) =>
        require(head.name == "Cuda.Kernel.mk", s"checkedKernel returned ${head.name}, not Cuda.Kernel.mk")
        require(fields.length == 5, s"Cuda.Kernel.mk returned ${fields.length} fields, expected 5")
        require(
          Value.InductiveFamilyValue.unapply(tpe).exists(_.head.name == "Cuda.Kernel"),
          s"checkedKernel application has the wrong result family: $tpe"
        )
      case other => throw new IllegalArgumentException(s"checkedKernel returned no Kernel constructor: $other")
    }

  private[raccoonlang] def invoke(function: Value, argument: Value): (Long, Value) =
    Execution.onStack(StackBytes) {
      val start = System.nanoTime()
      val result = Interpreter.evalApply(function, Vector(argument))
      (System.nanoTime() - start, result)
    }

  private[raccoonlang] def natOf(value: Value): BigInt =
    value match {
      case packed: Value.VPacked => packed.natValue.getOrElse(throw new IllegalArgumentException("Expected packed Nat"))
      case other                 => throw new IllegalArgumentException(s"Expected packed Nat result, got $other")
    }

  /** Independent host reference used only to validate the source workload outside its timed invocation. */
  private[raccoonlang] def expectedResult(iterations: Int): BigInt = {
    val cells = Array.fill(BufferCapacity)(0)
    var checksum = 0
    var iteration = 0
    while (iteration < iterations) {
      val iterationLong = iteration.toLong
      val index = ((iterationLong * 7919L + 101L) % BufferCapacity).toInt
      val priorIteration = iterationLong / 2L
      val probe = ((priorIteration * 7919L + 101L) % BufferCapacity).toInt
      val value = ((iterationLong * 2L) % RingModulus).toInt
      cells(index) = value
      val observed = cells(probe)
      cells(probe) = (observed + value) % RingModulus
      checksum = (checksum + observed) % RingModulus
      iteration += 1
    }
    BigInt((checksum + (iterations.toLong % RingModulus) + (BufferCapacity % RingModulus)) % RingModulus)
  }
}
