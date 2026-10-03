package com.raccoonlang

import java.lang.management.ManagementFactory
import java.nio.file.Paths

/** Opt-in, warmed JVM benchmark for the source-compiled generic Buffer.Program TinyGemm path. */
object BufferGpuSpikeBenchmark {
  private val DefaultWarmups = 2
  private val DefaultSamples = 3
  private val Seeds = Vector(17, 83)

  private final case class Options(warmups: Int, samples: Int)
  private final case class Timed[A](value: A, elapsedNs: Long, allocatedBytes: Option[Long])
  private final case class Measurements(
      run: Vector[Timed[Vector[Int]]],
      source: Vector[Timed[Vector[Int]]],
      vm: Vector[Timed[Vector[Int]]]
  )
  private final case class Work(
      seed: Int,
      prepared: Value,
      aValue: Value,
      bValue: Value,
      a: Vector[Int],
      b: Vector[Int],
      expected: Vector[Int]
  )

  private lazy val allocationBean: Option[com.sun.management.ThreadMXBean] =
    ManagementFactory.getThreadMXBean match {
      case bean: com.sun.management.ThreadMXBean if bean.isThreadAllocatedMemorySupported =>
        try {
          if (!bean.isThreadAllocatedMemoryEnabled) bean.setThreadAllocatedMemoryEnabled(true)
          if (bean.isThreadAllocatedMemoryEnabled) Some(bean) else None
        } catch {
          case _: SecurityException | _: UnsupportedOperationException => None
        }
      case _ => None
    }

  def main(args: Array[String]): Unit = {
    val options = parseArgs(args)
    val repoRoot = Paths.get(sys.props.getOrElse("raccoon.repoRoot", ".")).toAbsolutePath.normalize
    val gpuRoot = repoRoot.resolve("gpu")
    val prelude = Prelude.fromPath(gpuRoot.resolve("Prelude.rac"))

    val loaded = BufferGpuSpikeSupport.loadApi(
      gpuRoot.resolve("evaluator/BufferGpuApi.rac"),
      gpuRoot,
      repoRoot,
      prelude
    )
    val api = loaded.api
    val natType = prelude.checkedEnv("Nat")

    val compileWarmups = Vector.tabulate(options.warmups) { index =>
      val sample = timedEval(api.compile, api.kernel)
      val warmPlan = BufferGpuSpikeSupport.readyPlan(sample.value, s"compile warmup ${index + 1}")
      require(
        BufferGpuSpikeSupport.decodeStats(BufferGpuSpikeSupport.applyOnStack(api.planStats, warmPlan)) ==
          BufferGpuSpikeSupport.CanonicalStats,
        "compile warmup produced unexpected plan counters"
      )
      sample.elapsedNs -> sample.allocatedBytes
    }
    var latestPlan: Option[Value] = None
    val compileSamples = Vector.tabulate(options.samples) { index =>
      val sample = timedEval(api.compile, api.kernel)
      val compiledPlan = BufferGpuSpikeSupport.readyPlan(sample.value, s"compile sample ${index + 1}")
      require(
        BufferGpuSpikeSupport.decodeStats(BufferGpuSpikeSupport.applyOnStack(api.planStats, compiledPlan)) ==
          BufferGpuSpikeSupport.CanonicalStats,
        "compile sample produced unexpected plan counters"
      )
      latestPlan = Some(compiledPlan)
      println(s"compile_sample_${index + 1}_ns=${sample.elapsedNs}")
      println(s"compile_sample_${index + 1}_allocated_bytes=${sample.allocatedBytes.fold("unavailable")(_.toString)}")
      sample.elapsedNs -> sample.allocatedBytes
    }
    val plan = latestPlan.getOrElse(throw new IllegalStateException("no compile sample produced a plan"))
    val genericProgram = BufferGpuSpikeSupport.applyOnStack(api.planProgram, plan)
    val programWordValues = BufferGpuSpikeSupport
      .list(BufferGpuSpikeSupport.applyOnStack(api.programWords, genericProgram), "generic program words")
      .map(BufferGpuSpikeSupport.natOf)
    require(programWordValues.length >= 6, s"Buffer.Program has only ${programWordValues.length} words")
    val programWords = programWordValues
    val instructionCount = programWords(5)
    val bufferCount = programWords(4)
    val nativePrepared = NativeBufferProgram.prepare(programWords) match {
      case Right(prepared) => prepared
      case Left(error) =>
        throw new IllegalStateException(s"generic Buffer.Program preparation failed: ${error.description}")
    }

    require(
      nativePrepared.inputExtents == Vector(BufferGpuSpikeSupport.InputCells * 2, BufferGpuSpikeSupport.InputCells * 2),
      s"generic VM input extents were ${nativePrepared.inputExtents}"
    )
    require(
      nativePrepared.outputByteCount == BufferGpuSpikeSupport.OutputCells.toLong * 4L,
      s"generic VM output byte count was ${nativePrepared.outputByteCount}"
    )

    val works = Seeds.map { seed =>
      val inputs = BufferGpuSpikeSupport.prepareInputs(api, seed, natType)
      Work(
        seed,
        inputs.prepared,
        inputs.aValue,
        inputs.bValue,
        inputs.a,
        inputs.b,
        BufferGpuSpikeSupport.exactMatmul(inputs.a, inputs.b)
      )
    }
    val compiledStats = BufferGpuSpikeSupport.decodeStats(BufferGpuSpikeSupport.applyOnStack(api.planStats, plan))

    println("evaluator_spike=tinygemm-buffer-program")
    println("backend=source-compiled generic Buffer.Program VM")
    println(s"module_load_check_ns=${loaded.elapsedNs}")
    println(s"compile_warmups=${compileWarmups.length}")
    println(s"compile_timed_samples=${compileSamples.length}")
    println(s"warmups=${options.warmups}")
    println(s"timed_samples=${options.samples}")
    println(s"seeds=${Seeds.mkString(",")}")
    println(s"shape=M${BufferGpuSpikeSupport.Rows}-N${BufferGpuSpikeSupport.Columns}-K${BufferGpuSpikeSupport.K}")
    println(s"ring_modulus=${BufferGpuSpikeSupport.RingModulus}")
    println(s"input_cells_per_buffer=${BufferGpuSpikeSupport.InputCells}")
    println(s"input_bytes_per_buffer=${BufferGpuSpikeSupport.InputCells * 2}")
    println(s"generic_program_words=${programWords.length}")
    println(s"generic_program_instructions=$instructionCount")
    println(s"generic_program_buffers=$bufferCount")
    println(s"generic_program_u32_slots=${programWords(2)}")
    println(s"generic_program_u64_slots=${programWords(3)}")
    println(s"output_cells=${BufferGpuSpikeSupport.OutputCells}")
    println(s"allocation_measurement=${if (allocationBean.nonEmpty) "threadMXBean" else "unavailable"}")
    println(
      "timed_boundary_public_run=BufferGpuPlan.run evalApply; includes U16 input conversion, generic program validation/preparation, private buffers, execution and List(Nat) output marshalling"
    )
    println(
      "timed_boundary_source=TinyGemmApi.run plus outputs API evaluation; host decoding/validation is outside timer as for public run"
    )
    println(
      "timed_boundary_prepared_vm=NativeBufferProgram.Prepared.run with U16LE inputs prebuilt; excludes Raccoon conversions and source output marshalling"
    )
    println(
      "worker_creation_join=Execution.onStack worker creation/join outside public/source timed regions; ThreadMXBean sampled inside each executing worker; prepared generic VM runs on the calling thread"
    )
    println(s"plan_warp_steps=${compiledStats.warpSteps}")
    println(s"plan_async_completions=${compiledStats.asyncCompletions}")
    println(s"plan_tma_bytes=${compiledStats.tmaBytes}")
    println(s"plan_scalar_multiplies=${compiledStats.scalarMuls}")
    println(s"plan_scalar_adds=${compiledStats.scalarAdds}")
    println(s"plan_mma_instructions=${compiledStats.mmaInstructions}")
    println(s"plan_tmem_loads=${compiledStats.tmemLoads}")
    println(s"plan_tma_stores=${compiledStats.tmaStores}")
    println(s"compile_warmup_times_ns=${compileWarmups.map(_._1).mkString(",")}")
    println(s"compile_median_ns=${median(compileSamples.map(_._1))}")
    println(s"compile_median_allocated_bytes=${medianAllocated(compileSamples.map(_._2))}")

    works.foreach { work =>
      val nativeInputs = Vector(BufferGpuSpikeSupport.u16le(work.a), BufferGpuSpikeSupport.u16le(work.b))
      val measurements = measureWork(api, plan, nativePrepared, work, nativeInputs, options)
      reportWork(work, measurements)
    }
  }

  private def measureWork(
      api: BufferGpuSpikeSupport.Api,
      plan: Value,
      nativePrepared: NativeBufferProgram.Prepared,
      work: Work,
      nativeInputs: Vector[Vector[Byte]],
      options: Options
  ): Measurements = {
    (0 until options.warmups).foreach { index =>
      val public = timedEval(api.run, plan, work.aValue, work.bValue)
      validatePublic(public.value, work.expected, s"seed ${work.seed} public warmup ${index + 1}")
      val source = timedSource(api, work)
      BufferGpuSpikeSupport.expectOutputs(source.value, work.expected, s"seed ${work.seed} source warmup ${index + 1}")
      val vm = timedVm(nativePrepared, nativeInputs)
      BufferGpuSpikeSupport.expectOutputs(vm.value, work.expected, s"seed ${work.seed} prepared VM warmup ${index + 1}")
    }

    val publicRuns = Vector.tabulate(options.samples) { index =>
      val sample = timedEval(api.run, plan, work.aValue, work.bValue)
      val success = validatePublic(sample.value, work.expected, s"seed ${work.seed} public sample ${index + 1}")
      println(s"seed_${work.seed}_public_run_sample_${index + 1}_ns=${sample.elapsedNs}")
      println(
        s"seed_${work.seed}_public_run_sample_${index + 1}_allocated_bytes=${sample.allocatedBytes.fold("unavailable")(_.toString)}"
      )
      sample.copy(value = success.outputs)
    }
    val sourceRuns = Vector.tabulate(options.samples) { index =>
      val sample = timedSource(api, work)
      BufferGpuSpikeSupport.expectOutputs(sample.value, work.expected, s"seed ${work.seed} source sample ${index + 1}")
      println(s"seed_${work.seed}_source_run_plus_output_sample_${index + 1}_ns=${sample.elapsedNs}")
      println(
        s"seed_${work.seed}_source_run_plus_output_sample_${index + 1}_allocated_bytes=${sample.allocatedBytes.fold("unavailable")(_.toString)}"
      )
      sample
    }
    val vmRuns = Vector.tabulate(options.samples) { index =>
      val sample = timedVm(nativePrepared, nativeInputs)
      BufferGpuSpikeSupport.expectOutputs(
        sample.value,
        work.expected,
        s"seed ${work.seed} prepared VM sample ${index + 1}"
      )
      println(s"seed_${work.seed}_prepared_vm_sample_${index + 1}_ns=${sample.elapsedNs}")
      println(
        s"seed_${work.seed}_prepared_vm_sample_${index + 1}_allocated_bytes=${sample.allocatedBytes.fold("unavailable")(_.toString)}"
      )
      sample
    }
    Measurements(publicRuns, sourceRuns, vmRuns)
  }

  private def timedSource(api: BufferGpuSpikeSupport.Api, work: Work): Timed[Vector[Int]] = {
    val measured = Execution.onStack(BufferGpuSpikeSupport.StackBytes) {
      val allocatedBefore = allocatedBytes()
      val start = System.nanoTime()
      val result = Interpreter.evalApply(api.sourceRun, Vector(work.prepared))
      val outputValue = Interpreter.evalApply(api.sourceOutputs, Vector(result))
      val elapsed = System.nanoTime() - start
      Timed(outputValue, elapsed, delta(allocatedBefore, allocatedBytes()))
    }
    val outputs = BufferGpuSpikeSupport.natList(measured.value, s"source C(seed=${work.seed})")
    Timed(outputs, measured.elapsedNs, measured.allocatedBytes)
  }

  private def timedVm(
      prepared: NativeBufferProgram.Prepared,
      inputs: Vector[Vector[Byte]]
  ): Timed[Vector[Int]] = {
    val allocatedBefore = allocatedBytes()
    val start = System.nanoTime()
    val result = prepared.run(inputs)
    val elapsed = System.nanoTime() - start
    val allocated = delta(allocatedBefore, allocatedBytes())
    if (!result.succeeded) throw new IllegalStateException(s"generic VM failed: ${result.error}")
    require(result.outputs.length == 1, s"generic VM returned ${result.outputs.length} outputs, expected one")
    Timed(BufferGpuSpikeSupport.decodeU32le(result.outputs.head), elapsed, allocated)
  }

  private def timedEval(function: Value, arguments: Value*): Timed[Value] =
    Execution.onStack(BufferGpuSpikeSupport.StackBytes) {
      val allocatedBefore = allocatedBytes()
      val start = System.nanoTime()
      val result = Interpreter.evalApply(function, arguments.toVector)
      val elapsed = System.nanoTime() - start
      Timed(result, elapsed, delta(allocatedBefore, allocatedBytes()))
    }

  private def validatePublic(value: Value, expected: Vector[Int], label: String): BufferGpuSpikeSupport.Success = {
    val result = BufferGpuSpikeSupport.successful(value, label)
    BufferGpuSpikeSupport.expectOutputs(result.outputs, expected, label)
    require(result.stats == BufferGpuSpikeSupport.CanonicalStats, s"$label counters changed: ${result.stats}")
    result
  }

  private def reportWork(work: Work, measurements: Measurements): Unit = {
    def report(phase: String, samples: Vector[Timed[Vector[Int]]]): Unit = {
      println(s"seed_${work.seed}_${phase}_median_ns=${median(samples.map(_.elapsedNs))}")
      println(s"seed_${work.seed}_${phase}_median_allocated_bytes=${medianAllocated(samples.map(_.allocatedBytes))}")
    }
    println(s"seed_${work.seed}_validated_outputs=${work.expected.length}")
    report("public_run", measurements.run)
    report("source_run_plus_output", measurements.source)
    report("prepared_generic_vm", measurements.vm)
  }

  private def allocatedBytes(): Option[Long] = allocationBean.flatMap { bean =>
    try {
      val value = bean.getThreadAllocatedBytes(Thread.currentThread().threadId())
      if (value >= 0L) Some(value) else None
    } catch {
      case _: SecurityException | _: UnsupportedOperationException => None
    }
  }

  private def delta(before: Option[Long], after: Option[Long]): Option[Long] =
    for { start <- before; end <- after if end >= start } yield end - start

  private def median(values: Vector[Long]): Double = {
    val sorted = values.sorted
    if (sorted.length % 2 == 1) sorted(sorted.length / 2).toDouble
    else (sorted(sorted.length / 2 - 1).toDouble + sorted(sorted.length / 2).toDouble) / 2.0
  }

  private def medianAllocated(values: Vector[Option[Long]]): String = {
    val available = values.flatten
    if (available.isEmpty) "unavailable" else median(available).toLong.toString
  }

  private def parseArgs(args: Array[String]): Options = {
    var warmups = DefaultWarmups
    var samples = DefaultSamples
    var index = 0
    while (index < args.length) {
      val flag = args(index)
      if (index + 1 >= args.length) usage(s"missing value after $flag")
      val value = args(index + 1).toIntOption.getOrElse(usage(s"invalid integer for $flag: ${args(index + 1)}"))
      flag match {
        case "--warmups" => warmups = value
        case "--samples" => samples = value
        case other       => usage(s"unknown argument: $other")
      }
      index += 2
    }
    if (warmups < 0) usage("--warmups must be non-negative")
    if (samples < 1) usage("--samples must be positive")
    Options(warmups, samples)
  }

  private def usage(message: String): Nothing =
    throw new IllegalArgumentException(s"$message\nUsage: BufferGpuSpikeBenchmark [--warmups N] [--samples N]")
}
