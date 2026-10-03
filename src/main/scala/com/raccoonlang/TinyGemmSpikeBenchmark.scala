package com.raccoonlang

import java.nio.file.Files
import java.nio.file.Path
import java.nio.file.Paths
import java.lang.management.ManagementFactory

import jdk.jfr.Configuration
import jdk.jfr.Recording

/**
 * Opt-in host driver for the source TinyGEMM evaluator spike. All source setup and result checking are outside the
 * timed `run(prepared)` invocation; the independent oracle consumes the actual prepared A/B arrays.
 */
object TinyGemmSpikeBenchmark {
  private val StackBytes = 256L << 20
  private val M = 128
  private val N = 128
  private val K = 64
  private val RingModulus = 257
  private val ExpectedScalarOpsPerKind = M.toLong * N.toLong * K.toLong
  private val ExpectedWarpSteps = 1251L
  private val ExpectedMmaInstructions = 4L
  private val ExpectedAsyncCompletions = 88L
  private val ExpectedTmaBytes = 98304L
  private val ExpectedTmemLoads = 64L
  private val ExpectedTmaStores = 16L
  private val DefaultWarmups = 1
  private val DefaultSamples = 3
  private val Seeds = Vector(17, 83)

  private final case class Options(
      warmups: Int,
      samples: Int,
      jfrDirectory: Option[Path],
      jfrSettings: Option[Path]
  )
  private final case class Api(
      kernel: Value,
      prepare: Value,
      run: Value,
      inputs: Value,
      outputs: Value,
      stats: Value,
      errors: Value,
      mutantNames: Value,
      runMutant: Value,
      strings: Option[Value.ValidatedStringLayout]
  )
  private final case class InputPair(a: Vector[Int], b: Vector[Int])
  private final case class PhaseTimes(prepareNs: Long, inputExtractionNs: Long, oracleNs: Long)
  private[raccoonlang] final case class Stats(
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
  private[raccoonlang] final case class MutantCheck(name: String, category: String, stats: Stats)
  private final case class Sample(
      elapsedNs: Long,
      outputMaterializationNs: Long,
      allocatedBytes: Option[Long],
      outputAllocationBytes: Option[Long],
      stats: Stats,
      postRunValidationNs: Long,
      profileControlNs: Option[Long],
      profileThread: Option[(String, Long)]
  )
  private final case class Work(
      seed: Int,
      prepared: Value,
      input: InputPair,
      expected: Vector[Int],
      phaseTimes: Option[PhaseTimes]
  )
  private final case class JfrProfile(directory: Path, configuration: Configuration, settingsLoadNs: Long)
  private final case class TimedInvocation(
      elapsedNs: Long,
      result: Value,
      allocatedBytes: Option[Long],
      profileControlNs: Option[Long],
      profileThread: Option[(String, Long)]
  )
  private final case class OutputMaterialization(elapsedNs: Long, allocatedBytes: Option[Long], values: Vector[Int])

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
    require(
      options.jfrDirectory.isDefined == options.jfrSettings.isDefined,
      "--jfr-dir and --jfr-settings must be supplied together"
    )
    val profile = for {
      directory <- options.jfrDirectory
      settingsPath <- options.jfrSettings
    } yield {
      require(options.samples == 1, "JFR profiling expects exactly one timed sample per seed")
      require(options.warmups >= 2, "JFR profiling expects at least two warmups per seed")
      require(Files.isRegularFile(settingsPath), s"JFR settings file does not exist: $settingsPath")
      Files.createDirectories(directory)
      val settingsStart = System.nanoTime()
      val configuration = Configuration.create(settingsPath)
      JfrProfile(directory, configuration, System.nanoTime() - settingsStart)
    }
    val root = Paths.get(sys.props.getOrElse("raccoon.repoRoot", ".")).toAbsolutePath.normalize
    val gpuRoot = root.resolve("gpu")
    val preludeStart = System.nanoTime()
    val prelude = Prelude.fromPath(gpuRoot.resolve("Prelude.rac"))
    val preludeLoadNs = System.nanoTime() - preludeStart

    val setupStart = System.nanoTime()
    val entry = Execution.onStack(StackBytes) {
      EvaluatorSpikeBenchmark.checkedEntry(gpuRoot.resolve("evaluator/TinyGemmApi.rac"), gpuRoot, prelude)
    }
    val api = decodeApi(entry.value, entry.strings)
    EvaluatorSpikeBenchmark.requireTinyKernel(api.kernel)
    val apiLoadNs = System.nanoTime() - setupStart

    val natType = prelude.checkedEnv("Nat")
    val works = prepareWorks(api, natType, Seeds, measurePhases = true)

    val mmaCount = ExpectedScalarOpsPerKind
    println("evaluator_spike=tinygemm-z257")
    println("backend=source")
    println(s"prelude_config_load_ns=$preludeLoadNs")
    println(s"source_api_load_check_ns=$apiLoadNs")
    println(s"shape=M$M-N$N-K$K")
    println(s"ring_modulus=$RingModulus")
    println(s"seeds=${Seeds.mkString(",")}")
    println(s"expected_scalar_multiplies=$mmaCount")
    println(s"expected_scalar_adds=$mmaCount")
    println(s"warmups=${options.warmups}")
    println(s"timed_samples=${options.samples}")
    println(s"allocation_measurement=${if (allocationBean.nonEmpty) "threadMXBean" else "unavailable"}")
    println(
      "timed_region=Interpreter.evalApply(run, Vector(prepared)); includes one-element argument-vector construction"
    )
    println(
      "matched_boundary=source run plus output API evaluation/list decoding, measured as separate worker-thread regions"
    )
    profile.foreach { jfr =>
      println(s"jfr_settings_load_ns=${jfr.settingsLoadNs}")
      println(s"jfr_settings=${options.jfrSettings.get.toAbsolutePath.normalize}")
      println(s"jfr_profile_directory=${jfr.directory.toAbsolutePath.normalize}")
      println("jfr_recording_region=per-seed reported timed region only; recording control remains outside timer")
    }

    works.foreach { work =>
      work.phaseTimes.foreach { phases =>
        println(s"seed_${work.seed}_prepare_ns=${phases.prepareNs}")
        println(s"seed_${work.seed}_input_extraction_ns=${phases.inputExtractionNs}")
        println(s"seed_${work.seed}_host_oracle_ns=${phases.oracleNs}")
      }
      var firstStats: Option[Stats] = None

      def checkedRun(phase: String, recordTo: Option[Path] = None): Sample = {
        val runProfile = recordTo.flatMap(path => profile.map(jfr => jfr.configuration -> path))
        val invocation = timedRun(api.run, work.prepared, runProfile)
        val validationStart = if (profile.nonEmpty) System.nanoTime() else 0L
        val result = invocation.result
        val stats = decodeStats(applyOnStack(api.stats, result))
        val output = timedOutputMaterialization(api.outputs, result, work.seed, phase)
        validateSuccess(api, result, stats, output.values, work.expected, work.seed, phase)
        val validationNs = if (profile.nonEmpty) System.nanoTime() - validationStart else 0L
        firstStats match {
          case Some(reference) =>
            require(
              stats == reference,
              s"seed=${work.seed} $phase counters changed when reusing Prepared: $reference vs $stats"
            )
          case None => firstStats = Some(stats)
        }
        Sample(
          invocation.elapsedNs,
          output.elapsedNs,
          invocation.allocatedBytes,
          output.allocatedBytes,
          stats,
          validationNs,
          invocation.profileControlNs,
          invocation.profileThread
        )
      }

      (0 until options.warmups).foreach { index =>
        val warmupStart = if (profile.nonEmpty) System.nanoTime() else 0L
        val warmup = checkedRun("warmup")
        if (profile.nonEmpty) {
          println(s"seed_${work.seed}_warmup_${index + 1}_eval_ns=${warmup.elapsedNs}")
          println(s"seed_${work.seed}_warmup_${index + 1}_post_run_validation_ns=${warmup.postRunValidationNs}")
          println(s"seed_${work.seed}_warmup_${index + 1}_phase_wall_ns=${System.nanoTime() - warmupStart}")
        }
      }

      val samples = Vector.tabulate(options.samples) { index =>
        val recordTo = profile.map(_.directory.resolve(s"tinygemm-seed-${work.seed}-sample-${index + 1}.jfr"))
        val sample = checkedRun(s"sample ${index + 1}", recordTo)
        println(s"seed_${work.seed}_sample_${index + 1}_invocation_ns=${sample.elapsedNs}")
        println(s"seed_${work.seed}_sample_${index + 1}_output_materialization_ns=${sample.outputMaterializationNs}")
        println(
          s"seed_${work.seed}_sample_${index + 1}_run_plus_output_ns=${sample.elapsedNs + sample.outputMaterializationNs}"
        )
        println(
          s"seed_${work.seed}_sample_${index + 1}_run_allocated_bytes=${sample.allocatedBytes.fold("unavailable")(_.toString)}"
        )
        sample.outputAllocationBytes.foreach(bytes =>
          println(s"seed_${work.seed}_sample_${index + 1}_output_allocated_bytes=$bytes")
        )
        if (profile.nonEmpty) {
          println(s"seed_${work.seed}_sample_${index + 1}_post_run_validation_ns=${sample.postRunValidationNs}")
          println(
            s"seed_${work.seed}_sample_${index + 1}_profile_control_outside_timer_ns=${sample.profileControlNs.getOrElse(0L)}"
          )
          sample.profileThread.foreach { case (name, id) =>
            println(s"seed_${work.seed}_sample_${index + 1}_jfr_run_thread_name=$name")
            println(s"seed_${work.seed}_sample_${index + 1}_jfr_run_thread_id=$id")
          }
          println(s"seed_${work.seed}_sample_${index + 1}_jfr_path=${recordTo.get.toAbsolutePath.normalize}")
        }
        sample
      }

      val sortedSamples = samples.sortBy(_.elapsedNs)
      val medianNs = median(sortedSamples.map(_.elapsedNs))
      val matchedMedianNs = median(samples.map(sample => sample.elapsedNs + sample.outputMaterializationNs))
      val representativeStats = sortedSamples(sortedSamples.length / 2).stats
      val warpStepsPerSecond = rate(representativeStats.warpSteps, medianNs)
      val scalarOpsPerSecond = rate(representativeStats.scalarOps, medianNs)
      val tenMillionStepNs =
        if (warpStepsPerSecond == 0.0) Double.PositiveInfinity else 1.0e7 * 1.0e9 / warpStepsPerSecond

      println(s"seed_${work.seed}_checked_outputs=${work.expected.length}")
      println(s"seed_${work.seed}_coverage=16384_of_16384_no_257_sentinel")
      println(s"seed_${work.seed}_median_invocation_ns=$medianNs")
      println(s"seed_${work.seed}_median_run_plus_output_ns=$matchedMedianNs")
      println(s"seed_${work.seed}_warp_steps=${representativeStats.warpSteps}")
      println(s"seed_${work.seed}_async_event_completions=${representativeStats.asyncCompletions}")
      println(s"seed_${work.seed}_tma_bytes=${representativeStats.tmaBytes}")
      println(s"seed_${work.seed}_scalar_muls=${representativeStats.scalarMuls}")
      println(s"seed_${work.seed}_scalar_adds=${representativeStats.scalarAdds}")
      println(s"seed_${work.seed}_mma_instructions=${representativeStats.mmaInstructions}")
      println(s"seed_${work.seed}_tmem_loads=${representativeStats.tmemLoads}")
      println(s"seed_${work.seed}_tma_stores=${representativeStats.tmaStores}")
      println(f"seed_${work.seed}_warp_steps_per_second=$warpStepsPerSecond%.2f")
      println(f"seed_${work.seed}_scalar_ops_per_second=$scalarOpsPerSecond%.2f")
      println(
        f"seed_${work.seed}_ten_million_step_extrapolation_seconds=${tenMillionStepNs / 1.0e9}%.3f (MMA-heavy mix)"
      )
    }

    println("scope_caveat=TinyGEMM MMA-heavy exact-ring spike; not FP, broad hardware, or v0 race-coverage evidence")
  }

  private def timedOutputMaterialization(
      outputs: Value,
      result: Value,
      seed: Int,
      phase: String
  ): OutputMaterialization = Execution.onStack(StackBytes) {
    val allocatedBefore = threadAllocatedBytes()
    val start = System.nanoTime()
    val outputValue = Interpreter.evalApply(outputs, Vector(result))
    val values = decodeNatList(outputValue, s"C(seed=$seed,$phase)")
    val elapsed = System.nanoTime() - start
    val allocatedAfter = threadAllocatedBytes()
    OutputMaterialization(elapsed, allocatedDelta(allocatedBefore, allocatedAfter), values)
  }

  private def threadAllocatedBytes(): Option[Long] = allocationBean.flatMap { bean =>
    try {
      val value = bean.getThreadAllocatedBytes(Thread.currentThread().threadId())
      if (value >= 0L) Some(value) else None
    } catch {
      case _: SecurityException | _: UnsupportedOperationException => None
    }
  }

  private def allocatedDelta(before: Option[Long], after: Option[Long]): Option[Long] =
    for {
      start <- before
      end <- after if end >= start
    } yield end - start

  private def parseArgs(args: Array[String]): Options = {
    var warmups = DefaultWarmups
    var samples = DefaultSamples
    var jfrDirectory: Option[Path] = None
    var jfrSettings: Option[Path] = None
    var index = 0
    while (index < args.length) {
      val flag = args(index)
      if (index + 1 >= args.length) usage(s"missing value after $flag")
      flag match {
        case "--warmups" | "--samples" =>
          val value = args(index + 1).toIntOption.getOrElse(usage(s"invalid integer for $flag: ${args(index + 1)}"))
          if (flag == "--warmups") warmups = value else samples = value
        case "--jfr-dir"      => jfrDirectory = Some(Paths.get(args(index + 1)).toAbsolutePath.normalize)
        case "--jfr-settings" => jfrSettings = Some(Paths.get(args(index + 1)).toAbsolutePath.normalize)
        case other            => usage(s"unknown argument: $other")
      }
      index += 2
    }
    if (warmups < 0) usage("--warmups must be non-negative")
    if (samples < 1) usage("--samples must be positive")
    Options(warmups, samples, jfrDirectory, jfrSettings)
  }

  private def usage(message: String): Nothing =
    throw new IllegalArgumentException(
      s"$message\nUsage: TinyGemmSpikeBenchmark [--warmups N] [--samples N] [--jfr-dir DIR --jfr-settings FILE]"
    )

  private def decodeApi(value: Value, strings: Option[Value.ValidatedStringLayout]): Api = {
    val (kernel, rest0) = pair(value, "TinyGemmApi")
    val (prepare, rest1) = pair(rest0, "TinyGemmApi function bundle")
    val (run, rest2) = pair(rest1, "TinyGemmApi function bundle")
    val (inputs, rest3) = pair(rest2, "TinyGemmApi function bundle")
    val (outputs, rest4) = pair(rest3, "TinyGemmApi function bundle")
    val (stats, rest5) = pair(rest4, "TinyGemmApi function bundle")
    val (errors, rest6) = pair(rest5, "TinyGemmApi function bundle")
    val (mutantNames, runMutant) = pair(rest6, "TinyGemmApi malformed-case bundle")
    Api(kernel, prepare, run, inputs, outputs, stats, errors, mutantNames, runMutant, strings)
  }

  private def pair(value: Value, label: String): (Value, Value) =
    value match {
      case Value.VCtor(head, fields, _) if head.name == "Pair.mk" && fields.length == 2 => (fields(0), fields(1))
      case other => throw new IllegalArgumentException(s"Expected Pair.mk for $label, got $other")
    }

  private def optionSome(value: Value, label: String): Value =
    value match {
      case Value.VCtor(head, fields, _) if head.name == "Option.some" && fields.length == 1 => fields.head
      case Value.VCtor(head, _, _) if head.name == "Option.none" =>
        throw new IllegalStateException(s"$label returned None")
      case other => throw new IllegalArgumentException(s"Expected Option result for $label, got $other")
    }

  private def decodePair(value: Value, label: String): (Value, Value) = pair(value, label)

  private def prepareWorks(api: Api, natType: Value, seeds: Vector[Int], measurePhases: Boolean): Vector[Work] = {
    val works = seeds.map { seed =>
      val prepareStart = if (measurePhases) System.nanoTime() else 0L
      val preparedOption = applyOnStack(api.prepare, api.kernel, Value.VPacked.nat(BigInt(seed), natType))
      val prepared = optionSome(preparedOption, s"prepare(seed=$seed)")
      val prepareNs = if (measurePhases) System.nanoTime() - prepareStart else 0L
      val inputExtractionStart = if (measurePhases) System.nanoTime() else 0L
      val (aValues, bValues) = decodePair(applyOnStack(api.inputs, prepared), s"inputs(seed=$seed)")
      val a = decodeNatList(aValues, s"A(seed=$seed)")
      val b = decodeNatList(bValues, s"B(seed=$seed)")
      require(a.length == M * K, s"A(seed=$seed) has ${a.length} values, expected ${M * K}")
      require(b.length == N * K, s"B(seed=$seed) has ${b.length} values, expected ${N * K}")
      require(a.forall(x => x >= 0 && x < RingModulus), s"A(seed=$seed) contains a value outside Z/$RingModulus")
      require(b.forall(x => x >= 0 && x < RingModulus), s"B(seed=$seed) contains a value outside Z/$RingModulus")
      requireCoordinateDependent("A", seed, a)
      requireCoordinateDependent("B", seed, b)
      val inputExtractionNs = if (measurePhases) System.nanoTime() - inputExtractionStart else 0L
      val input = InputPair(a, b)
      val oracleStart = if (measurePhases) System.nanoTime() else 0L
      val expected = exactMatmul(input)
      val oracleNs = if (measurePhases) System.nanoTime() - oracleStart else 0L
      val phaseTimes = if (measurePhases) Some(PhaseTimes(prepareNs, inputExtractionNs, oracleNs)) else None
      Work(seed, prepared, input, expected, phaseTimes)
    }
    require(works.map(_.seed).distinct.length >= 2, "TinyGEMM spike requires at least two distinct input seeds")
    require(works.map(_.input.a).distinct.length == works.length, "different seeds produced identical A inputs")
    require(works.map(_.input.b).distinct.length == works.length, "different seeds produced identical B inputs")
    require(works.map(_.expected).distinct.length == works.length, "different seeds produced identical output matrices")

    val oracleTransposeDisagreements = works.map { work =>
      work.expected.indices.count { index =>
        val row = index / N
        val col = index % N
        work.expected(index) != work.expected(col * N + row)
      }
    }
    require(oracleTransposeDisagreements.forall(_ > 0), "seed fixtures did not produce an asymmetric C matrix")
    works
  }

  /** Compare each checked source result with the independent oracle, then reuse the prepared input. */
  private[raccoonlang] def verifySeeds(
      gpuRoot: java.nio.file.Path,
      prelude: Prelude.Config,
      seeds: Vector[Int]
  ): Vector[Stats] = {
    val entry = Execution.onStack(StackBytes) {
      EvaluatorSpikeBenchmark.checkedEntry(gpuRoot.resolve("evaluator/TinyGemmApi.rac"), gpuRoot, prelude)
    }
    val api = decodeApi(entry.value, entry.strings)
    EvaluatorSpikeBenchmark.requireTinyKernel(api.kernel)
    val natType = prelude.checkedEnv("Nat")
    prepareWorks(api, natType, seeds, measurePhases = false).map { work =>
      def runOnce(phase: String): Stats = {
        val result = applyOnStack(api.run, work.prepared)
        val stats = decodeStats(applyOnStack(api.stats, result))
        val outputs = decodeNatList(applyOnStack(api.outputs, result), s"C(seed=${work.seed},$phase)")
        validateSuccess(api, result, stats, outputs, work.expected, work.seed, phase)
        stats
      }
      val first = runOnce("integration test first run")
      val second = runOnce("integration test prepared reuse")
      require(first == second, s"seed=${work.seed} counters changed when reusing Prepared: $first vs $second")
      first
    }
  }

  /**
   * Exercise source-owned malformed ASTs through WarpMachine and compare complete output with the independent oracle.
   */
  private[raccoonlang] def verifyMutants(
      gpuRoot: java.nio.file.Path,
      prelude: Prelude.Config
  ): Vector[MutantCheck] = {
    val entry = Execution.onStack(StackBytes) {
      EvaluatorSpikeBenchmark.checkedEntry(gpuRoot.resolve("evaluator/TinyGemmApi.rac"), gpuRoot, prelude)
    }
    val api = decodeApi(entry.value, entry.strings)
    EvaluatorSpikeBenchmark.requireTinyKernel(api.kernel)
    val namedMutants = decodeStringList(api.mutantNames, api.strings)
    val expectedCategories = Vector(
      "wrong-k-slice" -> "complete-mismatch",
      "descriptor" -> "device-fault",
      "output-offset" -> "device-fault",
      "out-of-bounds" -> "device-fault",
      "partial-aligned" -> "invalid-state",
      "partial-wait" -> "invalid-state",
      "unsupported" -> "unsupported",
      "unsupported-regpool" -> "unsupported",
      "missing-commit" -> "deadlocked",
      "missing-tma-completion" -> "deadlocked",
      "fuel" -> "fuel-exhausted",
      "not-quiescent" -> "not-quiescent",
      "overlapping-tmem-load" -> "complete-match"
    )
    require(
      namedMutants
        .map(_._1)
        .toSet == expectedCategories.map(_._1).toSet && namedMutants.length == expectedCategories.length,
      s"TinyGemmApi malformed-case names differed: ${namedMutants.map(_._1).mkString(",")}"
    )
    val expectedByName = expectedCategories.toMap
    val natType = prelude.checkedEnv("Nat")
    val generousFuel = Value.VPacked.nat(BigInt(10000000), natType)
    val oracleSeed = 17
    val oraclePrepared = optionSome(
      applyOnStack(api.prepare, api.kernel, Value.VPacked.nat(BigInt(oracleSeed), natType)),
      s"prepare(seed=$oracleSeed) for valid K-slice mutant"
    )
    val (oracleA, oracleB) = decodePair(applyOnStack(api.inputs, oraclePrepared), s"inputs(seed=$oracleSeed)")
    val oracleInput = InputPair(
      decodeNatList(oracleA, s"A(seed=$oracleSeed)"),
      decodeNatList(oracleB, s"B(seed=$oracleSeed)")
    )
    require(
      oracleInput.a.length == M * K && oracleInput.b.length == N * K,
      "seed-17 mutant oracle inputs had wrong lengths"
    )
    require(oracleInput.a.forall(x => x >= 0 && x < RingModulus), "seed-17 mutant oracle A is outside Z/257")
    require(oracleInput.b.forall(x => x >= 0 && x < RingModulus), "seed-17 mutant oracle B is outside Z/257")
    requireCoordinateDependent("A", oracleSeed, oracleInput.a)
    requireCoordinateDependent("B", oracleSeed, oracleInput.b)
    val expectedOracle = exactMatmul(oracleInput)
    namedMutants.map { case (name, sourceName) =>
      val fuel = if (name == "fuel") Value.VPacked.nat(BigInt(1), natType) else generousFuel
      val result = applyOnStack(api.runMutant, sourceName, fuel)
      result match {
        case Value.VCtor(head, _, _) if head.name == "Evaluator.WarpMachine.MachineResult.complete" =>
          require(
            name == "wrong-k-slice" || name == "overlapping-tmem-load",
            s"mutant $name unexpectedly completed"
          )
          val values = decodeNatList(applyOnStack(api.outputs, result), s"mutant $name outputs")
          require(values.length == M * N, s"mutant $name produced ${values.length} outputs, expected ${M * N}")
          require(
            values.forall(x => x >= 0 && x < RingModulus),
            s"mutant $name produced a value outside Z/$RingModulus"
          )
          require(!values.contains(RingModulus), s"mutant $name retained output sentinel $RingModulus")
          val sourceMatchesOracle = name == "overlapping-tmem-load"
          if (sourceMatchesOracle) {
            require(
              values == expectedOracle,
              "source appendRegisterWrites ordering did not preserve the earlier overlapping TMEM load"
            )
            val adjacentValuesDiffer = (0 until M).exists(row =>
              (0 until 8).exists(column => expectedOracle(row * N + column) != expectedOracle(row * N + column + 8))
            )
            require(
              adjacentValuesDiffer,
              "overlapping-load fixture did not select visibly different adjacent TMEM columns"
            )
          } else {
            require(
              values != expectedOracle,
              "valid K-slice mutant unexpectedly matched the seed-17 independent oracle"
            )
          }
          val counts = decodeStats(applyOnStack(api.stats, result))
          val extraLoads = if (sourceMatchesOracle) 16L else 0L
          require(
            counts.warpSteps == ExpectedWarpSteps + extraLoads,
            s"mutant $name counted ${counts.warpSteps} warp statements, expected ${ExpectedWarpSteps + extraLoads}"
          )
          require(
            counts.asyncCompletions == ExpectedAsyncCompletions + extraLoads,
            s"mutant $name completed ${counts.asyncCompletions} events, expected ${ExpectedAsyncCompletions + extraLoads}"
          )
          require(counts.tmaBytes == ExpectedTmaBytes, "valid K-slice mutant transferred an unexpected byte count")
          require(
            counts.scalarMuls == ExpectedScalarOpsPerKind,
            "valid K-slice mutant counted an unexpected multiply count"
          )
          require(counts.scalarAdds == ExpectedScalarOpsPerKind, "valid K-slice mutant counted an unexpected add count")
          require(
            counts.mmaInstructions == ExpectedMmaInstructions,
            "valid K-slice mutant completed an unexpected MMA count"
          )
          require(
            counts.tmemLoads == ExpectedTmemLoads + extraLoads,
            s"mutant $name counted ${counts.tmemLoads} tensor-memory loads, expected ${ExpectedTmemLoads + extraLoads}"
          )
          require(counts.tmaStores == ExpectedTmaStores, "valid K-slice mutant counted an unexpected TMA store count")
          MutantCheck(name, if (sourceMatchesOracle) "complete-match" else "complete-mismatch", counts)
        case Value.VCtor(head, _, _) if head.name == "Evaluator.WarpMachine.MachineResult.failed" =>
          require(
            name != "wrong-k-slice",
            s"valid K-slice mutant failed: ${render(applyOnStack(api.errors, result), api.strings)}"
          )
          val category = render(applyOnStack(api.errors, result), api.strings)
          val expectedCategory = expectedByName(name)
          require(
            category.startsWith(expectedCategory),
            s"mutant $name reported '$category', expected category '$expectedCategory'"
          )
          if (name == "partial-wait") {
            require(
              category.contains("tcgen05.wait::ld") && category.contains("all 32 lanes") && category.contains(
                "participate"
              ),
              s"partial-wait failed before the aligned full-participation guard: '$category'"
            )
          }
          if (name == "unsupported-regpool") {
            require(
              category.contains("setmaxnreg register-pool behavior is not modeled"),
              s"unsupported-regpool did not report the unmodeled register-pool behavior: '$category'"
            )
          }
          val counts = decodeStats(applyOnStack(api.stats, result))
          if (name == "missing-tma-completion") {
            require(
              counts.asyncCompletions < ExpectedAsyncCompletions,
              s"missing-TMA-completion retired ${counts.asyncCompletions} events, expected fewer than $ExpectedAsyncCompletions"
            )
            require(
              counts.tmaBytes < ExpectedTmaBytes,
              s"missing-TMA-completion transferred ${counts.tmaBytes} bytes, expected fewer than $ExpectedTmaBytes"
            )
            require(
              counts.mmaInstructions == 0L,
              s"missing-TMA-completion reached ${counts.mmaInstructions} MMA instructions before failing"
            )
          }
          require(
            decodeNatList(applyOnStack(api.outputs, result), s"mutant $name outputs").isEmpty,
            s"failed mutant $name exposed output values"
          )
          MutantCheck(name, expectedCategory, counts)
        case other =>
          throw new IllegalArgumentException(s"mutant $name returned an unknown result: ${render(other, api.strings)}")
      }
    }
  }

  private def decodeNatList(value: Value, label: String): Vector[Int] = {
    val result = Vector.newBuilder[Int]
    var current = value
    var index = 0
    var done = false
    while (!done) {
      current match {
        case Value.VCtor(head, fields, _) if head.name == "List.nil" && fields.isEmpty => done = true
        case Value.VCtor(head, fields, _) if head.name == "List.cons" && fields.length == 2 =>
          val n = EvaluatorSpikeBenchmark.natOf(fields(0))
          require(n.isValidInt, s"$label[$index]=$n does not fit an Int")
          result += n.toInt
          current = fields(1)
          index += 1
        case other => throw new IllegalArgumentException(s"Malformed $label list at index $index: $other")
      }
    }
    result.result()
  }

  private def decodeStringList(
      value: Value,
      strings: Option[Value.ValidatedStringLayout]
  ): Vector[(String, Value)] = {
    val result = Vector.newBuilder[(String, Value)]
    var current = value
    var index = 0
    var done = false
    while (!done) {
      current match {
        case Value.VCtor(head, fields, _) if head.name == "List.nil" && fields.isEmpty => done = true
        case Value.VCtor(head, fields, _) if head.name == "List.cons" && fields.length == 2 =>
          val text = PrettyPrinter
            .rawString(fields(0), strings)
            .getOrElse(
              throw new IllegalArgumentException(s"Malformed source String in mutantNames[$index]")
            )
          result += ((text, fields(0)))
          current = fields(1)
          index += 1
        case other => throw new IllegalArgumentException(s"Malformed mutantNames list at index $index: $other")
      }
    }
    result.result()
  }

  private def decodeStats(value: Value): Stats =
    value match {
      case Value.VCtor(head, fields, _) if head.name == "Evaluator.WarpMachine.Stats.mk" && fields.length == 8 =>
        val values = fields.zipWithIndex.map { case (field, i) => natLong(field, s"Stats field $i") }
        Stats(values(0), values(1), values(2), values(3), values(4), values(5), values(6), values(7))
      case other => throw new IllegalArgumentException(s"Expected eight-field Stats.mk, got $other")
    }

  private def natLong(value: Value, label: String): Long = {
    val number = EvaluatorSpikeBenchmark.natOf(value)
    require(number.isValidLong, s"$label=$number does not fit a Long")
    number.toLong
  }

  private def applyOnStack(function: Value, arguments: Value*): Value =
    Execution.onStack(StackBytes) { Interpreter.evalApply(function, arguments.toVector) }

  private def timedRun(
      run: Value,
      prepared: Value,
      profile: Option[(Configuration, Path)]
  ): TimedInvocation =
    Execution.onStack(StackBytes) {
      profile match {
        case None =>
          val allocatedBefore = threadAllocatedBytes()
          val start = System.nanoTime()
          val result = Interpreter.evalApply(run, Vector(prepared))
          val elapsed = System.nanoTime() - start
          val allocatedAfter = threadAllocatedBytes()
          TimedInvocation(elapsed, result, allocatedDelta(allocatedBefore, allocatedAfter), None, None)
        case Some((configuration, path)) =>
          val recording = new Recording(configuration)
          recording.setName(path.getFileName.toString)
          recording.setToDisk(true)
          val controlStart = System.nanoTime()
          try recording.start()
          catch {
            case startFailure: Throwable =>
              try recording.close()
              catch { case closeFailure: Throwable => startFailure.addSuppressed(closeFailure) }
              throw startFailure
          }
          val recordingStarted = System.nanoTime()
          val runThread = Thread.currentThread()
          val runThreadIdentity = (runThread.getName, runThread.threadId())
          val allocatedBefore = threadAllocatedBytes()
          val runStart = System.nanoTime()
          var result: Value = null
          var runFailure: Throwable = null
          try result = Interpreter.evalApply(run, Vector(prepared))
          catch { case thrown: Throwable => runFailure = thrown }
          val elapsedNs = System.nanoTime() - runStart
          val allocatedAfter = threadAllocatedBytes()
          val allocated = allocatedDelta(allocatedBefore, allocatedAfter)
          val runEnd = System.nanoTime()
          var recordingFailure: Throwable = null
          try {
            recording.stop()
            recording.dump(path)
          } catch { case thrown: Throwable => recordingFailure = thrown }
          finally recording.close()
          val controlNs = (recordingStarted - controlStart) + (System.nanoTime() - runEnd)
          if (runFailure != null) {
            if (recordingFailure != null) runFailure.addSuppressed(recordingFailure)
            throw runFailure
          }
          if (recordingFailure != null) throw recordingFailure
          TimedInvocation(elapsedNs, result, allocated, Some(controlNs), Some(runThreadIdentity))
      }
    }

  private def validateSuccess(
      api: Api,
      result: Value,
      stats: Stats,
      values: Vector[Int],
      expected: Vector[Int],
      seed: Int,
      phase: String
  ): Unit = {
    result match {
      case Value.VCtor(head, _, _) if head.name == "Evaluator.WarpMachine.MachineResult.complete" =>
      case Value.VCtor(head, _, _) if head.name == "Evaluator.WarpMachine.MachineResult.failed" =>
        val diagnostic = render(applyOnStack(api.errors, result), api.strings)
        val failedStats = decodeStats(applyOnStack(api.stats, result))
        throw new IllegalStateException(s"seed=$seed $phase failed: $diagnostic; counters=$failedStats")
      case other =>
        throw new IllegalArgumentException(
          s"seed=$seed $phase returned unknown MachineResult: ${render(other, api.strings)}"
        )
    }

    require(values.length == M * N, s"seed=$seed $phase produced ${values.length} outputs, expected ${M * N}")
    require(values.forall(x => x >= 0 && x < RingModulus), s"seed=$seed $phase produced a value outside Z/$RingModulus")
    require(!values.contains(RingModulus), s"seed=$seed $phase retained the uninitialized output sentinel $RingModulus")
    val mismatch = expected.indices.find(i => values(i) != expected(i))
    require(
      mismatch.isEmpty,
      mismatch.fold("")(i =>
        s"seed=$seed $phase C[${i / N},${i % N}] mismatch: expected ${expected(i)}, got ${values(i)}"
      )
    )
    require(
      stats.scalarMuls == ExpectedScalarOpsPerKind,
      s"seed=$seed $phase counted ${stats.scalarMuls} multiplies, expected $ExpectedScalarOpsPerKind"
    )
    require(
      stats.scalarAdds == ExpectedScalarOpsPerKind,
      s"seed=$seed $phase counted ${stats.scalarAdds} adds, expected $ExpectedScalarOpsPerKind"
    )
    require(
      stats.mmaInstructions == ExpectedMmaInstructions,
      s"seed=$seed $phase completed ${stats.mmaInstructions} MMA requests, expected $ExpectedMmaInstructions"
    )
    require(
      stats.warpSteps == ExpectedWarpSteps,
      s"seed=$seed $phase counted ${stats.warpSteps} executed warp statements, expected $ExpectedWarpSteps"
    )
    require(
      stats.asyncCompletions == ExpectedAsyncCompletions,
      s"seed=$seed $phase counted ${stats.asyncCompletions} async completions, expected $ExpectedAsyncCompletions"
    )
    require(
      stats.tmaBytes == ExpectedTmaBytes,
      s"seed=$seed $phase transferred ${stats.tmaBytes} TMA bytes, expected $ExpectedTmaBytes"
    )
    require(
      stats.tmemLoads == ExpectedTmemLoads,
      s"seed=$seed $phase counted ${stats.tmemLoads} tensor-memory loads, expected $ExpectedTmemLoads"
    )
    require(
      stats.tmaStores == ExpectedTmaStores,
      s"seed=$seed $phase counted ${stats.tmaStores} TMA stores, expected $ExpectedTmaStores"
    )
  }

  private def requireCoordinateDependent(kind: String, seed: Int, values: Vector[Int]): Unit = {
    val row0 = values.take(K)
    val row1 = values.slice(K, 2 * K)
    require(row0.distinct.length > 1, s"$kind(seed=$seed) does not vary along K")
    require(row0 != row1, s"$kind(seed=$seed) does not vary by row")
  }

  /** Independent host-only exact Z/257 matrix multiplication over row-major source inputs. */
  private def exactMatmul(input: InputPair): Vector[Int] = {
    val output = Array.ofDim[Int](M * N)
    var row = 0
    while (row < M) {
      var col = 0
      while (col < N) {
        var sum = 0
        var k = 0
        while (k < K) {
          sum = (sum + input.a(row * K + k) * input.b(col * K + k)) % RingModulus
          k += 1
        }
        output(row * N + col) = sum
        col += 1
      }
      row += 1
    }
    output.toVector
  }

  private def median(values: Vector[Long]): Double = {
    val sorted = values.sorted
    if (sorted.length % 2 == 1) sorted(sorted.length / 2).toDouble
    else (sorted(sorted.length / 2 - 1).toDouble + sorted(sorted.length / 2).toDouble) / 2.0
  }

  private def rate(count: Long, elapsedNs: Double): Double =
    if (count == 0L || elapsedNs <= 0.0) 0.0 else count.toDouble * 1.0e9 / elapsedNs

  private def render(value: Value, strings: Option[Value.ValidatedStringLayout]): String =
    PrettyPrinter.rawString(value, strings).getOrElse(PrettyPrinter.print(value, strings))
}
