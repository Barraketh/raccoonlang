package com.raccoonlang

import java.nio.file.{Files, Paths}
import java.util.concurrent.{Callable, Executors, TimeUnit}
import scala.concurrent.duration.Duration

class BufferGpuApiTests extends munit.FunSuite {
  override val munitTimeout: Duration = Duration(20, "minutes")

  private val repoRoot = Paths.get("").toAbsolutePath.normalize
  private val gpuRoot = repoRoot.resolve("gpu")
  private val entry = gpuRoot.resolve("evaluator/BufferGpuApi.rac")
  private lazy val prelude = Prelude.fromPath(gpuRoot.resolve("Prelude.rac"))
  private lazy val loaded = BufferGpuSpikeSupport.loadApi(entry, gpuRoot, repoRoot, prelude)
  private lazy val api = loaded.api
  private lazy val natType = prelude.checkedEnv("Nat")
  private lazy val inputs17 = BufferGpuSpikeSupport.prepareInputs(api, 17, natType)
  private lazy val inputs83 = BufferGpuSpikeSupport.prepareInputs(api, 83, natType)
  private lazy val expected17 = BufferGpuSpikeSupport.exactMatmul(inputs17.a, inputs17.b)
  private lazy val expected83 = BufferGpuSpikeSupport.exactMatmul(inputs83.a, inputs83.b)
  private lazy val canonicalPlan = BufferGpuSpikeSupport.readyPlan(
    BufferGpuSpikeSupport.applyOnStack(api.compile, api.kernel),
    "canonical TinyGemm"
  )

  test("checked source wrapper compiles and reuses one generic plan for independent full outputs") {
    val source = Files.readString(entry)
    LanguageParser.parseProgram(source) match {
      case Success(_, _, _) => ()
      case Failure(_, at, message) =>
        fail(s"BufferGpuApi.rac did not parse at $at: $message near ${source.substring(at)}")
    }

    val planStats = BufferGpuSpikeSupport.decodeStats(
      BufferGpuSpikeSupport.applyOnStack(api.planStats, canonicalPlan)
    )
    assertEquals(planStats, BufferGpuSpikeSupport.CanonicalStats)

    val genericProgram = BufferGpuSpikeSupport.applyOnStack(api.planProgram, canonicalPlan)
    val words = BufferGpuSpikeSupport
      .list(BufferGpuSpikeSupport.applyOnStack(api.programWords, genericProgram), "generic Buffer.Program words")
      .map(BufferGpuSpikeSupport.natOf)
    assert(words.length > 6, s"generic program has only ${words.length} words")
    assertEquals(words(0), BigInt("42554646", 16))
    assertEquals(words(1), BigInt(3))
    assert(words(5) > 0, "generic program header reports no instructions")

    val source17 = runSource(inputs17, expected17, "source seed 17")
    val source83 = runSource(inputs83, expected83, "source seed 83")
    assertEquals(source17.stats, BufferGpuSpikeSupport.CanonicalStats)
    assertEquals(source83.stats, BufferGpuSpikeSupport.CanonicalStats)

    val initialRaw = runGpu(canonicalPlan, inputs17.aValue, inputs17.bValue)
    val initial = successful(initialRaw, expected17, "canonical seed 17")
    assertEquals(initial.stats, BufferGpuSpikeSupport.CanonicalStats)
    assertEquals(initial.outputs, source17.outputs)

    val seed83Run = successful(runGpu(canonicalPlan, inputs83.aValue, inputs83.bValue), expected83, "canonical seed 83")
    assertEquals(seed83Run.outputs, source83.outputs)
    assertEquals(seed83Run.stats, source83.stats)

    val changedAValues = inputs17.a.updated(37, (inputs17.a(37) + 1) % BufferGpuSpikeSupport.RingModulus)
    val changedA = BufferGpuSpikeSupport.changedInput(inputs17.aValue, inputs17.a, 37, changedAValues(37), natType)
    val expectedChangedA = BufferGpuSpikeSupport.exactMatmul(changedAValues, inputs17.b)
    val changedARun =
      successful(runGpu(canonicalPlan, changedA, inputs17.bValue), expectedChangedA, "same plan, changed A")

    val changedBValues = inputs17.b.updated(4097, (inputs17.b(4097) + 3) % BufferGpuSpikeSupport.RingModulus)
    val changedB = BufferGpuSpikeSupport.changedInput(inputs17.bValue, inputs17.b, 4097, changedBValues(4097), natType)
    val expectedChangedB = BufferGpuSpikeSupport.exactMatmul(inputs17.a, changedBValues)
    val changedBRun =
      successful(runGpu(canonicalPlan, inputs17.aValue, changedB), expectedChangedB, "same plan, changed B")
    assertNotEquals(changedARun.outputs, initial.outputs)
    assertNotEquals(changedBRun.outputs, initial.outputs)

    val repeat = successful(runGpu(canonicalPlan, inputs17.aValue, inputs17.bValue), expected17, "repeated seed 17")
    assertEquals(repeat, initial)

    val invalidA = BufferGpuSpikeSupport.invalidValueInput(inputs17.aValue, inputs17.a, 0, natType)
    val invalidB = BufferGpuSpikeSupport.invalidValueInput(inputs17.bValue, inputs17.b, 0, natType)
    val shortA =
      BufferGpuSpikeSupport.rebuildNatListLike(inputs17.aValue, inputs17.a.dropRight(1).map(BigInt(_)), natType)
    val shortB =
      BufferGpuSpikeSupport.rebuildNatListLike(inputs17.bValue, inputs17.b.dropRight(1).map(BigInt(_)), natType)
    assertEquals(runGpuError(canonicalPlan, invalidA, inputs17.bValue), BufferGpuSpikeSupport.InvalidInput(0))
    assertEquals(runGpuError(canonicalPlan, inputs17.aValue, invalidB), BufferGpuSpikeSupport.InvalidInput(1))
    assertEquals(runGpuError(canonicalPlan, shortA, inputs17.bValue), BufferGpuSpikeSupport.InvalidInput(0))
    assertEquals(runGpuError(canonicalPlan, inputs17.aValue, shortB), BufferGpuSpikeSupport.InvalidInput(1))

    val afterFailures =
      successful(runGpu(canonicalPlan, inputs17.aValue, inputs17.bValue), expected17, "run after invalid inputs")
    assertEquals(afterFailures, initial)
    assertEquals(
      successful(initialRaw, expected17, "retained first result"),
      initial,
      "later runs must not mutate an earlier output value"
    )
    assertEquals(BufferGpuSpikeSupport.natList(inputs17.aValue, "retained A after runs"), inputs17.a)
    assertEquals(BufferGpuSpikeSupport.natList(inputs17.bValue, "retained B after runs"), inputs17.b)

    val renamedPrepare = BufferGpuSpikeSupport.applyOnStack(
      api.prepare,
      api.renamedKernel,
      BufferGpuSpikeSupport.packedNat(17, natType)
    )
    assert(
      BufferGpuSpikeSupport.optionIsNone(renamedPrepare),
      "source prepare unexpectedly recognized the renamed kernel"
    )
    val renamedPlan = BufferGpuSpikeSupport.readyPlan(
      BufferGpuSpikeSupport.applyOnStack(api.compile, api.renamedKernel),
      "body-identical renamed TinyGemm"
    )
    val renamedStats = BufferGpuSpikeSupport.decodeStats(
      BufferGpuSpikeSupport.applyOnStack(api.planStats, renamedPlan)
    )
    assertEquals(renamedStats, BufferGpuSpikeSupport.CanonicalStats)
    val renamedRun = successful(runGpu(renamedPlan, inputs17.aValue, inputs17.bValue), expected17, "renamed kernel")
    assertEquals(renamedRun, initial)

    val pool = Executors.newFixedThreadPool(2)
    try {
      val left = pool.submit(new Callable[Value] {
        override def call(): Value = runGpu(canonicalPlan, inputs17.aValue, inputs17.bValue)
      })
      val right = pool.submit(new Callable[Value] {
        override def call(): Value = runGpu(canonicalPlan, inputs17.aValue, changedB)
      })
      val concurrent17 = successful(left.get(10, TimeUnit.MINUTES), expected17, "concurrent seed 17")
      val concurrentChangedB = successful(
        right.get(10, TimeUnit.MINUTES),
        expectedChangedB,
        "concurrent changed B"
      )
      assertEquals(concurrent17, initial)
      assertEquals(concurrentChangedB, changedBRun)
    } finally {
      pool.shutdownNow()
      pool.awaitTermination(30, TimeUnit.SECONDS)
    }
  }

  test("source-owned valid mutants preserve or change exact output and every other nonfuel mutant rejects") {
    val mutantNames = BufferGpuSpikeSupport.namedStrings(api.mutantNames, loaded.strings)
    val byName = mutantNames.toMap
    val expectedNames = BufferGpuSpikeSupport.NonfuelRejectNames.toSet ++
      Set("wrong-k-slice", "overlapping-tmem-load", "fuel")
    assertEquals(byName.keySet, expectedNames)

    val wrongKPlan = compileMutant(byName("wrong-k-slice"), "wrong-k-slice")
    val overlapPlan = compileMutant(byName("overlapping-tmem-load"), "overlapping-tmem-load")
    BufferGpuSpikeSupport.NonfuelRejectNames.foreach { name =>
      val kernel = BufferGpuSpikeSupport.applyOnStack(api.chooseMutant, api.kernel, byName(name))
      BufferGpuSpikeSupport.compileResult(BufferGpuSpikeSupport.applyOnStack(api.compile, kernel)) match {
        case BufferGpuSpikeSupport.Rejected(_) => ()
        case BufferGpuSpikeSupport.Ready(_)    => fail(s"unsupported/malformed source mutant '$name' compiled")
      }
    }

    val sourceWrongK = runSourceMutant(byName("wrong-k-slice"), "wrong-k-slice")
    val sourceOverlap = runSourceMutant(byName("overlapping-tmem-load"), "overlapping-tmem-load")
    assertEquals(sourceWrongK.stats, BufferGpuSpikeSupport.CanonicalStats)
    assertEquals(sourceOverlap.stats, BufferGpuSpikeSupport.OverlapStats)
    assertNotEquals(sourceWrongK.outputs, expected17, "wrong K slice must differ from the independent oracle")
    assertEquals(sourceOverlap.outputs, expected17, "overlapping load must preserve earlier snapshot values")

    val compiledWrongK = successful(
      runGpu(wrongKPlan, inputs17.aValue, inputs17.bValue),
      sourceWrongK.outputs,
      "compiled wrong-K mutant"
    )
    val compiledOverlap = successful(
      runGpu(overlapPlan, inputs17.aValue, inputs17.bValue),
      sourceOverlap.outputs,
      "compiled overlapping-load mutant"
    )
    assertEquals(compiledWrongK.stats, sourceWrongK.stats)
    assertEquals(compiledOverlap.stats, sourceOverlap.stats)
    assertNotEquals(compiledWrongK.outputs, expected17)
    assertEquals(compiledOverlap.outputs, expected17)
  }

  private def runSource(
      inputs: BufferGpuSpikeSupport.Inputs,
      expected: Vector[Int],
      label: String
  ): BufferGpuSpikeSupport.Success = {
    val result = BufferGpuSpikeSupport.applyOnStack(api.sourceRun, inputs.prepared)
    val error = BufferGpuSpikeSupport.sourceString(
      BufferGpuSpikeSupport.applyOnStack(api.sourceErrors, result),
      loaded.strings,
      s"$label error"
    )
    assertEquals(error, "ok")
    val stats = BufferGpuSpikeSupport.decodeStats(BufferGpuSpikeSupport.applyOnStack(api.sourceStats, result))
    val outputs = BufferGpuSpikeSupport.natList(BufferGpuSpikeSupport.applyOnStack(api.sourceOutputs, result), label)
    BufferGpuSpikeSupport.expectOutputs(outputs, expected, label)
    BufferGpuSpikeSupport.Success(outputs, stats)
  }

  private def runSourceMutant(name: Value, label: String): BufferGpuSpikeSupport.Success = {
    val result = BufferGpuSpikeSupport.applyOnStack(
      api.runMutant,
      name,
      BufferGpuSpikeSupport.packedNat(10000000, natType)
    )
    val error = BufferGpuSpikeSupport.sourceString(
      BufferGpuSpikeSupport.applyOnStack(api.sourceErrors, result),
      loaded.strings,
      s"$label error"
    )
    assertEquals(error, "ok", s"source mutant $label should complete")
    val stats = BufferGpuSpikeSupport.decodeStats(BufferGpuSpikeSupport.applyOnStack(api.sourceStats, result))
    val outputs = BufferGpuSpikeSupport.natList(BufferGpuSpikeSupport.applyOnStack(api.sourceOutputs, result), label)
    assertEquals(outputs.length, BufferGpuSpikeSupport.OutputCells)
    assert(outputs.forall(value => value >= 0 && value < BufferGpuSpikeSupport.RingModulus))
    BufferGpuSpikeSupport.Success(outputs, stats)
  }

  private def compileMutant(name: Value, label: String): Value = {
    val kernel = BufferGpuSpikeSupport.applyOnStack(api.chooseMutant, api.kernel, name)
    BufferGpuSpikeSupport.readyPlan(BufferGpuSpikeSupport.applyOnStack(api.compile, kernel), label)
  }

  private def runGpu(plan: Value, a: Value, b: Value): Value =
    BufferGpuSpikeSupport.applyOnStack(api.run, plan, a, b)

  private def runGpuError(plan: Value, a: Value, b: Value): BufferGpuSpikeSupport.RunError =
    BufferGpuSpikeSupport.gpuResult(runGpu(plan, a, b)) match {
      case BufferGpuSpikeSupport.GpuFailure(error) => error
      case BufferGpuSpikeSupport.GpuSuccess(result) =>
        fail(s"invalid input unexpectedly succeeded: ${result.outputs.take(4)}")
    }

  private def successful(raw: Value, expected: Vector[Int], label: String): BufferGpuSpikeSupport.Success = {
    val result = BufferGpuSpikeSupport.successful(raw, label)
    BufferGpuSpikeSupport.expectOutputs(result.outputs, expected, label)
    result
  }
}
