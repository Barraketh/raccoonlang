package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import java.nio.file.{Files, Paths}
import scala.concurrent.duration.Duration

class BufferProgramSourceTests extends munit.FunSuite {
  override val munitTimeout = Duration(2, "minutes")

  private def nat(value: Value): BigInt = value match {
    case packed: Value.VPacked if packed.codec eq Value.NatCodec           => packed.natValue.get
    case Value.VCtor(head, Vector(), _) if head.name == "Nat.zero"         => BigInt(0)
    case Value.VCtor(head, Vector(previous), _) if head.name == "Nat.succ" => BigInt(1) + nat(previous)
    case other => fail(s"Expected a Nat in Buffer.run result, got $other")
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
        case other => fail(s"Expected a List in Buffer.run result, got $other")
      }
    }
    result.result()
  }

  private def successBytes(value: Value): Vector[Vector[BigInt]] = value match {
    case Value.VCtor(head, Vector(outputs), _) if head.name == "Buffer.Result.success" =>
      list(outputs).map(row => list(row).map(nat))
    case other => fail(s"Expected Buffer.Result.success, got $other")
  }

  private def runEntry(root: java.nio.file.Path, relative: String): Value = {
    val entry = root.resolve(relative)
    val loaded = ModuleLoader.load(entry, ModuleLoader.LoadConfig(Vector(root), Prelude.default))
    val checked = Execution.check(Execution.elaborate(loaded.program, Prelude.default))
    checked.result.getOrElse(fail(s"$relative has no result"))
  }

  private def assertSemanticRejection(
      root: java.nio.file.Path,
      relative: String,
      expected: Set[String],
      expectedDefinition: Option[String],
      exactError: Option[TypeError] = None
  ): Unit = {
    val entry = root.resolve(relative)
    val source = Files.readString(entry)
    LanguageParser.parseProgram(source) match {
      case Success(_, _, _)        => ()
      case Failure(_, at, message) => fail(s"$relative did not parse at $at: $message near ${source.substring(at)}")
    }
    val loaded = ModuleLoader.load(entry, ModuleLoader.LoadConfig(Vector(root), Prelude.default))
    val rejected = intercept[Execution.CheckFailure] {
      Execution.check(Execution.elaborate(loaded.program, Prelude.default))
    }
    val errors = rejected.diagnostics.map(_.error.productPrefix).toSet
    assert(
      errors == expected,
      s"Expected exactly $expected for $relative, got $errors\n${rejected.getMessage}"
    )
    assertEquals(rejected.diagnostics.size, 1, s"Expected one localized diagnostic for $relative")
    val entrySourceId = loaded.sources.find(_.path == entry.toRealPath()).map(_.sourceId)
    assert(entrySourceId.nonEmpty, s"The loaded source graph did not contain $entry")
    assert(
      rejected.diagnostics.forall(_.span.flatMap(_.source) == entrySourceId),
      s"Expected the diagnostic for $relative to originate in its fixture, got ${rejected.diagnostics.map(_.span)}"
    )
    expectedDefinition.foreach { name =>
      assert(
        rejected.diagnostics.exists(_.frames.contains(Frame.InDefinition(name))),
        s"Expected the diagnostic for $relative in definition $name, got ${rejected.diagnostics.map(_.frames)}"
      )
    }
    exactError.foreach { wanted =>
      assert(
        rejected.diagnostics.exists(_.error == wanted),
        s"Expected $wanted for $relative, got ${rejected.diagnostics.map(_.error)}"
      )
    }
  }

  test("source builder runs a finite byte transform through the native immutable-result boundary") {
    val root = Paths.get("").toAbsolutePath.normalize
    val entry = root.resolve("buffer/TokenProbe.rac")
    val sourcePath = root.resolve("buffer/Program.rac")
    val source = Files.readString(sourcePath)
    LanguageParser.parseProgram(source) match {
      case Success(_, _, _)        => ()
      case Failure(_, at, message) => fail(s"Program.rac parse failed at $at: $message near ${source.substring(at)}")
    }
    val loadedProgram = ModuleLoader.load(sourcePath, ModuleLoader.LoadConfig(Vector(root), Prelude.default))
    try TypeChecker.check(Elaborator.elaborate(loadedProgram.program, Prelude.default))
    catch { case diagnostic: Diagnostic => fail(ErrorReporter.pretty(diagnostic, Source(source), None)) }
    val entrySource = Files.readString(entry)
    LanguageParser.parseProgram(entrySource) match {
      case Success(_, _, _) => ()
      case Failure(_, at, message) =>
        fail(s"TokenProbe.rac parse failed at $at: $message near ${entrySource.substring(at)}")
    }
    val checked =
      try {
        val loaded = ModuleLoader.load(entry, ModuleLoader.LoadConfig(Vector(root), Prelude.default))
        Execution.check(Execution.elaborate(loaded.program, Prelude.default))
      } catch {
        case diagnostic: Diagnostic => fail(ErrorReporter.pretty(diagnostic, Source(entrySource), None))
      }
    val result = checked.result.getOrElse(fail("TokenProbe has no result"))
    result match {
      case Value.VCtor(pair, Vector(first, Value.VCtor(innerPair, Vector(second, again), _)), _)
          if pair.name == "Pair.mk" && innerPair.name == "Pair.mk" =>
        assertEquals(successBytes(first), Vector(Vector(BigInt(42))))
        assertEquals(successBytes(second), Vector(Vector(BigInt(10))))
        assertEquals(successBytes(again), Vector(Vector(BigInt(42))))
        assertEquals(successBytes(first), successBytes(again))
      case other => fail(s"Expected Buffer.run's Pair result, got $other")
    }
  }

  test("nested owners support a captured-register reduction, zero trips, and a finite branch") {
    val root = Paths.get("").toAbsolutePath.normalize
    runEntry(root, "buffer/ReductionProbe.rac") match {
      case Value.VCtor(pair, Vector(nonEmpty, empty), _) if pair.name == "Pair.mk" =>
        assertEquals(successBytes(nonEmpty), Vector(Vector(BigInt(10), BigInt(0), BigInt(0), BigInt(0))))
        assertEquals(successBytes(empty), Vector(Vector(BigInt(0), BigInt(0), BigInt(0), BigInt(0))))
      case other => fail(s"Expected the nonzero and zero-trip Buffer.run results, got $other")
    }
  }

  test("extent metadata can outlive its owner because it carries no buffer authority") {
    val root = Paths.get("").toAbsolutePath.normalize
    assertEquals(nat(runEntry(root, "buffer/accepted/handle_metadata_escape.rac")), BigInt(3))
  }

  test("ancestor views compose for nested lifts and preserve the emitted scalar result") {
    val root = Paths.get("").toAbsolutePath.normalize
    val result = runEntry(root, "buffer/accepted/nested_frame_views.rac")
    assertEquals(
      successBytes(result),
      Vector(Vector(BigInt(1), BigInt(0), BigInt(0), BigInt(0), BigInt(0), BigInt(0), BigInt(0), BigInt(0)))
    )
  }

  test("a mutable register cannot be packaged as Fixed loop state") {
    val root = Paths.get("").toAbsolutePath.normalize
    assertSemanticRejection(
      root,
      "buffer/rejected/fixed_register.rac",
      Set("SealedConstructor"),
      expectedDefinition = Some("forged"),
      exactError = Some(SealedConstructor("Buffer.Fixed", Some("Buffer.Fixed.mk")))
    )
  }

  test("source ownership rejects forged, duplicated, dropped, reused, captured, cross-builder, and stale resources") {
    val root = Paths.get("").toAbsolutePath.normalize
    Vector(
      ("buffer/rejected/duplicate_owner.rac", Set("LinearReused"), "duplicate"),
      ("buffer/rejected/unused_owner.rac", Set("LinearUnused"), "discard"),
      ("buffer/rejected/forged_owner.rac", Set("SealedConstructor"), "forged"),
      ("buffer/rejected/store_after_export.rac", Set("LinearReused"), "useAfterExport"),
      ("buffer/rejected/load_after_release.rac", Set("LinearReused"), "loadAfterRelease"),
      ("buffer/rejected/store_after_release.rac", Set("LinearReused"), "storeAfterRelease"),
      ("buffer/rejected/capture_owner_in_repeat.rac", Set("TypeMismatch"), "invalid"),
      ("buffer/rejected/cross_builder_handle.rac", Set("TypeMismatch"), "invalid"),
      ("buffer/rejected/cross_allocation_owner.rac", Set("TypeMismatch"), "mismatched"),
      ("buffer/rejected/cross_root_value.rac", Set("TypeMismatch"), "useForeignRoot"),
      ("buffer/rejected/packaged_loop_index.rac", Set("TypeMismatch"), "usePackagedLoopIndex"),
      ("buffer/rejected/packaged_branch_value.rac", Set("TypeMismatch"), "usePackagedBranchValue"),
      ("buffer/rejected/forged_reverse_view.rac", Set("SealedConstructor"), "reverseView")
    ).foreach { case (relative, expected, definition) =>
      assertSemanticRejection(root, relative, expected, expectedDefinition = Some(definition))
    }
  }
}
