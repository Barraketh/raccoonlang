package com.raccoonlang

import com.raccoonlang.LeanExportIr._
import com.raccoonlang.Value.VPacked

import java.io.ByteArrayInputStream
import java.nio.charset.StandardCharsets

class LeanImportT14Tests extends munit.FunSuite {
  private val meta =
    s"""{"meta":{"exporter":{"name":"${LeanExportReader.ExporterName}","version":"${LeanExportReader.ExporterVersion}"},"lean":{"githash":"${LeanExportReader.LeanGitHash}","version":"${LeanExportReader.LeanVersion}"},"format":{"version":"${LeanExportReader.FormatVersion}"}}}"""

  private val fixture = Vector(
    meta,
    """{"str":{"pre":0,"str":"Carrier"},"in":1}""",
    """{"str":{"pre":0,"str":"carrierValue"},"in":2}""",
    """{"str":{"pre":0,"str":"letValue"},"in":3}""",
    """{"str":{"pre":0,"str":"metadataValue"},"in":4}""",
    """{"str":{"pre":0,"str":"unsafeValue"},"in":5}""",
    """{"str":{"pre":0,"str":"partialValue"},"in":6}""",
    """{"str":{"pre":0,"str":"opaqueValue"},"in":7}""",
    """{"str":{"pre":0,"str":"theoremValue"},"in":8}""",
    """{"str":{"pre":0,"str":"x"},"in":9}""",
    """{"succ":0,"il":1}""",
    """{"sort":1,"ie":0}""",
    """{"const":{"name":1,"us":[]},"ie":1}""",
    """{"const":{"name":2,"us":[]},"ie":2}""",
    """{"bvar":0,"ie":3}""",
    """{"letE":{"name":9,"type":1,"value":2,"body":3,"nondep":false},"ie":4}""",
    """{"mdata":{"expr":2,"data":{"source":{"synthetic":true},"ignored":[1,2,3]}},"ie":5}""",
    """{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}""",
    """{"axiom":{"name":2,"levelParams":[],"type":1,"isUnsafe":false}}""",
    """{"def":{"name":3,"levelParams":[],"type":1,"value":4,"hints":{"regular":7},"safety":"safe","all":[3]}}""",
    """{"def":{"name":4,"levelParams":[],"type":1,"value":5,"hints":"abbrev","safety":"safe","all":[4]}}""",
    """{"def":{"name":5,"levelParams":[],"type":1,"value":2,"hints":{"regular":1},"safety":"unsafe","all":[5]}}""",
    """{"def":{"name":6,"levelParams":[],"type":1,"value":2,"hints":{"regular":1},"safety":"partial","all":[6]}}""",
    """{"opaque":{"name":7,"levelParams":[],"type":1,"value":2,"isUnsafe":false,"all":[7]}}""",
    """{"thm":{"name":8,"levelParams":[],"type":1,"value":2,"all":[8]}}"""
  ).mkString("\n")

  private def imported(text: String = fixture): Either[Vector[LeanImportDiagnostic], LeanImportResult] =
    LeanImportSession.importStream(new ByteArrayInputStream(text.getBytes(StandardCharsets.UTF_8)), "t14.ndjson")

  test("let, metadata, hints, opaque declarations, and theorem bodies import and publish cleanly") {
    val result = imported().fold(errors => fail(errors.map(_.message).mkString("; ")), identity)
    Vector("letValue", "metadataValue").foreach { name =>
      assert(ValueEquivalence.defEq(result.env(name), result.env("carrierValue")), name)
    }
    assertEquals(result.env("opaqueValue").asInstanceOf[Value.VConst].name, "opaqueValue")
    assertEquals(result.env("theoremValue").asInstanceOf[Value.VConst].name, "theoremValue")
    assertEquals(result.manifest.skipped.map(_.name), Vector("unsafeValue", "partialValue"))
    assertEquals(result.manifest.skipped.map(_.kind), Vector("def", "def"))
    assertEquals(result.manifest.skipped.map(_.safety), Vector(Some(Unsafe), Some(Partial)))
    assertEquals(result.manifest.installed.find(_.name == "letValue").flatMap(_.hint), Some(HintRegular(7)))
    assert(result.manifest.installed.find(_.name == "opaqueValue").exists(_.opaque))
    assert(result.manifest.installed.find(_.name == "theoremValue").exists(_.opaque))
    assertEquals(result.metrics.transparentGlobals, 2L)
    assertEquals(result.metrics.opaqueGlobals, 4L)
  }

  test("nondependent let metadata is checked and opaque/theorem source bodies cannot bypass checking") {
    val badNonDep = fixture.replace("\"nondep\":false", "\"nondep\":true")
    assert(imported(badNonDep).swap.toOption.get.exists(_.isInstanceOf[InvalidBinderMetadata]))

    val badOpaque = fixture.replace(
      """{"opaque":{"name":7,"levelParams":[],"type":1,"value":2,"isUnsafe":false,"all":[7]}}""",
      """{"opaque":{"name":7,"levelParams":[],"type":1,"value":1,"isUnsafe":false,"all":[7]}}"""
    )
    assert(imported(badOpaque).swap.toOption.get.exists(_.isInstanceOf[DeclarationTypeError]))

    val badTheorem = fixture.replace(
      """{"thm":{"name":8,"levelParams":[],"type":1,"value":2,"all":[8]}}""",
      """{"thm":{"name":8,"levelParams":[],"type":1,"value":1,"all":[8]}}"""
    )
    assert(imported(badTheorem).swap.toOption.get.exists(_.isInstanceOf[DeclarationTypeError]))
  }

  test("safe declarations cannot depend on skipped unsafe or partial globals") {
    val extra = Vector(
      """{"str":{"pre":0,"str":"badDependency"},"in":10}""",
      """{"const":{"name":5,"us":[]},"ie":6}""",
      """{"def":{"name":10,"levelParams":[],"type":1,"value":6,"hints":"abbrev","safety":"safe","all":[10]}}"""
    ).mkString("\n")
    val errors = imported(fixture + "\n" + extra).swap.getOrElse(fail("unsafe dependency unexpectedly imported"))
    assert(errors.exists(_.isInstanceOf[UnsafeDependency]))
  }

  test("Nat and String literal lowering is gated by validated representation state") {
    var tables: ExportTables = null
    val input = Vector(meta, """{"natVal":"12345678901234567890","ie":0}""",
      """{"strVal":"raccoon 🦝","ie":1}""").mkString("\n")
    LeanExportReader.read(new ByteArrayInputStream(input.getBytes(StandardCharsets.UTF_8)), "literals.ndjson",
      new LeanExportConsumer {
        def onMeta(meta: ExportMeta): Unit = ()
        def onDeclaration(decl: ExportDecl, current: ExportTables): Unit = ()
        def finish(current: ExportTables): Unit = tables = current
      })

    val natLowerer = new LeanTermLowerer(tables, Prelude.default.checkedEnv, LeanGlobalRegistry.empty, "literal")
    val nat = TypeChecker.checkTerm(natLowerer.lowerTerm(ExprId(0)), Prelude.default.checkedEnv).value
    assertEquals(nat.asInstanceOf[VPacked].natValue, Some(BigInt("12345678901234567890")))

    val bootstrap = LeanImportBootstrap.build().fold(errors => fail(errors.map(_.message).mkString("; ")), identity)
    val gated = new LeanTermLowerer(tables, bootstrap, LeanGlobalRegistry.empty, "literal")
    intercept[MissingKernelGate](gated.lowerTerm(ExprId(0)))
    intercept[MissingKernelGate](gated.lowerTerm(ExprId(1)))
  }

  test("exported projection nodes lower directly to positional Core projections") {
    var tables: ExportTables = null
    val input = Vector(
      meta,
      """{"str":{"pre":0,"str":"Prod"},"in":1}""",
      """{"str":{"pre":1,"str":"mk"},"in":2}""",
      """{"str":{"pre":0,"str":"Nat"},"in":3}""",
      """{"succ":0,"il":1}""",
      """{"const":{"name":2,"us":[1,1]},"ie":0}""",
      """{"const":{"name":3,"us":[]},"ie":1}""",
      """{"app":{"fn":0,"arg":1},"ie":2}""",
      """{"app":{"fn":2,"arg":1},"ie":3}""",
      """{"natVal":"7","ie":4}""",
      """{"app":{"fn":3,"arg":4},"ie":5}""",
      """{"natVal":"9","ie":6}""",
      """{"app":{"fn":5,"arg":6},"ie":7}""",
      """{"proj":{"typeName":1,"idx":0,"struct":7},"ie":8}"""
    ).mkString("\n")
    LeanExportReader.read(new ByteArrayInputStream(input.getBytes(StandardCharsets.UTF_8)), "projection.ndjson",
      new LeanExportConsumer {
        def onMeta(meta: ExportMeta): Unit = ()
        def onDeclaration(decl: ExportDecl, current: ExportTables): Unit = ()
        def finish(current: ExportTables): Unit = tables = current
      })
    val provenance = tables.exprProvenance(ExprId(0))
    val registry = LeanGlobalRegistry.empty
      .add(ImportedGlobal(NameId(1), "Prod", provenance, Installed, Vector(NameId(0), NameId(0))), tables)
      .add(ImportedGlobal(NameId(2), "Prod.mk", provenance, Installed, Vector(NameId(0), NameId(0))), tables)
      .add(ImportedGlobal(NameId(3), "Nat", provenance, Installed, Vector.empty), tables)
    val env = Prelude.default.checkedEnv
    val lowerer = new LeanTermLowerer(tables, env, registry, "projection")
    val lowered = lowerer.lowerTerm(ExprId(8))
    assert(lowered.isInstanceOf[CoreAst.Term.Proj])
    val projected = TypeChecker.checkTerm(lowered, env).value.asInstanceOf[VPacked]
    assertEquals(projected.natValue, Some(BigInt(7)))

    val skippedRegistry = LeanGlobalRegistry.empty
      .add(ImportedGlobal(NameId(1), "Prod", provenance, SkippedUnsafe, Vector(NameId(0), NameId(0))), tables)
    intercept[UnsafeDependency](new LeanTermLowerer(tables, env, skippedRegistry, "projection").lowerTerm(ExprId(8)))
  }

  test("let values and results retain expected lambda types after implicit demotion") {
    var tables: ExportTables = null
    val input = Vector(
      meta,
      """{"str":{"pre":0,"str":"x"},"in":1}""",
      """{"str":{"pre":0,"str":"f"},"in":2}""",
      """{"str":{"pre":0,"str":"Nat"},"in":3}""",
      """{"const":{"name":3,"us":[]},"ie":0}""",
      """{"forallE":{"name":1,"type":0,"body":0,"binderInfo":"implicit"},"ie":1}""",
      """{"bvar":0,"ie":2}""",
      """{"lam":{"name":1,"type":0,"body":2,"binderInfo":"implicit"},"ie":3}""",
      """{"letE":{"name":2,"type":1,"value":3,"body":3,"nondep":true},"ie":4}"""
    ).mkString("\n")
    LeanExportReader.read(new ByteArrayInputStream(input.getBytes(StandardCharsets.UTF_8)), "let-lambda.ndjson",
      new LeanExportConsumer {
        def onMeta(meta: ExportMeta): Unit = ()
        def onDeclaration(decl: ExportDecl, current: ExportTables): Unit = ()
        def finish(current: ExportTables): Unit = tables = current
      })
    val env = Prelude.default.checkedEnv
    val provenance = tables.exprProvenance(ExprId(0))
    val registry = LeanGlobalRegistry.empty
      .add(ImportedGlobal(NameId(3), "Nat", provenance, Installed, Vector.empty), tables)
    val lowerer = new LeanTermLowerer(tables, env, registry, "letLambda")
    val declared = lowerer.lowerDeclarationType(Vector.empty, ExprId(1))
    val body = lowerer.lowerDeclarationBody(ExprId(4), declared, "letLambda")
    TypeChecker.checkTerm(body, TypeChecker.checkTerm(declared.term, env).value, env)
  }

  test("failed publication is all-or-error and diagnostics are bounded") {
    val corrupt = fixture.replace(
      """{"thm":{"name":8,"levelParams":[],"type":1,"value":2,"all":[8]}}""",
      """{"thm":{"name":8,"levelParams":[],"type":1,"value":0,"all":[8]}}"""
    )
    val errors = imported(corrupt).swap.getOrElse(fail("bad transaction unexpectedly imported"))
    assert(errors.forall(_.getMessage.length <= 4096))
    val oversized = DeclarationTypeError(errors.head.provenance, "X" * 5000)
    assertEquals(oversized.getMessage.length, 4096)
  }

  test("ordinary all groups cannot claim non-ordinary declarations in either order") {
    val groupName = """{"str":{"pre":0,"str":"grouped"},"in":10}"""
    val grouped = """{"def":{"name":10,"levelParams":[],"type":1,"value":2,"hints":"abbrev","safety":"safe","all":[1,10]}}"""
    val afterAxiom = Vector(meta, fixture.split('\n').slice(1, 18).mkString("\n"), groupName, grouped).mkString("\n")
    assert(imported(afterAxiom).swap.toOption.get.exists(_.isInstanceOf[MalformedExport]))

    val beforeAxiom = Vector(
      meta,
      """{"str":{"pre":0,"str":"claimed"},"in":1}""",
      """{"str":{"pre":0,"str":"grouped"},"in":2}""",
      """{"succ":0,"il":1}""",
      """{"sort":1,"ie":0}""",
      """{"def":{"name":2,"levelParams":[],"type":0,"value":0,"hints":"abbrev","safety":"unsafe","all":[1,2]}}""",
      """{"axiom":{"name":1,"levelParams":[],"type":0,"isUnsafe":false}}"""
    ).mkString("\n")
    assert(imported(beforeAxiom).swap.toOption.get.exists(_.isInstanceOf[MalformedExport]))
  }
}
