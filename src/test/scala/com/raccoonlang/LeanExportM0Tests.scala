package com.raccoonlang

import java.io.ByteArrayInputStream
import java.nio.charset.StandardCharsets

class LeanExportM0Tests extends munit.FunSuite {
  private val meta =
    """{"meta":{"exporter":{"name":"lean4export","version":"3.1.0"},"lean":{"githash":"919e297292280cdb27598edd4e03437be5850221","version":"4.24.0-rc1"},"format":{"version":"3.1.0"}}}"""

  private val fixture =
    Vector(
      meta,
      """{"str":{"pre":0,"str":"Acc"},"in":1}""",
      """{"str":{"pre":1,"str":"rec"},"in":2}""",
      """{"str":{"pre":0,"str":"Nat"},"in":3}""",
      """{"str":{"pre":3,"str":"add"},"in":4}""",
      """{"str":{"pre":0,"str":"Demo"},"in":5}""",
      """{"str":{"pre":5,"str":"imax"},"in":6}""",
      """{"str":{"pre":5,"str":"acc"},"in":7}""",
      """{"str":{"pre":5,"str":"irred"},"in":8}""",
      """{"str":{"pre":0,"str":"u"},"in":9}""",
      """{"str":{"pre":0,"str":"Even"},"in":10}""",
      """{"str":{"pre":0,"str":"Odd"},"in":11}""",
      """{"str":{"pre":0,"str":"WellFounded"},"in":12}""",
      """{"str":{"pre":12,"str":"fixF"},"in":13}""",
      """{"param":9,"il":1}""",
      """{"imax":[0,1],"il":2}""",
      """{"sort":2,"ie":0}""",
      """{"const":{"name":4,"us":[]},"ie":1}""",
      """{"const":{"name":2,"us":[1,0]},"ie":2}""",
      """{"app":{"fn":2,"arg":1},"ie":3}""",
      """{"bvar":0,"ie":4}""",
      """{"proj":{"typeName":3,"idx":0,"struct":4},"ie":5}""",
      """{"natVal":"42","ie":6}""",
      """{"strVal":"raccoon","ie":7}""",
      """{"sort":0,"ie":8}""",
      """{"def":{"name":6,"levelParams":[9],"type":0,"value":6,"hints":"opaque","safety":"safe","all":[6]}}""",
      """{"def":{"name":7,"levelParams":[],"type":8,"value":3,"hints":{"regular":1},"safety":"safe","all":[7]}}""",
      """{"opaque":{"name":8,"levelParams":[],"type":8,"value":4,"isUnsafe":false,"all":[8]}}""",
      """{"def":{"name":13,"levelParams":[],"type":8,"value":3,"hints":{"regular":1},"safety":"safe","all":[13]}}""",
      """{"inductive":{"types":[{"name":10,"levelParams":[],"type":8,"numParams":0,"numIndices":0,"all":[10,11],"ctors":[],"numNested":1,"isRec":true,"isUnsafe":false,"isReflexive":false},{"name":11,"levelParams":[],"type":8,"numParams":0,"numIndices":0,"all":[10,11],"ctors":[],"numNested":0,"isRec":true,"isUnsafe":false,"isReflexive":false}],"ctors":[],"recs":[]}}"""
    ).mkString("\n")

  private def scan(text: String): LeanExportM0.Report =
    LeanExportM0.scan(new ByteArrayInputStream(text.getBytes(StandardCharsets.UTF_8)), "fixture.ndjson")

  test("M0 scanner resolves interned nodes and records every decision-gate statistic") {
    val report = scan(fixture)

    assertEquals(report.metadata.formatVersion, "3.1.0")
    assertEquals(report.objects, 30L)
    assertEquals(report.names, 14)
    assertEquals(report.levels, 3)
    assertEquals(report.expressions, 9)
    assertEquals(report.declarations, 6L)
    assertEquals(report.inductiveBlocks, 1L)
    assertEquals(report.sortImaxDeclaredTypes, Vector("Demo.imax"))
    assertEquals(report.mutualBlocks, Vector(LeanExportM0.MutualBlock(Vector("Even", "Odd"))))
    assertEquals(report.nestedInductives, Vector(LeanExportM0.NestedInductive("Even", 1)))
    assertEquals(report.sortMotiveAccRecOutsideFixCluster, Vector("Demo.acc"))
    assertEquals(report.projectionNodes, 1L)
    assertEquals(report.natLiteralNodes, 1L)
    assertEquals(report.stringLiteralNodes, 1L)
    assertEquals(report.nativeNatOps, Vector("Nat.add" -> 1L))
    assertEquals(report.irreducibleDeclarations, Vector("Demo.imax", "Demo.irred"))
  }

  test("M0 report renderers retain counts and declaration provenance") {
    val report = scan(fixture)
    val text = report.renderText
    val json = report.renderJson

    assert(text.contains("declared types containing Sort(imax ...): 1"))
    assert(text.contains("Demo.acc"))
    assert(json.contains("\"sortImaxDeclaredTypes\":[\"Demo.imax\"]"))
    assert(json.contains("\"nativeNatOps\":{\"Nat.add\":1}"))
  }

  test("M0 scanner rejects unsupported format versions") {
    val badMeta = meta.replace("\"3.1.0\"}}}", "\"4.0.0\"}}}")
    val error = intercept[LeanExportM0.ScanError](scan(badMeta))
    assert(error.detail.contains("unsupported lean4export format 4.0.0"))
  }

  test("M0 scanner rejects forward expression references") {
    val input = s"$meta\n" + """{"app":{"fn":0,"arg":0},"ie":0}"""
    val error = intercept[LeanExportM0.ScanError](scan(input))
    assert(error.detail.contains("expression reference 0 has not been defined"))
  }

  test("shared reader exposes compact semantic nodes and heap counters") {
    var seen = Vector.empty[LeanExportIr.ExportDecl]
    val consumer = new LeanExportIr.LeanExportConsumer {
      def onMeta(meta: LeanExportIr.ExportMeta): Unit = ()
      def onDeclaration(decl: LeanExportIr.ExportDecl, tables: LeanExportIr.ExportTables): Unit = seen :+= decl
      def finish(tables: LeanExportIr.ExportTables): Unit = ()
    }
    val result = LeanExportReader.read(
      new ByteArrayInputStream(fixture.getBytes(StandardCharsets.UTF_8)),
      "fixture.ndjson",
      consumer
    )
    assertEquals(result.tables.nameNode(LeanExportIr.NameId(1)), LeanExportIr.NameStr(LeanExportIr.NameId(0), "Acc"))
    assertEquals(result.tables.exprNode(LeanExportIr.ExprId(6)), LeanExportIr.NatVal(BigInt(42)))
    assert(result.tables.currentBytes > 0L)
    assert(result.tables.highWaterBytes >= result.tables.currentBytes)
    assertEquals(seen.length, 5)
  }

  test("shared reader rejects duplicate fields with structured provenance") {
    val input = s"$meta\n" + """{"bvar":0,"bvar":1,"ie":0}"""
    val error = intercept[MalformedExport](
      LeanExportReader.read(
        new ByteArrayInputStream(input.getBytes(StandardCharsets.UTF_8)),
        "bad.ndjson",
        LeanExportIr.LeanExportConsumer.ignore
      )
    )
    assertEquals(error.provenance.objectOrdinal, 2L)
    assert(error.message.contains("duplicate field 'bvar'"))
  }

  test("shared reader enforces pinned numeric token kinds") {
    val numericNat = s"$meta\n" + """{"natVal":42,"ie":0}"""
    assert(intercept[LeanExportM0.ScanError](scan(numericNat)).detail.contains("VALUE_STRING"))

    val stringNameNumber = Vector(
      meta,
      """{"num":{"pre":0,"i":"1"},"in":1}"""
    ).mkString("\n")
    assert(intercept[LeanExportM0.ScanError](scan(stringNameNumber)).detail.contains("VALUE_NUMBER_INT"))

    val stringRegularHeight = Vector(
      meta,
      """{"str":{"pre":0,"str":"d"},"in":1}""",
      """{"sort":0,"ie":0}""",
      """{"def":{"name":1,"levelParams":[],"type":0,"value":0,"hints":{"regular":"1"},"safety":"unsafe","all":[1]}}"""
    ).mkString("\n")
    assert(intercept[LeanExportM0.ScanError](scan(stringRegularHeight)).detail.contains("VALUE_NUMBER_INT"))
  }

  test("shared reader rejects the non-format constructor owner alias") {
    val input = Vector(
      meta,
      """{"str":{"pre":0,"str":"Even"},"in":1}""",
      """{"str":{"pre":1,"str":"mk"},"in":2}""",
      """{"sort":0,"ie":0}""",
      """{"inductive":{"types":[{"name":1,"levelParams":[],"type":0,"numParams":0,"numIndices":0,"all":[1],"ctors":[2],"numNested":0,"isRec":false,"isUnsafe":false,"isReflexive":false}],"ctors":[{"name":2,"levelParams":[],"type":0,"induct":1,"inductive":1,"cidx":0,"numParams":0,"numFields":0,"isUnsafe":false}],"recs":[]}}"""
    ).mkString("\n")
    val error = intercept[LeanExportM0.ScanError](scan(input))
    assert(error.detail.contains("unknown ConstructorVal field 'inductive'"))
  }
}
