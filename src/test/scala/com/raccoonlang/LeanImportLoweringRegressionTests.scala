package com.raccoonlang

import java.io.ByteArrayInputStream
import java.nio.charset.StandardCharsets
import scala.collection.mutable

class LeanImportLoweringRegressionTests extends munit.FunSuite {
  private final class ExportBuilder {
    private val lines = mutable.ArrayBuffer(
      s"""{"meta":{"exporter":{"name":"${LeanExportReader.ExporterName}","version":"${LeanExportReader.ExporterVersion}"},"lean":{"githash":"${LeanExportReader.LeanGitHash}","version":"${LeanExportReader.LeanVersion}"},"format":{"version":"${LeanExportReader.FormatVersion}"}}}"""
    )
    private var nextName = 1
    private var nextLevel = 1
    private var nextExpr = 0

    def name(value: String, prefix: Int = 0): Int = {
      val id = nextName
      nextName += 1
      lines += s"""{"str":{"pre":$prefix,"str":"$value"},"in":$id}"""
      id
    }

    def levelSucc(of: Int): Int = level(s"""{"succ":$of""")
    def levelParam(name: Int): Int = level(s"""{"param":$name""")

    private def level(payload: String): Int = {
      val id = nextLevel
      nextLevel += 1
      lines += s"$payload,\"il\":$id}"
      id
    }

    def sort(level: Int): Int = expr(s""""sort":$level""")
    def const(name: Int, levels: Vector[Int] = Vector.empty): Int =
      expr("\"const\":{\"name\":" + name + ",\"us\":[" + levels.mkString(",") + "]}")
    def bvar(index: Int): Int = expr(s""""bvar":$index""")
    def app(fn: Int, arg: Int): Int = expr(s""""app":{"fn":$fn,"arg":$arg}""")
    def forall(name: Int, tpe: Int, body: Int, info: String = "default"): Int =
      expr(s""""forallE":{"name":$name,"type":$tpe,"body":$body,"binderInfo":"$info"}""")
    def lam(name: Int, tpe: Int, body: Int, info: String = "default"): Int =
      expr(s""""lam":{"name":$name,"type":$tpe,"body":$body,"binderInfo":"$info"}""")
    def let(name: Int, tpe: Int, value: Int, body: Int, nonDependent: Boolean): Int =
      expr(s""""letE":{"name":$name,"type":$tpe,"value":$value,"body":$body,"nondep":$nonDependent}""")
    def mdata(child: Int): Int = expr(s""""mdata":{"expr":$child,"data":{"synthetic":true}}""")

    private def expr(payload: String): Int = {
      val id = nextExpr
      nextExpr += 1
      lines += s"{$payload,\"ie\":$id}"
      id
    }

    def axiom(name: Int, tpe: Int, levelParams: Vector[Int] = Vector.empty): Unit =
      lines += s"""{"axiom":{"name":$name,"levelParams":[${levelParams.mkString(",")}],"type":$tpe,"isUnsafe":false}}"""

    def definition(name: Int, tpe: Int, value: Int, levelParams: Vector[Int] = Vector.empty): Unit =
      lines +=
        s"""{"def":{"name":$name,"levelParams":[${levelParams.mkString(
            ","
          )}],"type":$tpe,"value":$value,"hints":"abbrev","safety":"safe","all":[$name]}}"""

    def bytes: Array[Byte] = lines.mkString("\n").getBytes(StandardCharsets.UTF_8)

    def result: Either[Vector[LeanImportDiagnostic], LeanImportResult] = {
      LeanImportSession.importStream(new ByteArrayInputStream(bytes), "lowering-regression.ndjson")
    }
  }

  private def imported(fixture: ExportBuilder): LeanImportResult =
    fixture.result.fold(
      errors =>
        fail(
          errors
            .map(error =>
              s"${error.getClass.getSimpleName}${error.declaration.fold("")(name => s"($name)")}: ${error.message}"
            )
            .mkString("; ")
        ),
      identity
    )

  test("application arguments are lowered against their expected binder types") {
    val f = new ExportBuilder
    val bName = f.name("B")
    val xName = f.name("x")
    val fnName = f.name("higher")
    val useName = f.name("useHigher")
    val sort1 = f.sort(f.levelSucc(0))
    val b = f.const(bName)
    val unary = f.forall(xName, b, b)
    val higherType = f.forall(f.name("fn"), unary, b)
    val identity = f.lam(xName, b, f.bvar(0))
    val useBody = f.app(f.const(fnName), identity)
    f.axiom(bName, sort1)
    f.axiom(fnName, higherType)
    f.definition(useName, b, useBody)

    imported(f)
  }

  test("nested eta expansion freshens every generated binder") {
    val f = new ExportBuilder
    val bName = f.name("B")
    val xName = f.name("x")
    val gName = f.name("g")
    val fnName = f.name("f")
    val testName = f.name("nestedPartial")
    val sort1 = f.sort(f.levelSucc(0))
    val b = f.const(bName)
    val unary = f.forall(xName, b, b)
    val binaryOperator = f.forall(f.name("h"), unary, unary)
    val inner = f.app(f.const(fnName), f.const(gName))
    val outer = f.app(f.const(fnName), inner)
    f.axiom(bName, sort1)
    f.axiom(gName, unary)
    f.axiom(fnName, binaryOperator)
    f.definition(testName, unary, outer)

    imported(f)
  }

  test("zero-term-binder polymorphic values are checked under their universe wrapper") {
    val f = new ExportBuilder
    val uName = f.name("u")
    val carrierName = f.name("UCarrier")
    val valueName = f.name("uValue")
    val aliasName = f.name("uAlias")
    val u = f.levelParam(uName)
    val carrierSort = f.sort(u)
    val carrierAtU = f.const(carrierName, Vector(u))
    val valueAtU = f.const(valueName, Vector(u))
    f.axiom(carrierName, carrierSort, Vector(uName))
    f.axiom(valueName, carrierAtU, Vector(uName))
    f.definition(aliasName, carrierAtU, valueAtU, Vector(uName))

    imported(f)
  }

  test("a closed declaration body cannot resolve a bvar from its declared type") {
    val f = new ExportBuilder
    val uName = f.name("u")
    val bName = f.name("B")
    val xName = f.name("x")
    val yName = f.name("y")
    val fnName = f.name("binary")
    val badName = f.name("bad")
    val sort1 = f.sort(f.levelSucc(0))
    val b = f.const(bName)
    val binary = f.forall(xName, b, f.forall(yName, b, b))
    val unary = f.forall(xName, b, b)
    val malformedBody = f.app(f.const(fnName), f.bvar(0))
    f.axiom(bName, sort1)
    f.axiom(fnName, binary)
    f.definition(badName, unary, malformedBody, Vector(uName))

    val errors = f.result.swap.getOrElse(fail("out-of-scope bvar unexpectedly imported"))
    assert(errors.exists(_.isInstanceOf[BadBVar]))
  }

  test("Pi-valued local terms carry calling conventions for underapplication") {
    val f = new ExportBuilder
    val bName = f.name("B")
    val xName = f.name("x")
    val yName = f.name("y")
    val fnName = f.name("fn")
    val aliasName = f.name("Fn")
    val partialName = f.name("localPartial")
    val sort1 = f.sort(f.levelSucc(0))
    val b = f.const(bName)
    val unary = f.forall(xName, b, b)
    val binary = f.forall(xName, b, f.forall(yName, b, b))
    val alias = f.const(aliasName)
    val partialType = f.forall(fnName, binary, f.forall(xName, b, alias))
    val partialBody = f.lam(fnName, binary, f.lam(xName, b, f.app(f.bvar(1), f.bvar(0))))
    f.axiom(bName, sort1)
    f.definition(aliasName, sort1, unary)
    f.definition(partialName, partialType, partialBody)

    imported(f)
  }

  test("underapplication eta-expands after crossing a second Pi layer") {
    val f = new ExportBuilder
    val bName = f.name("B")
    val xName = f.name("x")
    val yName = f.name("y")
    val valueName = f.name("value")
    val binaryName = f.name("Binary")
    val returnsName = f.name("returnsBinary")
    val partialName = f.name("secondLayerPartial")
    val sort1 = f.sort(f.levelSucc(0))
    val b = f.const(bName)
    val unary = f.forall(xName, b, b)
    val binary = f.forall(xName, b, f.forall(yName, b, b))
    val binaryAlias = f.const(binaryName)
    val returnsType = f.forall(xName, b, binaryAlias)
    val firstLayer = f.app(f.const(returnsName), f.const(valueName))
    val partial = f.app(firstLayer, f.const(valueName))
    f.axiom(bName, sort1)
    f.axiom(valueName, b)
    f.definition(binaryName, sort1, binary)
    f.axiom(returnsName, returnsType)
    f.definition(partialName, unary, partial)

    imported(f)
  }

  test("semantic expected types accept synonyms and eta-contracted lambda chains") {
    val f = new ExportBuilder
    val bName = f.name("B")
    val xName = f.name("x")
    val yName = f.name("y")
    val gName = f.name("g")
    val aliasName = f.name("Fn")
    val idName = f.name("aliasId")
    val contractedName = f.name("contracted")
    val sort1 = f.sort(f.levelSucc(0))
    val b = f.const(bName)
    val unary = f.forall(xName, b, b)
    val binary = f.forall(xName, b, f.forall(yName, b, b))
    val alias = f.const(aliasName)
    val identity = f.lam(xName, b, f.bvar(0))
    val contracted = f.lam(xName, b, f.const(gName))
    f.axiom(bName, sort1)
    f.axiom(gName, unary)
    f.definition(aliasName, sort1, unary)
    f.definition(idName, alias, identity)
    f.definition(contractedName, binary, contracted)

    imported(f)
  }

  test("metadata is transparent while peeling declaration Pi and lambda spines") {
    val f = new ExportBuilder
    val bName = f.name("B")
    val xName = f.name("x")
    val idName = f.name("metadataId")
    val sort1 = f.sort(f.levelSucc(0))
    val b = f.const(bName)
    val unary = f.forall(xName, b, b)
    val identity = f.lam(xName, b, f.bvar(0))
    f.axiom(bName, sort1)
    f.definition(idName, f.mdata(unary), f.mdata(identity))

    val result = imported(f)
    result.env("metadataId") match {
      case Value.VLam(_, Value.ValueId.Const("metadataId"), _) =>
      case other => fail(s"monomorphic declaration lambda lost its name: $other")
    }
  }

  test("a lambda retains its declaration name when the declared function type is an alias") {
    val f = new ExportBuilder
    val bName = f.name("B")
    val xName = f.name("x")
    val aliasName = f.name("Fn")
    val idName = f.name("aliasNamedId")
    val sort1 = f.sort(f.levelSucc(0))
    val b = f.const(bName)
    val unary = f.forall(xName, b, b)
    val identity = f.lam(xName, b, f.bvar(0))
    f.axiom(bName, sort1)
    f.definition(aliasName, sort1, unary)
    f.definition(idName, f.const(aliasName), identity)

    val result = imported(f)
    result.env("aliasNamedId") match {
      case Value.VLam(_, Value.ValueId.Const("aliasNamedId"), _) =>
      case other => fail(s"alias-typed declaration lambda lost its name: $other")
    }
  }

  test("a failure after reading does not blame the last installed declaration") {
    val f = new ExportBuilder
    val bName = f.name("B")
    val sort1 = f.sort(f.levelSucc(0))
    f.axiom(bName, sort1)
    val input = new ByteArrayInputStream(f.bytes) {
      override def close(): Unit = throw new java.io.IOException("synthetic close failure")
    }

    val errors = LeanImportSession
      .importStream(input, "post-read-failure.ndjson")
      .swap
      .getOrElse(fail("post-read stream failure unexpectedly imported"))
    assertEquals(errors.length, 1)
    val error = errors.head
    assert(error.isInstanceOf[DeclarationTypeError])
    assertEquals(error.provenance.line, 0L)
    assertEquals(error.provenance.kind, "import")
    assertEquals(error.declaration, None)
  }

  test("deep right-nested arguments fail with a bounded diagnostic instead of overflowing") {
    val f = new ExportBuilder
    val bName = f.name("B")
    val xName = f.name("x")
    val fnName = f.name("step")
    val valueName = f.name("value")
    val deepName = f.name("deep")
    val sort1 = f.sort(f.levelSucc(0))
    val b = f.const(bName)
    val unary = f.forall(xName, b, b)
    var body = f.const(valueName)
    var depth = 0
    while (depth < 600) {
      body = f.app(f.const(fnName), body)
      depth += 1
    }
    f.axiom(bName, sort1)
    f.axiom(fnName, unary)
    f.axiom(valueName, b)
    f.definition(deepName, b, body)

    val errors = f.result.swap.getOrElse(fail("deep expression unexpectedly imported"))
    assert(errors.exists(error => error.isInstanceOf[BodyLowering] && error.message.contains("nesting exceeds")))
    assert(errors.forall(_.getMessage.length <= 4096))
  }

  test("deep expected-type recursion through let values consumes the lowering depth budget") {
    val f = new ExportBuilder
    val bName = f.name("B")
    val valueName = f.name("value")
    val letName = f.name("nested")
    val deepName = f.name("deepLetValue")
    val sort1 = f.sort(f.levelSucc(0))
    val b = f.const(bName)
    val value = f.const(valueName)
    var nested = value
    var depth = 0
    while (depth < 600) {
      nested = f.let(letName, b, nested, value, nonDependent = true)
      depth += 1
    }
    f.axiom(bName, sort1)
    f.axiom(valueName, b)
    f.definition(deepName, b, nested)

    val errors = f.result.swap.getOrElse(fail("deep expected-type recursion unexpectedly imported"))
    assert(errors.exists(error => error.isInstanceOf[BodyLowering] && error.message.contains("nesting exceeds")))
  }

  test("nondependent-let analysis visits shared expression nodes once per binder depth") {
    val f = new ExportBuilder
    val bName = f.name("B")
    val valueName = f.name("value")
    val letName = f.name("unused")
    val badName = f.name("sharedBadBVar")
    val sort1 = f.sort(f.levelSucc(0))
    val b = f.const(bName)
    var shared = f.bvar(1)
    var depth = 0
    while (depth < 28) {
      shared = f.app(shared, shared)
      depth += 1
    }
    val body = f.let(letName, b, f.const(valueName), shared, nonDependent = true)
    f.axiom(bName, sort1)
    f.axiom(valueName, b)
    f.definition(badName, b, body)

    val errors = f.result.swap.getOrElse(fail("out-of-scope shared bvar unexpectedly imported"))
    assert(errors.exists(_.isInstanceOf[BadBVar]))
  }

  test("Core substitution rejects a replacement that would be captured") {
    val span = Span(0, 1)
    val x = CoreAst.LocalRef(20000, "x")
    val y = CoreAst.LocalRef(20001, "y")
    val term = CoreAst.Term.Pi(
      Vector(CoreAst.Binder(y, CoreAst.Term.GlobalRef("Type", span), span)),
      CoreAst.Term.LocalRef(x, span),
      span
    )
    intercept[WTF](
      CoreSubstitution.substitute(
        term,
        Map(x -> CoreAst.Term.LocalRef(y, span))
      )
    )
  }
}
