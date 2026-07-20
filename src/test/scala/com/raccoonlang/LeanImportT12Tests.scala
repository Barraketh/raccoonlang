package com.raccoonlang

import com.raccoonlang.CoreAst.Term
import com.raccoonlang.LeanExportIr._

import java.io.ByteArrayInputStream
import java.nio.charset.StandardCharsets

class LeanImportT12Tests extends munit.FunSuite {
  private val meta =
    s"""{"meta":{"exporter":{"name":"${LeanExportReader.ExporterName}","version":"${LeanExportReader.ExporterVersion}"},"lean":{"githash":"${LeanExportReader.LeanGitHash}","version":"${LeanExportReader.LeanVersion}"},"format":{"version":"${LeanExportReader.FormatVersion}"}}}"""

  private val fixture = Vector(
    meta,
    """{"str":{"pre":0,"str":"u"},"in":1}""",
    """{"str":{"pre":0,"str":"A"},"in":2}""",
    """{"str":{"pre":0,"str":"x"},"in":3}""",
    """{"str":{"pre":0,"str":"polyId"},"in":4}""",
    """{"str":{"pre":0,"str":"Carrier"},"in":5}""",
    """{"str":{"pre":0,"str":"carrierAlias"},"in":6}""",
    """{"str":{"pre":0,"str":"polyIdTheorem"},"in":7}""",
    """{"str":{"pre":0,"str":"carrierValue"},"in":8}""",
    """{"param":1,"il":1}""",
    """{"succ":0,"il":2}""",
    """{"sort":1,"ie":0}""",
    """{"bvar":0,"ie":1}""",
    """{"bvar":1,"ie":2}""",
    """{"forallE":{"name":3,"type":1,"body":2,"binderInfo":"default"},"ie":3}""",
    """{"forallE":{"name":2,"type":0,"body":3,"binderInfo":"default"},"ie":4}""",
    """{"lam":{"name":3,"type":1,"body":1,"binderInfo":"default"},"ie":5}""",
    """{"lam":{"name":2,"type":0,"body":5,"binderInfo":"default"},"ie":6}""",
    """{"sort":2,"ie":7}""",
    """{"const":{"name":5,"us":[]},"ie":8}""",
    """{"axiom":{"name":5,"levelParams":[],"type":7,"isUnsafe":false}}""",
    """{"axiom":{"name":8,"levelParams":[],"type":8,"isUnsafe":false}}""",
    """{"def":{"name":6,"levelParams":[],"type":7,"value":8,"hints":"abbrev","safety":"safe","all":[6]}}""",
    """{"def":{"name":4,"levelParams":[1],"type":4,"value":6,"hints":{"regular":2},"safety":"safe","all":[4]}}""",
    """{"thm":{"name":7,"levelParams":[1],"type":4,"value":6,"all":[7]}}"""
  ).mkString("\n")

  private def importText(text: String = fixture): Either[Vector[LeanImportDiagnostic], LeanImportResult] =
    LeanImportSession.importStream(new ByteArrayInputStream(text.getBytes(StandardCharsets.UTF_8)), "t12.ndjson")

  test("Lean names retain safe spellings and exotic/numeric components round-trip injectively") {
    val examples = Vector(
      Vector[Either[String, BigInt]](Left("Nat"), Left("add")),
      Vector[Either[String, BigInt]](Left("foo-bar"), Right(BigInt(12)), Left("λ")),
      Vector[Either[String, BigInt]](Left("1")),
      Vector[Either[String, BigInt]](Right(BigInt(1))),
      Vector[Either[String, BigInt]](Left("match"))
    )
    examples.foreach { components =>
      val encoded = LeanExportNames.encode(components)
      assertEquals(LeanExportNames.decode(encoded), Some(components))
    }
    assertEquals(LeanExportNames.encode(examples.head), "Nat.add")
    assertNotEquals(LeanExportNames.encode(examples(2)), LeanExportNames.encode(examples(3)))
    assert(LeanExportNames.encode(examples(4)).startsWith("$lean.name"))
  }

  test("minimal Lean bootstrap installs only the universe machinery and reserves its identities") {
    val env = LeanImportBootstrap.build().fold(errors => fail(errors.map(_.message).mkString("; ")), identity)
    Vector("Type", "Level", "Level.zero", "Level.one", "Prop", "Sort", "Level.succ", "Level.max", "Level.imax")
      .foreach(name => assert(env.globals.contains(name)))
    assert(!env.globals.contains("Nat"))
    assertEquals(ReservedNamePermit.leanImportBootstrap.names,
      Set("Sort", "Level.succ", "Level.max", "Level.imax"))

    val span = Span(0, 1)
    val replacement = CoreAst.Decl.AxiomDecl("Sort", Term.GlobalRef("Type", span), span)
    intercept[ReservedKernelName](Interpreter.evalDecl(replacement, env))
  }

  test("synthetic polymorphic axioms, definitions, and theorems import without Prelude.default") {
    val result = importText().fold(errors => fail(errors.map(_.message).mkString("; ")), identity)
    assertEquals(result.manifest.installed.map(_.name),
      Vector("Carrier", "carrierValue", "carrierAlias", "polyId", "polyIdTheorem"))
    assert(!result.env.globals.contains("Nat"))

    val span = Span(0, 1)
    val applied = TypeChecker.checkTerm(
      Term.App(Term.GlobalRef("polyId", span), Vector(Term.GlobalRef("Carrier", span), Term.GlobalRef("carrierValue", span)), span),
      result.env
    ).value
    assert(ValueEquivalence.defEq(applied, result.env("carrierValue")))
  }

  test("lambda binder annotations are validated against the declared type") {
    val corrupt = fixture.replace(
      """{"lam":{"name":3,"type":1,"body":1,"binderInfo":"default"},"ie":5}""",
      """{"lam":{"name":3,"type":0,"body":1,"binderInfo":"default"},"ie":5}"""
    )
    val errors = importText(corrupt).swap.getOrElse(fail("corrupt lambda unexpectedly imported"))
    assert(errors.exists(_.isInstanceOf[InvalidBinderMetadata]))
  }

  test("undeclared universe parameters and bad de Bruijn indices are structured failures") {
    val badLevel = fixture.replace("\"levelParams\":[1],\"type\":4", "\"levelParams\":[],\"type\":4")
    assert(importText(badLevel).swap.toOption.get.exists(_.isInstanceOf[UnknownLevelParameter]))

    val badBvar = fixture.replace("""{"bvar":1,"ie":2}""", """{"bvar":3,"ie":2}""")
    assert(importText(badBvar).swap.toOption.get.exists(_.isInstanceOf[BadBVar]))
  }
}
