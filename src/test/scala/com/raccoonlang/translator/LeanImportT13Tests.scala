package com.raccoonlang.translator

import com.raccoonlang._
import com.raccoonlang.translator.LeanExportIr._

import java.io.ByteArrayInputStream
import java.nio.charset.StandardCharsets

class LeanImportT13Tests extends munit.FunSuite {
  private val meta =
    s"""{"meta":{"exporter":{"name":"${LeanExportReader.ExporterName}","version":"${LeanExportReader.ExporterVersion}"},"lean":{"githash":"${LeanExportReader.LeanGitHash}","version":"${LeanExportReader.LeanVersion}"},"format":{"version":"${LeanExportReader.FormatVersion}"}}}"""

  private val fixture = Vector(
    meta,
    """{"str":{"pre":0,"str":"u"},"in":1}""",
    """{"str":{"pre":0,"str":"A"},"in":2}""",
    """{"str":{"pre":0,"str":"x"},"in":3}""",
    """{"str":{"pre":0,"str":"polyId"},"in":4}""",
    """{"str":{"pre":0,"str":"Carrier"},"in":5}""",
    """{"str":{"pre":0,"str":"carrierValue"},"in":6}""",
    """{"str":{"pre":0,"str":"useId"},"in":7}""",
    """{"str":{"pre":0,"str":"idAtCarrier"},"in":8}""",
    """{"str":{"pre":0,"str":"ignoreA"},"in":9}""",
    """{"str":{"pre":0,"str":"useIgnore"},"in":10}""",
    """{"str":{"pre":0,"str":"ignoreAPartial"},"in":11}""",
    """{"str":{"pre":0,"str":"strictArg"},"in":12}""",
    """{"str":{"pre":0,"str":"instanceArg"},"in":13}""",
    """{"str":{"pre":0,"str":"polyAlias"},"in":14}""",
    """{"str":{"pre":0,"str":"v"},"in":15}""",
    """{"str":{"pre":0,"str":"PolyPair"},"in":16}""",
    """{"param":1,"il":1}""",
    """{"succ":0,"il":2}""",
    """{"param":15,"il":3}""",
    """{"max":[1,3],"il":4}""",
    """{"sort":1,"ie":0}""",
    """{"bvar":0,"ie":1}""",
    """{"bvar":1,"ie":2}""",
    """{"forallE":{"name":3,"type":1,"body":2,"binderInfo":"default"},"ie":3}""",
    """{"forallE":{"name":2,"type":0,"body":3,"binderInfo":"implicit"},"ie":4}""",
    """{"lam":{"name":3,"type":1,"body":1,"binderInfo":"default"},"ie":5}""",
    """{"lam":{"name":2,"type":0,"body":5,"binderInfo":"implicit"},"ie":6}""",
    """{"sort":2,"ie":7}""",
    """{"const":{"name":5,"us":[]},"ie":8}""",
    """{"const":{"name":6,"us":[]},"ie":9}""",
    """{"const":{"name":4,"us":[2]},"ie":10}""",
    """{"app":{"fn":10,"arg":8},"ie":11}""",
    """{"app":{"fn":11,"arg":9},"ie":12}""",
    """{"forallE":{"name":3,"type":8,"body":8,"binderInfo":"default"},"ie":13}""",
    """{"forallE":{"name":2,"type":7,"body":13,"binderInfo":"implicit"},"ie":14}""",
    """{"lam":{"name":3,"type":8,"body":1,"binderInfo":"default"},"ie":15}""",
    """{"lam":{"name":2,"type":7,"body":15,"binderInfo":"implicit"},"ie":16}""",
    """{"const":{"name":9,"us":[]},"ie":17}""",
    """{"app":{"fn":17,"arg":8},"ie":18}""",
    """{"app":{"fn":18,"arg":9},"ie":19}""",
    """{"forallE":{"name":2,"type":7,"body":13,"binderInfo":"strictImplicit"},"ie":20}""",
    """{"forallE":{"name":2,"type":7,"body":13,"binderInfo":"instImplicit"},"ie":21}""",
    """{"const":{"name":4,"us":[1]},"ie":22}""",
    """{"sort":3,"ie":23}""",
    """{"sort":4,"ie":24}""",
    """{"forallE":{"name":2,"type":23,"body":24,"binderInfo":"default"},"ie":25}""",
    """{"forallE":{"name":2,"type":0,"body":25,"binderInfo":"default"},"ie":26}""",
    """{"axiom":{"name":5,"levelParams":[],"type":7,"isUnsafe":false}}""",
    """{"axiom":{"name":6,"levelParams":[],"type":8,"isUnsafe":false}}""",
    """{"def":{"name":4,"levelParams":[1],"type":4,"value":6,"hints":{"regular":1},"safety":"safe","all":[4]}}""",
    """{"def":{"name":14,"levelParams":[1],"type":4,"value":22,"hints":"abbrev","safety":"safe","all":[14]}}""",
    """{"def":{"name":7,"levelParams":[],"type":8,"value":12,"hints":"abbrev","safety":"safe","all":[7]}}""",
    """{"def":{"name":8,"levelParams":[],"type":13,"value":11,"hints":"abbrev","safety":"safe","all":[8]}}""",
    """{"def":{"name":9,"levelParams":[],"type":14,"value":16,"hints":{"regular":1},"safety":"safe","all":[9]}}""",
    """{"def":{"name":10,"levelParams":[],"type":8,"value":19,"hints":"abbrev","safety":"safe","all":[10]}}""",
    """{"def":{"name":11,"levelParams":[],"type":14,"value":17,"hints":"abbrev","safety":"safe","all":[11]}}""",
    """{"axiom":{"name":12,"levelParams":[],"type":20,"isUnsafe":false}}""",
    """{"axiom":{"name":13,"levelParams":[],"type":21,"isUnsafe":false}}""",
    """{"axiom":{"name":16,"levelParams":[1,15],"type":26,"isUnsafe":false}}"""
  ).mkString("\n")

  private def imported(text: String = fixture): Either[Vector[LeanImportDiagnostic], LeanImportResult] =
    LeanImportSession.importStream(new ByteArrayInputStream(text.getBytes(StandardCharsets.UTF_8)), "t13.ndjson")

  test("full source arguments validate implicits and produce saturated Core applications") {
    val result = imported().fold(errors => fail(errors.map(_.message).mkString("; ")), identity)
    assert(ValueEquivalence.defEq(result.env("useId"), result.env("carrierValue")))
    assert(ValueEquivalence.defEq(result.env("useIgnore"), result.env("carrierValue")))

    val span = Span(0, 1)
    val aliasApplied = TypeChecker
      .checkTerm(
        CoreAst.Term
          .App(CoreAst.Term.GlobalRef("polyAlias", span), Vector(CoreAst.Term.GlobalRef("carrierValue", span)), span),
        result.env
      )
      .value
    assert(ValueEquivalence.defEq(aliasApplied, result.env("carrierValue")))

    val idConvention = result.manifest.installed.find(_.name == "polyId").flatMap(_.callingConvention).get
    assertEquals(idConvention.universeCount, 1)
    assertEquals(
      idConvention.telescopes.head.binders.map(b => b.requestedImplicit -> b.checkedImplicit),
      Vector(true -> true, true -> true, false -> false)
    )
    assertEquals(result.manifest.installed.find(_.name == "PolyPair").flatMap(_.callingConvention).get.universeCount, 2)

    val ignored = result.manifest.installed.find(_.name == "ignoreA").flatMap(_.callingConvention).get
    assertEquals(
      ignored.telescopes.head.binders.map(b => b.requestedImplicit -> b.checkedImplicit),
      Vector(true -> false, false -> false)
    )
  }

  test("underapplications before and after an implicit eta-expand to checked functions") {
    val result = imported().fold(errors => fail(errors.map(_.message).mkString("; ")), identity)
    val span = Span(0, 1)
    val idApplied = TypeChecker
      .checkTerm(
        CoreAst.Term
          .App(CoreAst.Term.GlobalRef("idAtCarrier", span), Vector(CoreAst.Term.GlobalRef("carrierValue", span)), span),
        result.env
      )
      .value
    assert(ValueEquivalence.defEq(idApplied, result.env("carrierValue")))

    val partialApplied = TypeChecker
      .checkTerm(
        CoreAst.Term.App(
          CoreAst.Term.GlobalRef("ignoreAPartial", span),
          Vector(CoreAst.Term.GlobalRef("Carrier", span), CoreAst.Term.GlobalRef("carrierValue", span)),
          span
        ),
        result.env
      )
      .value
    assert(ValueEquivalence.defEq(partialApplied, result.env("carrierValue")))
  }

  test("strict and instance implicits retain source metadata but demote when unforced") {
    val result = imported().fold(errors => fail(errors.map(_.message).mkString("; ")), identity)
    val strict = result.manifest.installed
      .find(_.name == "strictArg")
      .flatMap(_.callingConvention)
      .get
      .telescopes
      .head
      .binders
      .head
    val instance = result.manifest.installed
      .find(_.name == "instanceArg")
      .flatMap(_.callingConvention)
      .get
      .telescopes
      .head
      .binders
      .head
    assertEquals(strict.sourceInfo, SourceTermBinder(StrictImplicit))
    assertEquals(instance.sourceInfo, SourceTermBinder(InstImplicit))
    assert(!strict.checkedImplicit && !instance.checkedImplicit)
  }

  test("wrong universe arity and inconsistent supplied arguments fail before publication") {
    val wrongArity =
      fixture.replace("""{"const":{"name":4,"us":[2]},"ie":10}""", """{"const":{"name":4,"us":[]},"ie":10}""")
    assert(imported(wrongArity).swap.toOption.get.exists(_.isInstanceOf[ApplicationConventionMismatch]))

    val wrongUniverse =
      fixture.replace("""{"const":{"name":4,"us":[2]},"ie":10}""", """{"const":{"name":4,"us":[0]},"ie":10}""")
    assert(imported(wrongUniverse).isLeft)
  }

  test("supplied implicit validation rejects a projected value after both arguments typecheck") {
    var tables: ExportTables = null
    val input = s"$meta\n" + """{"sort":0,"ie":0}"""
    LeanExportReader.read(
      new ByteArrayInputStream(input.getBytes(StandardCharsets.UTF_8)),
      "implicit-mismatch.ndjson",
      new LeanExportConsumer {
        def onMeta(meta: ExportMeta): Unit = ()
        def onDeclaration(decl: ExportDecl, current: ExportTables): Unit = ()
        def finish(current: ExportTables): Unit = tables = current
      }
    )

    val base = LeanImportBootstrap.build().fold(errors => fail(errors.map(_.message).mkString("; ")), identity)
    val env = base
      .putGlobal("B", Value.VConst("B", Value.Symbol, Value.TypeTpe))
      .putGlobal("C", Value.VConst("C", Value.Symbol, Value.TypeTpe))
    val span = Span(0, 1)
    val aRef = CoreAst.LocalRef(10000, "A")
    val xRef = CoreAst.LocalRef(10001, "X")
    val typeTerm = ElabAst.Term.GlobalRef("Type", span)
    val binders = Vector(
      ElabAst.Binder(
        aRef,
        typeTerm,
        span,
        isImplicit = true,
        projection = Some(com.raccoonlang.telescope.Projection.Spec(0, Vector.empty))
      ),
      ElabAst.Binder(xRef, typeTerm, span)
    )
    val pi = Value.VPi(
      env,
      binders,
      _ => Value.TypeTpe,
      DepSet.empty,
      Value.ValueId.Const("mismatch.pi"),
      () => Value.VSort(Value.Level.const(2))
    )
    val lowerer = new LeanTermLowerer(tables, env, LeanGlobalRegistry.empty, "mismatch")
    val context = LeanTermLowerer.Context(Vector.empty, Map.empty, env)
    intercept[SuppliedImplicitMismatch](
      lowerer.checkSourceArguments(
        pi,
        Vector(
          Left(CoreAst.Term.GlobalRef("B", span)),
          Left(CoreAst.Term.GlobalRef("C", span))
        ),
        context,
        ExprId(0),
        requireAllProjections = true
      )
    )
  }
}
