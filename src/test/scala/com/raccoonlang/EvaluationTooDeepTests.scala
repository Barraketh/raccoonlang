package com.raccoonlang

/** Stack exhaustion is located at the declaration or program body and stops checking. */
class EvaluationTooDeepTests extends munit.FunSuite with TestSupport {
  private val SmallStack = 2L << 20
  private val PreparationStack = 128L << 20

  private val deepPreludeSource =
    TestSupport.bundledPreludeSource +
      """
        |
        |def build (n: Nat)(acc: List(Nat)): List(Nat) decreases structural(n) := {
        |  match n returning List(Nat) with
        |  | Nat.zero => acc
        |  | Nat.succ smaller => build(smaller, List.cons(smaller, acc))
        |}
        |
        |def countList (xs: List(Nat)): Nat decreases structural(xs) := {
        |  match xs returning Nat with
        |  | List.nil => Nat.zero
        |  | List.cons head tail => Nat.succ(countList(tail))
        |}
        |
        |def huge : List(Nat) := build(12000, List.nil(Nat))
        |""".stripMargin

  private lazy val deepPrelude = Prelude.fromSource("deep-stack-test-prelude", deepPreludeSource)

  /** Build and cache the deep prelude on a roomy worker before testing a smaller program stack. */
  private def preparePrelude(): Unit = {
    Execution.onStack(PreparationStack)(deepPrelude.checkedEnv)
    ()
  }

  private def runOnSmallStack(source: String): Unit = {
    preparePrelude()
    val surface = parseSurface(source)
    Execution.onStack(SmallStack) {
      TypeChecker.check(Elaborator.elaborate(surface, deepPrelude))
    }
    ()
  }

  private def spanText(source: String, diagnostic: Diagnostic): String =
    diagnostic.span.fold("<nowhere>")(span => source.substring(span.start, span.end))

  test("overflow while checking a declaration's type becomes a located diagnostic") {
    val declaration = "def deep : Eq(Nat, countList(huge), Nat.zero) := Eq.refl(Nat.zero)"
    val source = declaration + "\n"
    val diagnostic = interceptDiagnostic(runOnSmallStack(source))
    assertEquals(diagnostic.error, EvaluationTooDeep)
    assertEquals(spanText(source, diagnostic), declaration)
    assertEquals(diagnostic.frames, Vector(Frame.InDefinition("deep")))
  }

  test("overflow while checking the program body becomes a located diagnostic") {
    val body = "countList(huge)"
    val source = "{ " + body + " }\n"
    val diagnostic = interceptDiagnostic(runOnSmallStack(source))
    assertEquals(diagnostic.error, EvaluationTooDeep)
    assertEquals(spanText(source, diagnostic), body)
    assertEquals(diagnostic.frames, Vector.empty)
  }

  test("checking stops after a declaration overflow and does not publish later declarations") {
    val deep = "def deep : Eq(Nat, countList(huge), Nat.zero) := Eq.refl(Nat.zero)"
    val source =
      "def before : Nat := Bool.true\n" +
        deep + "\n" +
        "def after : Nat := Bool.false\n" +
        "{ Nat.zero }\n"
    preparePrelude()
    val diagnostics = interceptDiagnostics {
      val surface = parseSurface(source)
      Execution.onStack(SmallStack) {
        TypeChecker.check(Elaborator.elaborate(surface, deepPrelude))
      }
    }
    assertEquals(diagnostics.map(_.error.isInstanceOf[TypeMismatch]), Vector(true, false))
    assertEquals(
      diagnostics.map(_.frames.collect { case Frame.InDefinition(name) => name }),
      Vector(Vector("before"), Vector("deep"))
    )
    assertEquals(diagnostics.last.error, EvaluationTooDeep)
  }
}
