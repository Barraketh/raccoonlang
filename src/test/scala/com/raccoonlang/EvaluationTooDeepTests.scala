package com.raccoonlang

/**
 * Stack exhaustion is a diagnostic (PROOF_BY_EVALUATION §2.5): an overflow while checking a declaration, or while
 * evaluating the program's result, is `EvaluationTooDeep` located there, and checking stops. Programs are checked on a
 * thread of a stack chosen here, so what overflows does not depend on the JVM's default.
 */
class EvaluationTooDeepTests extends munit.FunSuite with TestSupport {
  private val SmallStack = 512L << 10
  private val LargeStack = 256L << 20

  /** Core non-tail calls now use reusable frames and can exceed a small Java stack. */
  private val count =
    """def count (n: Nat): Nat decreases structural(n) := {
      |  match n returning Nat with
      |  | Nat.zero => Nat.zero
      |  | Nat.succ k => Nat.succ(count(k))
      |}
      |""".stripMargin

  /** Classifying each dependent Pi still recurses through the checker and its semantic helpers. */
  private val nest =
    """def nest (n: Nat): Type decreases structural(n) := {
      |  match n returning Type with
      |  | Nat.zero => Nat
      |  | Nat.succ k => (x: Nat) -> nest(k)
      |}
      |""".stripMargin

  /**
   * `source` checked and run on a thread of `stackBytes`. The suite's prelude is built on this thread first, so that
   * only the program meets the chosen stack.
   */
  private def runOn(stackBytes: Long, source: String): Option[Value] = {
    suitePrelude.checkedEnv
    val elaborated = Elaborator.elaborate(parseSurface(source), suitePrelude)
    Execution.onStack(stackBytes)(Interpreter.run(TypeChecker.check(elaborated)))
  }

  /** Each diagnostic as its error, the source text it is located at, and its frames. */
  private def located(source: String, diagnostics: Vector[Diagnostic]): Vector[(TypeError, String, Vector[Frame])] =
    diagnostics.map { diagnostic =>
      (
        diagnostic.error,
        diagnostic.span.fold("<nowhere>")(span => source.substring(span.start, span.end)),
        diagnostic.frames
      )
    }

  test("deep recursion that a declaration's type evaluates is EvaluationTooDeep at that declaration") {
    val deep = "def deep : Type := nest(100000)"
    val source = nest + deep + "\n"
    assertEquals(
      located(source, interceptDiagnostics(runOn(SmallStack, source))),
      Vector((EvaluationTooDeep, deep, Vector(Frame.InDefinition("deep"))))
    )
  }

  test("deep recursion while evaluating the program's result is EvaluationTooDeep at the result") {
    // The result is the block's contents, as the parser locates a program's body.
    val result = "nest(100000)"
    val source = nest + "{\n  " + result + "\n}\n"
    val diagnostics = interceptDiagnostics(runOn(SmallStack, source))
    assertEquals(located(source, diagnostics), Vector((EvaluationTooDeep, result, Vector.empty)))
  }

  test("checking stops at EvaluationTooDeep, reporting what it found before and nothing after") {
    val source =
      nest +
        """def before : Nat := Bool.true
          |def deep : Type := nest(100000)
          |def after : Nat := Bool.false
          |{ nest(100000) }
          |""".stripMargin
    val diagnostics = interceptDiagnostics(runOn(SmallStack, source))
    assertEquals(
      diagnostics.map(_.frames),
      Vector(Vector(Frame.InDefinition("before")), Vector(Frame.InDefinition("deep")))
    )
    assert(diagnostics.head.error.isInstanceOf[TypeMismatch], diagnostics.head.error)
    assertEquals(diagnostics.last.error, EvaluationTooDeep)
  }

  test("a program within the stack checks and runs on it as on any other") {
    val source = count + "def small : Eq(Nat, count(10), 10) := Eq.refl(10)\n{ count(10) }\n"
    assertEquals(runOn(SmallStack, source).map(PrettyPrinter.print), Some("10"))
  }

  test("explicit non-tail frames evaluate deeply on a small physical stack") {
    val source = count + "{ count(20000) }\n"
    assertEquals(runOn(SmallStack, source).map(PrettyPrinter.print), Some("20000"))
    assertEquals(runOn(LargeStack, source).map(PrettyPrinter.print), Some("20000"))
  }

  test("an overflow in a prelude declaration is EvaluationTooDeep at that declaration") {
    // Literals wait for the completed prelude, so the depth is built by doubling: 2^20.
    val deep = "def deep : Type := nest(" + "double(" * 20 + "Nat.succ(Nat.zero)" + ")" * 20 + ")"
    val double =
      """def double (n: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ k => Nat.succ(Nat.succ(double(k)))
        |}
        |""".stripMargin
    val prelude = TestSupport.preludeAssuming(TestSupport.bundledPreludeSource, nest + double + deep)
    val source = TestSupport.preludeSourceAssuming(TestSupport.bundledPreludeSource, nest + double + deep)
    assertEquals(
      located(source, Vector(interceptDiagnostic(Execution.onStack(SmallStack)(prelude.checkedEnv)))),
      Vector((EvaluationTooDeep, deep, Vector(Frame.InDefinition("deep"))))
    )
  }
}
