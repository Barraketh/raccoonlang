package com.raccoonlang

/**
 * Stack exhaustion is a diagnostic (PROOF_BY_EVALUATION §2.5): an overflow while checking a declaration, or while
 * evaluating the program's result, is `EvaluationTooDeep` located there, and checking stops. Programs are checked on a
 * thread of a stack chosen here, so what overflows does not depend on the JVM's default.
 */
class EvaluationTooDeepTests extends munit.FunSuite with TestSupport {
  private val SmallStack = 512L << 10
  private val LargeStack = 256L << 20

  /** Non-tail recursion: one level of host recursion per unit of its argument. */
  private val count =
    """def count (n: Nat): Nat decreases structural(n) := {
      |  match n returning Nat with
      |  | Nat.zero => Nat.zero
      |  | Nat.succ k => Nat.succ(count(k))
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
    val deep = "def deep : Eq(Nat, count(100000), 100000) := Eq.refl(100000)"
    val source = count + deep + "\n"
    assertEquals(
      located(source, interceptDiagnostics(runOn(SmallStack, source))),
      Vector((EvaluationTooDeep, deep, Vector(Frame.InDefinition("deep"))))
    )
  }

  test("deep recursion while evaluating the program's result is EvaluationTooDeep at the result") {
    // The result is the block's contents, as the parser locates a program's body.
    val result = "let small := count(3)\n  let big := count(100000)\n  Nat.add(small, big)"
    val source = count + "{\n  " + result + "\n}\n"
    val diagnostics = interceptDiagnostics(runOn(SmallStack, source))
    assertEquals(located(source, diagnostics), Vector((EvaluationTooDeep, result, Vector.empty)))
  }

  test("checking stops at EvaluationTooDeep, reporting what it found before and nothing after") {
    val source =
      count +
        """def before : Nat := Bool.true
          |def deep : Eq(Nat, count(100000), 100000) := Eq.refl(100000)
          |def after : Nat := Bool.false
          |{ count(100000) }
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

  test("the stack a program is checked on is the one chosen") {
    val source = count + "{ count(20000) }\n"
    assertEquals(interceptDiagnostics(runOn(SmallStack, source)).map(_.error), Vector(EvaluationTooDeep))
    assertEquals(runOn(LargeStack, source).map(PrettyPrinter.print), Some("20000"))
  }

  test("an overflow in a prelude declaration is EvaluationTooDeep at that declaration") {
    // Literals wait for the completed prelude, so the depth is built by doubling: 2^20.
    val deep = "def deep : Nat := count(" + "double(" * 20 + "Nat.succ(Nat.zero)" + ")" * 20 + ")"
    val double =
      """def double (n: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ k => Nat.succ(Nat.succ(double(k)))
        |}
        |""".stripMargin
    val prelude = TestSupport.preludeAssuming(TestSupport.bundledPreludeSource, count + double + deep)
    val source = TestSupport.preludeSourceAssuming(TestSupport.bundledPreludeSource, count + double + deep)
    assertEquals(
      located(source, Vector(interceptDiagnostic(Execution.onStack(SmallStack)(prelude.checkedEnv)))),
      Vector((EvaluationTooDeep, deep, Vector(Frame.InDefinition("deep"))))
    )
  }
}
