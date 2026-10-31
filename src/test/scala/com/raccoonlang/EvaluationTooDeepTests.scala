package com.raccoonlang

import com.raccoonlang.ProgramFixtures.Programs

/**
 * Evaluation depth (docs/kernel.md, "Evaluation depth"): a host stack overflow while checking a declaration, or while
 * checking, evaluating or printing the program's body, is `EvaluationTooDeep`, located at the whole declaration or
 * body. The programs run on a 4 MiB stack, so they overflow alike on every machine.
 */
class EvaluationTooDeepTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = true)
  import programs._

  private def onSmallStack[T](body: => T): T = Execution.onStack(4L << 20)(body)

  /** `count`, whose recursive call is an argument, not in tail position. */
  private val count =
    """
      |def count (n: Nat) : Nat decreases structural(n) := {
      |  match n returning Nat with
      |  | Nat.zero => 0
      |  | Nat.succ k => Nat.succ(count(k))
      |}
      |
      |""".stripMargin

  test("a declaration whose checking exhausts the stack is EvaluationTooDeep at the declaration") {
    onSmallStack(
      assertErrorAt[EvaluationTooDeep](
        count + "def big : Nat := count(100000)\n\nNat.zero\n",
        "def big : Nat := count(100000)"
      )
    )
  }

  test("a body whose evaluation exhausts the stack is EvaluationTooDeep at the body") {
    onSmallStack(assertErrorAt[EvaluationTooDeep](count + "count(100000)\n", "count(100000)"))
  }

  test("a result whose printing forces a proof too deep for the stack is EvaluationTooDeep at the body") {
    val src =
      """
        |def deep (n: Nat) : True decreases structural(n) := {
        |  match n returning True with
        |  | Nat.zero => True.intro
        |  | Nat.succ k => {
        |    let h := deep(k)
        |    h
        |  }
        |}
        |
        |Fact.mk(deep(100000))
        |""".stripMargin
    onSmallStack {
      // The body evaluates to a fact over an undemanded proof call, which only printing forces.
      val result = runProgram(src)
      val body = Span(src.indexOf("Fact.mk"), src.indexOf("Fact.mk") + "Fact.mk(deep(100000))".length)
      val error = intercept[EvaluationTooDeep](Interpreter.show(result, body))
      assertEquals(error.span, Some(body))
    }
  }

  test("an overflow while a demanded proof runs leaves later proof calls suspended") {
    val deep =
      """
        |def deep (n: Nat) : True decreases structural(n) := {
        |  match n returning True with
        |  | Nat.zero => True.intro
        |  | Nat.succ k => {
        |    let h := deep(k)
        |    h
        |  }
        |}
        |
        |""".stripMargin
    onSmallStack {
      // The match, a large elimination, demands the proof, which overflows while it runs.
      val demanded =
        deep + "def t : Nat := {\n  match deep(100000) returning Nat with\n  | True.intro => 0\n}\n"
      intercept[EvaluationTooDeep](runChecked(demanded + "Nat.zero\n"))
      // Nothing demands this one, so it only checks if proof calls are suspended again.
      assertEquals(result(deep + "def t : True := deep(100000)\n\nNat.zero\n"), "0")
    }
  }

  test("a --stack size is a positive number of bytes, KiB, MiB or GiB, as -Xss reads it") {
    assertEquals(Main.parseStackSize("4096"), Some(4096L))
    assertEquals(Main.parseStackSize("512k"), Some(512L << 10))
    assertEquals(Main.parseStackSize("256M"), Some(256L << 20))
    assertEquals(Main.parseStackSize("1g"), Some(1L << 30))
    assertEquals(Main.parseStackSize("0"), None)
    assertEquals(Main.parseStackSize("12x"), None)
    assertEquals(Main.parseStackSize("-1m"), None)
    assertEquals(Main.parseStackSize("99999999999999999999"), None)
    assertEquals(Main.parseStackSize("9000000000g"), None)
  }
}
