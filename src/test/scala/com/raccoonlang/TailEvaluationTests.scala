package com.raccoonlang

class TailEvaluationTests extends munit.FunSuite with TestSupport {
  private val SmallStack = 2L << 20
  private val Steps = 50000

  private val countSource =
    """
      |def count (n: Nat): Bool decreases structural(n) := {
      |  match n returning Bool with
      |  | Nat.zero => Bool.true
      |  | Nat.succ smaller => {
      |    let next := smaller
      |    count(next)
      |  }
      |}
      |""".stripMargin

  private lazy val env: Env =
    parse(countSource).decls.foldLeft(suitePrelude.checkedEnv) { (current, decl) =>
      Interpreter.evalDecl(decl, current)
    }

  /** Build a constructor chain outside the constrained thread, without a source numeral or native shortcut. */
  private def natural(value: Env, size: Int): Value = {
    var result = value("Nat.zero")
    val succ = value("Nat.succ")
    var remaining = 0
    while (remaining < size) {
      result = Interpreter.evalApply(succ, Vector(result))
      remaining += 1
    }
    result
  }

  test("tail calls through a match branch and block result run in a 2MB stack") {
    val checked = env
    val input = natural(checked, Steps)
    val result = Execution.onStack(SmallStack) {
      Interpreter.evalApply(checked("count"), Vector(input))
    }
    assertEquals(ctorName(result), "Bool.true")
  }

  test("runLam uses the same tail loop as evalApply") {
    val checked = env
    val function = checked("count").asInstanceOf[Value.VLam]
    val input = natural(checked, Steps)
    val result = Execution.onStack(SmallStack) {
      Interpreter.runLam(function, Vector(input))
    }
    assertEquals(ctorName(result), "Bool.true")
  }
}
