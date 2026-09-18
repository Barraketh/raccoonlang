package com.raccoonlang

class ExecutionBoundaryTests extends munit.FunSuite {
  test("surface programs use the elaborated, checked, then executed pipeline") {
    val source = """
                   |inductive Nat : Type
                   | | zero : Nat
                   | | succ (n: Nat) : Nat
                   |{ Nat.succ(Nat.zero) }
                   |""".stripMargin
    val surface = LanguageParser.parseProgram(source) match {
      case Success(program, _, _) => program
      case failure                => fail(s"failed to parse: $failure")
    }

    val elaborated = Elaborator.elaborate(surface, Prelude.none)
    val checked = TypeChecker.check(elaborated)

    val result = Interpreter.run(checked)
    assert(result.nonEmpty)
    assertEquals(result, checked.result)
  }

  test("checked terms are produced by the checker and have no public case-class copy path") {
    val surface = LanguageParser.parseProgram("{ Type }") match {
      case Success(program, _, _) => program
      case failure                => fail(s"failed to parse: $failure")
    }
    val core = Elaborator.elab(surface, Prelude.none)
    val checked = TypeChecker.checkTerm(core.body.get, Prelude.none.checkedEnv)

    assert(checked.isInstanceOf[TypeChecker.CheckedTerm])
    assert(!classOf[TypeChecker.CheckedTerm].getMethods.exists(_.getName == "copy"))
  }

  test("the checker uses the prelude captured by elaboration") {
    val functionPrelude = Prelude.fromSource(
      "function-prelude",
      """
        |inductive Box : Type
        | | zero : Box
        |
        |def answer (x: Box): Box := x
        |""".stripMargin + "\n",
      Set.empty
    )
    val valuePrelude = Prelude.fromSource(
      "value-prelude",
      """
        |inductive Box : Type
        | | zero : Box
        |
        |def answer : Box := Box.zero
        |""".stripMargin + "\n",
      Set.empty
    )
    val surface = LanguageParser.parseProgram("{ answer(Box.zero) }") match {
      case Success(program, _, _) => program
      case failure                => fail(s"failed to parse: $failure")
    }

    val checked = TypeChecker.check(Elaborator.elaborate(surface, functionPrelude))
    assert(Interpreter.run(checked).nonEmpty)

    val checkMethods = TypeChecker.getClass.getMethods.filter(_.getName == "check")
    assertEquals(checkMethods.map(_.getParameterCount).toSet, Set(1))
    assert(valuePrelude.checkedEnv("answer").tpe != functionPrelude.checkedEnv("answer").tpe)
  }
}
