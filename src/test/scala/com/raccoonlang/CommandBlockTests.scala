package com.raccoonlang

class CommandBlockTests extends munit.FunSuite with TestSupport {
  test("library composition determines sequencing and association") {
    val source = """
                   |def join (a: Nat)(b: Nat): Nat := Nat.add(Nat.mul(a, 10), b)
                   |command join {
                   |  1
                   |  2
                   |  3
                   |}
                   |""".stripMargin
    assertEquals(PrettyPrinter.print(runProgram(source)), "33")
  }

  test("lets and opens scope over the remaining commands; nested blocks compose") {
    val source = """
                   |namespace Numbers {
                   |  def two: Nat := 2
                   |}
                   |command Nat.add {
                   |  1
                   |  open Numbers
                   |  let n := two
                   |  command Nat.add {
                   |    n
                   |    // The same line separator rules apply to command blocks.
                   |
                   |    3
                   |  }
                   |  n
                   |}
                   |""".stripMargin
    assertEquals(PrettyPrinter.print(runProgram(source)), "8")
  }

  test("command remains an ordinary identifier outside block notation") {
    val source = """
                   |def command (n: Nat): Nat := Nat.succ(n)
                   |command(4)
                   |""".stripMargin
    assertEquals(PrettyPrinter.print(runProgram(source)), "5")
  }

  test("indexed composition rejects a mismatched intermediate state") {
    val source = """
                   |inductive State: Type
                   | | empty: State
                   | | full: State
                   |inductive Action (a: State)(b: State): Type { kind = lin }
                   | | mk: Action(a, b)
                   |def join {a: State}{m: State}{b: State}(first: Action(a, m))(next: Action(m, b)): Action(a, b) := {
                   |  match first returning Action(a, b) with
                   |  | .mk => match next returning Action(a, b) with
                   |    | .mk => Action.mk(a, b)
                   |}
                   |command join {
                   |  Action.mk(State.empty, State.full)
                   |  Action.mk(State.empty, State.full)
                   |}
                   |""".stripMargin
    expectTypeError[TypeMismatch](source)
  }

  test("a command block does not weaken ordinary linear consumption") {
    val source = """
                   |inductive Token: Type { kind = lin }
                   | | mk: Token
                   |def join (a: Token)(b: Token): Token := {
                   |  match a returning Token with
                   |  | .mk => b
                   |}
                   |{
                   |  let token := Token.mk
                   |  command join {
                   |    token
                   |    token
                   |  }
                   |}
                   |""".stripMargin
    expectTypeError[LinearReused](source)
  }

  test("empty blocks and blocks ending in a binding are rejected") {
    for (source <- Vector("command Nat.add {}", "command Nat.add { let n := 1 }")) {
      val failure = LanguageParser.parseProgram(source).asInstanceOf[Failure]
      assert(failure.message.contains("A command block ends with a command"))
    }
  }
}
