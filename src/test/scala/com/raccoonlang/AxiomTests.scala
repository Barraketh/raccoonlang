package com.raccoonlang

class AxiomTests extends munit.FunSuite {
  private def runProgram(src: String): Value =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test).getOrElse(fail("Program has no body"))
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def typecheckDecls(src: String): Unit =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private val natPrelude =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (_: Peano) : Peano
      |
      |""".stripMargin

  test("axiom declares an opaque constant") {
    val res = runProgram(
      natPrelude +
        """
          |axiom magicNat : Peano
          |
          |{
          |  magicNat
          |}
          |""".stripMargin
    )

    assertEquals(PrettyPrinter.print(res), "magicNat")
    assertEquals(PrettyPrinter.print(res.tpe), "Peano")
  }

  test("parameterized axiom can be applied") {
    val res = runProgram(
      natPrelude +
        """
          |axiom choose (A: Type)(x: A): A
          |
          |{
          |  choose(Peano, Peano.zero)
          |}
          |""".stripMargin
    )

    assertEquals(PrettyPrinter.print(res), "choose(Peano, Peano.zero)")
    assertEquals(PrettyPrinter.print(res.tpe), "Peano")
  }

  test("axiom result must be a type") {
    val p =
      natPrelude +
        """
          |axiom bad : Peano.zero
          |""".stripMargin

    intercept[NotAType] {
      typecheckDecls(p)
    }
  }
}
