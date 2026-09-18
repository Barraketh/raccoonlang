package com.raccoonlang

class AxiomTests extends munit.FunSuite with TestSupport {
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
          |""".stripMargin,
      Prelude.test
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
          |""".stripMargin,
      Prelude.test
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
      typecheckDecls(p, Prelude.test)
    }
  }
}
