package com.raccoonlang

class AxiomTests extends munit.FunSuite {
  private def runProgram(src: String): Value =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core).getOrElse(fail("Program has no body"))
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def typecheckDecls(src: String): Unit =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private val natPrelude =
    """
      |inductive Nat : Type
      | | zero : Nat
      | | succ (_: Nat) : Nat
      |
      |""".stripMargin

  test("axiom declares an opaque constant") {
    val res = runProgram(
      natPrelude +
        """
          |axiom magicNat : Nat
          |
          |{
          |  magicNat
          |}
          |""".stripMargin
    )

    assertEquals(PrettyPrinter.print(res), "magicNat")
    assertEquals(PrettyPrinter.print(res.tpe), "Nat")
  }

  test("parameterized axiom can be applied") {
    val res = runProgram(
      natPrelude +
        """
          |axiom choose (A: Type)(x: A): A
          |
          |{
          |  choose(Nat, Nat.zero)
          |}
          |""".stripMargin
    )

    assertEquals(PrettyPrinter.print(res), "choose(Nat, Nat.zero)")
    assertEquals(PrettyPrinter.print(res.tpe), "Nat")
  }

  test("axiom instance participates in derive") {
    val res = runProgram(
      natPrelude +
        """
          |struct Eq (A: Type) : Type
          | | mk (ok: Nat) : Eq(A)
          |
          |axiom instance natEq : Eq(Nat)
          |
          |{
          |  derive[Eq(Nat)]
          |}
          |""".stripMargin
    )

    assertEquals(PrettyPrinter.print(res), "natEq")
  }

  test("axiom result must be a type") {
    val p =
      natPrelude +
        """
          |axiom bad : Nat.zero
          |""".stripMargin

    intercept[NotAType] {
      typecheckDecls(p)
    }
  }
}
