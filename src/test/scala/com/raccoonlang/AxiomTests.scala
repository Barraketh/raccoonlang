package com.raccoonlang

class AxiomTests extends munit.FunSuite with TestSupport {
  private val peano =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (_: Peano) : Peano
      |""".stripMargin

  /** The test prelude with Peano and two assumptions about it. */
  private lazy val assumptions =
    TestSupport.preludeAssuming(
      TestSupport.testPreludeSource,
      peano + "\naxiom magicNat : Peano\n\naxiom choose (A: Type)(x: A): A\n"
    )

  test("an axiom in the trusted prelude declares an opaque constant") {
    val res = runProgram("{ magicNat }", assumptions)
    assertEquals(PrettyPrinter.print(res), "magicNat")
    assertEquals(PrettyPrinter.print(res.tpe), "Peano")
  }

  test("a parameterized axiom in the trusted prelude can be applied") {
    val res = runProgram("{ choose(Peano, Peano.zero) }", assumptions)
    assertEquals(PrettyPrinter.print(res), "choose(Peano, Peano.zero)")
    assertEquals(PrettyPrinter.print(res.tpe), "Peano")
  }

  test("an axiom's result must be a type") {
    val bad = TestSupport.preludeAssuming(TestSupport.testPreludeSource, peano + "\naxiom bad : Peano.zero\n")
    interceptError[NotAType](bad.checkedEnv)
  }

  test("axioms are ordinary declarations in entry files and imports") {
    assertEquals(PrettyPrinter.print(runProgram("axiom n : Nat\n{ n }")), "n")
    assertEquals(outside("axiom n : Nat\n", "{ n }").map(PrettyPrinter.print), Some("n"))
    expectOnly[NotAType](typecheckDecls("axiom bad : Nat.zero\n"))
  }
}
