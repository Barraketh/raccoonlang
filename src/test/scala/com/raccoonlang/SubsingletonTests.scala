package com.raccoonlang

class SubsingletonTests extends munit.FunSuite with TestSupport {

  test("propositions have a Subsingleton witness") {
    typecheckDecls(
      """
        |def trueSubsingleton : Subsingleton(True) := propSubsingleton(True)
        |""".stripMargin
    )
  }

  test("Subsingleton.elim proves equality between proofs of the same proposition") {
    val res =
      runProgram(
        """
          |{
          |  Subsingleton.elim(propSubsingleton(True))(True.intro, True.intro)
          |}
          |""".stripMargin
      )

    res.tpe match {
      case Value.VApp(Value.VConst("Eq", _, _), Vector(_, Value.VConst("True", _, _), _, _), _, _) =>
      case other => fail(s"Expected equality proof over True, got $other")
    }
  }
}
