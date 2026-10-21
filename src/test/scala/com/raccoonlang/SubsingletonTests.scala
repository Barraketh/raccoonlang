package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class SubsingletonTests extends munit.FunSuite {
  private def parse(src: String): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => Elaborator.elab(value)
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def typecheckDecls(src: String): Unit =
    try {
      Interpreter.run(parse(src))
    } catch {
      case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
    }

  private def runProgram(src: String): Value =
    try {
      Interpreter.run(parse(src)).getOrElse(fail("Program has no body"))
    } catch {
      case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
    }

  private def assertTypeError[T <: TypeError](src: String)(implicit loc: munit.Location, ct: reflect.ClassTag[T]): T =
    intercept[T] {
      Interpreter.run(parse(src))
    }

  private val unitInstance =
    """
      |def unitEq (a: Unit)(b: Unit): Eq(Unit, a, b) := {
      |  match a returning Eq(Unit, a, b) with
      |  | Unit.unit => {
      |    match b returning Eq(Unit, Unit.unit, b) with
      |    | Unit.unit => Eq.refl(Unit.unit)
      |  }
      |}
      |
      |def instance unitSubsingleton : Subsingleton(Unit) := Subsingleton.intro(Unit, unitEq)
      |""".stripMargin

  test("Type carriers can have an explicit Subsingleton witness") {
    typecheckDecls(
      unitInstance +
        """
          |def unitWitness : Subsingleton(Unit) := unitSubsingleton
          |""".stripMargin
    )
  }

  test("Subsingleton instances for Type carriers participate in derive") {
    typecheckDecls(
      unitInstance +
        """
          |def derived : Subsingleton(Unit) := derive[Subsingleton(Unit)]
          |""".stripMargin
    )
  }

  test("Subsingleton.elim proves equality between values of a Type carrier") {
    val res =
      runProgram(
        unitInstance +
          """
            |{
            |  Subsingleton.elim(derive[Subsingleton(Unit)])(Unit.unit, Unit.unit)
            |}
            |""".stripMargin
      )

    res.tpe match {
      case Value.VApp(Value.VConst("Eq", _, _), Vector(Value.VConst("Unit", _, _), _, _), _, _) =>
      case other => fail(s"Expected equality proof over Unit, got $other")
    }
  }

  test("propositions cannot be Subsingleton carriers") {
    val error = assertTypeError[PropositionAsTypeCarrier](
      """
        |def bad : Subsingleton(True) := derive[Subsingleton(True)]
        |""".stripMargin
    )

    assertEquals(error.getMessage, "Expected a Type carrier, but got a proposition (of sort Prop)")
    assert(error.span.nonEmpty)
  }

  test("propositions cannot be DecidableEq carriers") {
    assertTypeError[PropositionAsTypeCarrier](
      """
        |def bad : DecidableEq(False) := derive[DecidableEq(False)]
        |""".stripMargin
    )
  }

  test("ordinary data types are not subsingletons without an instance") {
    assertTypeError[NoInstanceFound](
      """
        |def bad : Subsingleton(Nat) := derive[Subsingleton(Nat)]
        |""".stripMargin
    )
  }
}
