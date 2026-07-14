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
