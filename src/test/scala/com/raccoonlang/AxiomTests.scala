package com.raccoonlang

import com.raccoonlang.Value.{VApp, VConst, Symbol}

class AxiomTests extends munit.FunSuite {
  private def run(source: String): Value = {
    val surface = LanguageParser.parseProgram(source) match {
      case Success(program, _, _) => program
      case failure                => fail(s"Expected parse success, got $failure")
    }
    Interpreter.run(Elaborator.elab(surface)).getOrElse(fail("Expected a result"))
  }

  test("a nullary axiom is an opaque symbolic constant") {
    run("axiom choice : Type\n\nchoice") match {
      case VConst(name, Symbol, tpe) =>
        assertEquals(name, "choice")
        assert(tpe == Value.TypeValue)
      case other => fail(s"Expected symbolic constant, got $other")
    }
  }

  test("a parameterized axiom remains applicable as a symbolic head") {
    run("axiom choice (A: Type): Type\n\nchoice(Type)") match {
      case VApp(VConst(name, Symbol, _), args, tpe, _) =>
        assertEquals(name, "choice")
        assertEquals(args.length, 1)
        assert(tpe == Value.TypeValue)
      case other => fail(s"Expected applied symbolic axiom, got $other")
    }
  }

  test("an axiom result must itself be a type") {
    intercept[NotAType] {
      TestSupport.check("axiom A : Type\naxiom x : A\naxiom bad : x\n")
    }
  }
}
