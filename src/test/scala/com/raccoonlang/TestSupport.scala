package com.raccoonlang

object TestSupport {
  def core(source: String): CoreAst.Program = LanguageParser.parseProgram(source) match {
    case Success(program, _, _) => Elaborator.elab(program)
    case failure                => throw new AssertionError(s"Expected parse success, got $failure")
  }

  def eval(source: String): Value = Interpreter.run(core(source)).getOrElse(throw new AssertionError("Expected result"))

  def check(source: String): (Env, Option[TypeChecker.CheckedTerm]) = TypeChecker.checkProgram(core(source))
}
