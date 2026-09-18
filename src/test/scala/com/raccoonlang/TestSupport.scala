package com.raccoonlang

object TestSupport {
  def core(source: String): CoreAst.Program = LanguageParser.parseProgram(source) match {
    case Success(program, _, _) => Elaborator.elab(program)
    case failure                => throw new AssertionError(s"Expected parse success, got $failure")
  }

  def eval(source: String): Value = Interpreter.run(core(source)).getOrElse(throw new AssertionError("Expected result"))

  def check(source: String): (Env, Option[TypeChecker.CheckedTerm]) = TypeChecker.checkProgram(core(source))
}

/** Source-facing harness for suites that deliberately select a production or test prelude. */
trait TestSupport {
  protected val suitePrelude: Prelude.Config = Prelude.default

  protected def suiteCore(source: String): CoreAst.Program = LanguageParser.parseProgram(source) match {
    case Success(program, _, _) => Elaborator.elab(program)
    case failure                => throw new AssertionError(s"Expected parse success, got $failure")
  }

  protected def typecheckDecls(source: String): Env = {
    val (env, _) = TypeChecker.checkProgram(suiteCore(source), suitePrelude.checkedEnv)
    env
  }

  protected def runProgram(source: String): Value = {
    val (_, checked) = TypeChecker.checkProgram(suiteCore(source), suitePrelude.checkedEnv)
    checked.map(_.value).getOrElse(throw new AssertionError("Expected result"))
  }

  protected def ctorName(value: Value): String = value match {
    case Value.VCtor(head, _, _)                 => head.name
    case Value.ConstructorHead(name, _, _, _, _) => name
    case packed: Value.VPacked                   => packed.codec.decodeHead(packed)._1
    case other                                   => throw new AssertionError(s"Expected constructor, got $other")
  }
}
