package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

/** Shared source-level test plumbing. Specialized environment and residual helpers stay with their suites. */
trait TestSupport { this: munit.FunSuite =>
  protected def suitePrelude: Prelude.Config = Prelude.default

  protected def parse(source: String, prelude: Prelude.Config): CoreAst.Program =
    LanguageParser.parseProgram(source) match {
      case Success(value, _, _) => Elaborator.elab(value, prelude)
      case failure: Failure     => fail(s"Failed to parse: $failure, ${source.substring(failure.curIdx)}")
    }

  protected def parse(source: String): CoreAst.Program = parse(source, suitePrelude)

  protected def runProgram(source: String, prelude: Prelude.Config): Value =
    try Interpreter.run(parse(source, prelude), prelude).getOrElse(fail("Program has no body"))
    catch {
      case error: TypeError => fail(ErrorReporter.pretty(error, Source(source)))
    }

  protected def runProgram(source: String): Value = runProgram(source, suitePrelude)

  protected def typecheckDecls(source: String, prelude: Prelude.Config): Unit =
    Interpreter.run(parse(source, prelude), prelude)

  protected def typecheckDecls(source: String): Unit = typecheckDecls(source, suitePrelude)

  protected def expectTypeError[E <: TypeError](source: String, prelude: Prelude.Config)(implicit
      tag: reflect.ClassTag[E],
      loc: munit.Location
  ): E = intercept[E](Interpreter.run(parse(source, prelude), prelude))

  protected def expectAnyTypeError(source: String)(implicit loc: munit.Location): TypeError =
    intercept[TypeError](Interpreter.run(parse(source, suitePrelude), suitePrelude))

  protected def expectTypeError[E <: TypeError](source: String)(implicit
      tag: reflect.ClassTag[E],
      loc: munit.Location
  ): E = expectTypeError(source, suitePrelude)

  protected def ctorName(value: Value): String = value match {
    case Value.ConstructorHead(name, _, _, _, _) => name
    case Value.VCtor(head, _, _)                 => head.name
    case packed: Value.VPacked                   => packed.codec.decodeHead(packed)._1
    case other                                   => fail(s"Expected constructor value, got $other")
  }
}
