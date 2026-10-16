package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

import java.nio.charset.StandardCharsets
import java.nio.file.Files

/** Shared source-level test plumbing. Specialized environment and residual helpers stay with their suites. */
trait TestSupport extends DiagnosticAssertions { this: munit.FunSuite =>
  protected def suitePrelude: Prelude.Config = Prelude.default

  protected def parseSurface(source: String): SurfaceAst.Program =
    LanguageParser.parseProgram(source) match {
      case Success(value, _, _)        => value
      case Failure(_, curIdx, message) => fail(s"Failed to parse: $message, ${source.substring(curIdx)}")
    }

  protected def parse(source: String, prelude: Prelude.Config): CoreAst.Program =
    LanguageParser.parseProgram(source) match {
      case Success(value, _, _) => Elaborator.elab(value, prelude)
      case failure: Failure     => fail(s"Failed to parse: $failure, ${source.substring(failure.curIdx)}")
    }

  protected def parse(source: String): CoreAst.Program = parse(source, suitePrelude)

  protected def runProgram(source: String, prelude: Prelude.Config): Value =
    try {
      val checked = TypeChecker.check(Elaborator.elaborate(parseSurface(source), prelude))
      Interpreter.run(checked).getOrElse(fail("Program has no body"))
    } catch {
      case Execution.CheckFailure(diagnostics) =>
        fail(diagnostics.map(ErrorReporter.pretty(_, Source(source))).mkString)
      case diagnostic: Diagnostic => fail(ErrorReporter.pretty(diagnostic, Source(source)))
    }

  protected def runProgram(source: String): Value = runProgram(source, suitePrelude)

  protected def typecheckDecls(source: String, prelude: Prelude.Config): Unit =
    TypeChecker.check(Elaborator.elaborate(parseSurface(source), prelude))

  protected def typecheckDecls(source: String): Unit = typecheckDecls(source, suitePrelude)

  protected def expectTypeError[E <: TypeError](source: String, prelude: Prelude.Config)(implicit
      tag: reflect.ClassTag[E],
      loc: munit.Location
  ): E = interceptError[E](TypeChecker.check(Elaborator.elaborate(parseSurface(source), prelude)))

  protected def expectAnyTypeError(source: String)(implicit loc: munit.Location): TypeError =
    interceptDiagnostic {
      TypeChecker.check(Elaborator.elaborate(parseSurface(source), suitePrelude))
    }.error

  protected def expectTypeError[E <: TypeError](source: String)(implicit
      tag: reflect.ClassTag[E],
      loc: munit.Location
  ): E = expectTypeError(source, suitePrelude)

  /** `client` checked in the same file as `module`, and run when it has a body. */
  protected def inside(module: String, client: String): Option[Value] =
    Interpreter.run(TypeChecker.check(Elaborator.elaborate(parseSurface(module + "\n" + client), suitePrelude)))

  /** `client` checked as an entry file importing `module`, another module, and run when it has a body. */
  protected def outside(module: String, client: String): Option[Value] =
    Interpreter.run(TypeChecker.check(Elaborator.elaborate(outsideProgram(module, client), suitePrelude)))

  /** `client` loaded as an entry file importing `module`, another module. */
  protected def outsideProgram(module: String, client: String): SurfaceAst.Program = {
    val root = Files.createTempDirectory("raccoon-module")
    Files.write(root.resolve("Module.rac"), module.getBytes(StandardCharsets.UTF_8))
    val entry = root.resolve("main.rac")
    Files.write(entry, ("import Module\n" + client).getBytes(StandardCharsets.UTF_8))
    ModuleLoader.load(entry, ModuleLoader.LoadConfig.forEntry(entry, suitePrelude)).program
  }

  protected def ctorName(value: Value): String = value match {
    case Value.ConstructorHead(name, _, _, _, _) => name
    case Value.VCtor(head, _, _)                 => head.name
    case other                                   => fail(s"Expected constructor value, got $other")
  }
}

object TestSupport {
  lazy val bundledPreludeSource: String = resource("/Init/Prelude.rac")

  lazy val testPreludeSource: String = resource("/Init/TestPrelude.rac")

  /** A custom prelude extended with shared assumptions for a suite. */
  def preludeAssuming(base: String, assumptions: String): Prelude.Config =
    Prelude.fromSource("assumptions", base + "\n" + assumptions)

  private def resource(path: String): String = {
    val stream = getClass.getResourceAsStream(path)
    try new String(stream.readAllBytes(), StandardCharsets.UTF_8)
    finally stream.close()
  }
}
