package com.raccoonlang

import java.nio.file.Paths
import java.nio.file.Files

/** Examples are standalone programs exercised through the current parser, checker, and evaluator APIs. */
class ExampleSmokeTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.none

  private def smoke(path: String, prelude: Prelude.Config = Prelude.none): Value = {
    val source = Files.readString(Paths.get(path))
    val program = suiteCore(source)
    val (env, checked) = TypeChecker.checkProgram(program, prelude.checkedEnv)
    checked match {
      case Some(term) => Interpreter.evalTerm(term.residual, env)
      case None       => throw new AssertionError(s"$path has no result")
    }
  }

  test("nats example parses, elaborates, checks, and evaluates") {
    assertEquals(PrettyPrinter.print(smoke("examples/nats.rac")), "2")
  }

  test("universe-polymorphic Vec example parses, elaborates, checks, and evaluates") {
    val result = smoke("examples/universe_polymorphic_vec.rac", Prelude.default)
    assertEquals(ctorName(result), "Vec.nil")
  }

  test("ordinary source rejects qualified declaration heads") {
    LanguageParser.parseProgram("def A.f : Type := Type") match {
      case Failure(_, _, _) => ()
      case other            => fail(s"ordinary parser accepted qualified declaration: $other")
    }
  }

  test("prelude configs cache and isolate trusted capabilities") {
    assert(Prelude.default.checkedEnv eq Prelude.default.checkedEnv)
    assert(Prelude.test.checkedEnv eq Prelude.test.checkedEnv)
    assert(!(Prelude.default.checkedEnv eq Prelude.test.checkedEnv))
    assert(Prelude.none.checkedEnv.nativeLiterals.natLayout.isEmpty)
    intercept[ReservedKernelName] {
      val source = LanguageParser.parseProgram("def bad : Type := builtin\n{ Type }") match {
        case Success(program, _, _) => Elaborator.elab(program)
        case failure                => throw new AssertionError(failure.toString)
      }
      TypeChecker.checkProgram(source, Prelude.default.checkedEnv)
    }
  }
}
