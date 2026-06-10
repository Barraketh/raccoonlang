package com.raccoonlang

import java.nio.file.{Path, Paths}

class MathlibPilotTests extends munit.FunSuite {
  private val SourceRoot: Path = Paths.get("src/test/resources")

  private def typecheckModule(path: String): Unit = {
    val entry = SourceRoot.resolve(path)
    val loaded =
      try ModuleLoader.load(entry, ModuleLoader.LoadConfig(Vector(SourceRoot), Prelude.default))
      catch {
        case ModuleLoader.LoadFailure(error, sources) => fail(ErrorReporter.pretty(error, sources))
      }

    try {
      val core = Elaborator.elab(loaded.program, Prelude.default)
      Interpreter.run(core, Prelude.default)
    } catch {
      case t: TypeError => fail(ErrorReporter.pretty(t, loaded))
    }
  }

  test("Set-like core definitions and subset lemmas typecheck") {
    typecheckModule("MathlibPilot/SetCore.rac")
  }

  test("Set-like definitions can be combined in mathlib-shaped code") {
    typecheckModule("MathlibPilot/SetExamples.rac")
  }

  test("Set extensionality and subset antisymmetry typecheck") {
    typecheckModule("MathlibPilot/SetExtensionality.rac")
  }
}
