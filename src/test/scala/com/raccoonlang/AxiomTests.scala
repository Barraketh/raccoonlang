package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

class AxiomTests extends munit.FunSuite {
  private def runProgram(src: String): Value =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test).getOrElse(fail("Program has no body"))
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def typecheckDecls(src: String): Unit =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value, Prelude.test)
        Interpreter.run(core, Prelude.test)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  test("axiom declares an opaque constant") {
    val res = runProgram(
      """
        |axiom magicNat : Nat
        |
        |{
        |  magicNat
        |}
        |""".stripMargin
    )

    assertEquals(PrettyPrinter.print(res), "magicNat")
    assertEquals(PrettyPrinter.print(res.tpe), "Nat")
  }

  test("parameterized axiom can be applied") {
    val res = runProgram(
      """
        |axiom choose (A: Type)(x: A): A
        |
        |{
        |  choose(Nat, Nat.zero)
        |}
        |""".stripMargin
    )

    assertEquals(PrettyPrinter.print(res), "choose(Nat, 0)")
    assertEquals(PrettyPrinter.print(res.tpe), "Nat")
  }

  test("axiom instance participates in derive") {
    val res = runProgram(
      """
        |struct DecEq (A: Type) : Type
        | | mk {A: Type} (ok: Nat) : DecEq(A)
        |
        |axiom instance natEq : DecEq(Nat)
        |
        |{
        |  derive[DecEq(Nat)]
        |}
        |""".stripMargin
    )

    assertEquals(PrettyPrinter.print(res), "natEq")
  }

  private def elab(src: String, prelude: Prelude.Config): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => Elaborator.elab(value, prelude)
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  test("the axiom report lists the program's axioms and not the prelude's") {
    val core = elab(
      """
        |axiom magic : Nat
        |def two : Nat := Nat.succ(Nat.succ(Nat.zero))
        |axiom choose (A: Type)(x: A): A
        |""".stripMargin,
      Prelude.default
    )

    assertEquals(Interpreter.axioms(core).map(_.name), Vector("magic", "choose"))
  }

  test("disallowing user axioms rejects a program axiom at its span") {
    val src =
      """
        |def two : Nat := Nat.succ(Nat.succ(Nat.zero))
        |axiom magic : Nat
        |
        |{
        |  magic
        |}
        |""".stripMargin
    val core = elab(src, Prelude.test)

    val error = intercept[UserAxiom](Interpreter.run(core, Prelude.test, allowUserAxioms = false))
    assertEquals(error.name, "magic")
    assertEquals(error.span.map(_.start), Some(src.indexOf("axiom magic")))
  }

  test("disallowing user axioms accepts a program without any, over a prelude that declares one") {
    val core = elab(
      """
        |def two : Nat := Nat.succ(Nat.succ(Nat.zero))
        |
        |{
        |  two
        |}
        |""".stripMargin,
      Prelude.default
    )

    assertEquals(Interpreter.axioms(core), Vector.empty)
    val res = Interpreter.run(core, Prelude.default, allowUserAxioms = false).getOrElse(fail("Program has no body"))
    assertEquals(PrettyPrinter.print(res), "2")
  }

  /** Writes `modules`, by path relative to a fresh root, and loads and elaborates the entry `Main.rac` among them. */
  private def loadModules(modules: (String, String)*): (CoreAst.Program, ModuleLoader.LoadedProgram) = {
    val root = Files.createTempDirectory("raccoon-axioms")
    modules.foreach { case (relative, source) =>
      val path = root.resolve(relative)
      Files.createDirectories(path.getParent)
      Files.write(path, source.getBytes(StandardCharsets.UTF_8))
    }
    val entry: Path = root.resolve("Main.rac")
    val loaded = ModuleLoader.load(entry, ModuleLoader.LoadConfig.forEntry(entry, Prelude.test))
    (Elaborator.elab(loaded.program, Prelude.test), loaded)
  }

  test("disallowing user axioms rejects an imported module's axiom at its span") {
    val lib = "namespace Lib {\n  axiom magic : Nat\n}\n"
    val (core, loaded) = loadModules("Lib/Magic.rac" -> lib, "Main.rac" -> "import Lib.Magic\n\nLib.magic\n")

    assertEquals(Interpreter.axioms(core).map(_.name), Vector("Lib.magic"))
    val error = intercept[UserAxiom](Interpreter.run(core, Prelude.test, allowUserAxioms = false))
    assertEquals(error.name, "Lib.magic")
    val span = error.span.getOrElse(fail("UserAxiom has no span"))
    val source = loaded.sources
      .find(loadedSource => span.source.contains(loadedSource.sourceId))
      .getOrElse(fail("unknown source"))
      .source
    assertEquals(source, lib)
    assertEquals(span.start, lib.indexOf("axiom magic"))
  }

  test("a program cannot declare a builtin, whatever the axiom policy and prelude") {
    // A builtin's declared type is trusted: this one would make `Level.succ` return a `Nat`.
    val src = "namespace Level {\n  def succ (l: Level): Nat := builtin\n}\n"
    Vector(true, false).foreach { allowUserAxioms =>
      val error = intercept[ProgramBuiltin](Interpreter.run(elab(src, Prelude.none), Prelude.none, allowUserAxioms))
      assertEquals(error.name, "Level.succ")
      assertEquals(error.span.map(span => src.substring(span.start, span.end)), Some("builtin"))
    }
    // An imported module is part of the program.
    val (core, _) = loadModules("Lib/Raw.rac" -> "def raw (n: Nat): Nat := builtin\n", "Main.rac" -> "import Lib.Raw\n")
    assertEquals(intercept[ProgramBuiltin](Interpreter.run(core, Prelude.test)).name, "raw")
  }

  test("a prelude may declare a builtin") {
    val prelude =
      Prelude.fromSource("custom prelude", "namespace Level {\n  def succ (l: Level): Level := builtin\n}\n")
    val res =
      Interpreter.run(elab("Sort(Level.succ(Level.zero))\n", prelude), prelude).getOrElse(fail("Program has no body"))
    assertEquals(res, Value.VSort(Value.Level.one))
  }

  test("axiom result must be a type") {
    val p =
      """
        |axiom bad : Nat.zero
        |""".stripMargin

    intercept[NotAType] {
      typecheckDecls(p)
    }
  }
}
