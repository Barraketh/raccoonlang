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
        |inductive DecEq (A: Type) : Type
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

  /** A prelude with one trusted axiom; the bundled prelude declares none. */
  private lazy val axiomPrelude = Prelude.fromSource("custom prelude", "axiom trusted : Nat\n")

  test("the axiom report lists the program's axioms and not the prelude's") {
    val core = elab(
      """
        |axiom magic : Nat
        |def two : Nat := Nat.succ(Nat.succ(Nat.zero))
        |axiom choose (A: Type)(x: A): A
        |""".stripMargin,
      axiomPrelude
    )

    assertEquals(Interpreter.axioms(axiomPrelude.core).map(_.name), Vector("trusted"))
    assertEquals(Interpreter.axioms(core).map(_.name), Vector("magic", "choose"))
    // The bundled prelude's trusted axioms: the division laws; `Nat.mul_add` is proved by expansion.
    assertEquals(Interpreter.axioms(Prelude.default.core).map(_.name), Vector("Nat.div_add_mod", "Nat.mod_lt"))
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
        |  Nat.add(two, trusted)
        |}
        |""".stripMargin,
      axiomPrelude
    )

    assertEquals(Interpreter.axioms(core), Vector.empty)
    val res = Interpreter.run(core, axiomPrelude, allowUserAxioms = false).getOrElse(fail("Program has no body"))
    assertEquals(PrettyPrinter.print(res), "trusted + 2")
  }

  /**
   * Writes `modules`, by path relative to a fresh root, and checks the entry `Main.rac` among them as the CLI does,
   * with or without user axioms.
   */
  private def checkModules(allowUserAxioms: Boolean, modules: (String, String)*): ModuleChecker.EntryResult = {
    val root = Files.createTempDirectory("raccoon-axioms")
    modules.foreach { case (relative, source) =>
      val path = root.resolve(relative)
      Files.createDirectories(path.getParent)
      Files.write(path, source.getBytes(StandardCharsets.UTF_8))
    }
    val entry: Path = root.resolve("Main.rac")
    val options = ModuleChecker.Options(
      Vector.empty,
      ModuleChecker.PreludeSource.Given("test", Prelude.test),
      allowUserAxioms,
      stackBytes = 0
    )
    new ModuleChecker().run(options).check(entry, entry.toString)
  }

  test("disallowing user axioms rejects an imported module's axiom at its span") {
    val lib = "namespace Lib {\n  axiom magic : Nat\n}\n"
    val result =
      checkModules(allowUserAxioms = false, "Lib/Magic.rac" -> lib, "Main.rac" -> "import Lib.Magic\n\nLib.magic\n")

    assertEquals(result.axioms, Vector("Lib.magic"))
    val error = result.outcome match {
      case Left(error: UserAxiom) => error
      case other                  => fail(s"expected UserAxiom, got $other")
    }
    assertEquals(error.name, "Lib.magic")
    val span = error.span.getOrElse(fail("UserAxiom has no span"))
    val source = result.sources
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
    val result =
      checkModules(
        allowUserAxioms = true,
        "Lib/Raw.rac" -> "def raw (n: Nat): Nat := builtin\n",
        "Main.rac" -> "import Lib.Raw\n"
      )
    result.outcome match {
      case Left(error: ProgramBuiltin) => assertEquals(error.name, "raw")
      case other                       => fail(s"expected ProgramBuiltin, got $other")
    }
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
