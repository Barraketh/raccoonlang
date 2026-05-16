package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

class ModuleLoaderTests extends munit.FunSuite {
  private def write(root: Path, relative: String, source: String): Path = {
    val path = root.resolve(relative)
    Files.createDirectories(path.getParent)
    Files.write(path, source.getBytes(StandardCharsets.UTF_8))
    path
  }

  private def loadCore(entry: Path): CoreAst.Program =
    Elaborator.elab(ModuleLoader.load(entry).program)

  private def run(entry: Path): Value =
    Interpreter.run(loadCore(entry)).getOrElse(fail("Program has no body"))

  private def ctorName(v: Value): String =
    v match {
      case Value.VCtor(head, _, _) => head.name
      case other                   => fail(s"Expected constructor value, got $other")
    }

  private def loadError(entry: Path): TypeError =
    intercept[ModuleLoader.LoadFailure] {
      ModuleLoader.load(entry)
    }.error

  test("loads an entry-relative module and exposes canonical names") {
    val root = Files.createTempDirectory("raccoon-modules")
    write(
      root,
      "Lib/Nat.rac",
      """
        |namespace Lib {
        |  inductive Nat : Type
        |   | zero : Nat
        |   | succ (_: Nat) : Nat
        |}
        |""".stripMargin
    )
    val entry = write(
      root,
      "Main.rac",
      """
        |import Lib.Nat
        |
        |{
        |  Lib.Nat.zero
        |}
        |""".stripMargin
    )

    assertEquals(ctorName(run(entry)), "Lib.Nat.zero")
  }

  test("explicit Init.Prelude import is harmless because the prelude is automatic") {
    val root = Files.createTempDirectory("raccoon-modules")
    val entry = write(
      root,
      "Main.rac",
      """
        |import Init.Prelude
        |
        |inductive Nat : Type
        | | zero : Nat
        |
        |{
        |  Eq.refl(Nat.zero)
        |}
        |""".stripMargin
    )

    assertEquals(ctorName(run(entry)), "Eq.refl")
  }

  test("loads transitive imports before importers") {
    val root = Files.createTempDirectory("raccoon-modules")
    write(
      root,
      "Lib/Nat.rac",
      """
        |namespace Lib {
        |  inductive Nat : Type
        |   | zero : Nat
        |}
        |""".stripMargin
    )
    write(
      root,
      "Lib/Id.rac",
      """
        |import Lib.Nat
        |
        |namespace Lib {
        |  inline def idNat (n: Nat): Nat := n
        |}
        |""".stripMargin
    )
    val entry = write(
      root,
      "Main.rac",
      """
        |import Lib.Id
        |
        |{
        |  Lib.idNat(Lib.Nat.zero)
        |}
        |""".stripMargin
    )

    assertEquals(ctorName(run(entry)), "Lib.Nat.zero")
  }

  test("deduplicates modules reached through multiple imports") {
    val root = Files.createTempDirectory("raccoon-modules")
    write(
      root,
      "Lib/Nat.rac",
      """
        |namespace Lib {
        |  inductive Nat : Type
        |   | zero : Nat
        |}
        |""".stripMargin
    )
    write(
      root,
      "Lib/UseNat.rac",
      """
        |import Lib.Nat
        |
        |namespace Lib {
        |  inline def useNat (n: Nat): Nat := n
        |}
        |""".stripMargin
    )
    val entry = write(
      root,
      "Main.rac",
      """
        |import Lib.Nat
        |import Lib.UseNat
        |
        |{
        |  Lib.useNat(Lib.Nat.zero)
        |}
        |""".stripMargin
    )

    assertEquals(ctorName(run(entry)), "Lib.Nat.zero")
  }

  test("top-level opens in imported modules do not leak to importers") {
    val root = Files.createTempDirectory("raccoon-modules")
    write(
      root,
      "Lib/Nat.rac",
      """
        |namespace Lib {
        |  inductive Nat : Type
        |   | zero : Nat
        |}
        |""".stripMargin
    )
    write(
      root,
      "Lib/Makers.rac",
      """
        |import Lib.Nat
        |
        |open Lib.Nat
        |
        |namespace Lib {
        |  inline def makeNat : Nat := zero
        |}
        |""".stripMargin
    )
    val okEntry = write(
      root,
      "Ok.rac",
      """
        |import Lib.Makers
        |
        |{
        |  Lib.makeNat
        |}
        |""".stripMargin
    )
    assertEquals(ctorName(run(okEntry)), "Lib.Nat.zero")

    val leakingEntry = write(
      root,
      "Leaking.rac",
      """
        |import Lib.Makers
        |
        |{
        |  zero
        |}
        |""".stripMargin
    )
    val loaded = ModuleLoader.load(leakingEntry)
    intercept[NotFound] {
      Elaborator.elab(loaded.program)
    }
  }

  test("reports missing modules, cycles, parse errors, and imported bodies") {
    val missingRoot = Files.createTempDirectory("raccoon-modules")
    val missingEntry = write(missingRoot, "Main.rac", "import Lib.Missing\n")
    assert(loadError(missingEntry).isInstanceOf[ModuleNotFound])

    val cycleRoot = Files.createTempDirectory("raccoon-modules")
    write(cycleRoot, "Lib/A.rac", "import Lib.B\n")
    write(cycleRoot, "Lib/B.rac", "import Lib.A\n")
    val cycleEntry = write(cycleRoot, "Main.rac", "import Lib.A\n")
    assert(loadError(cycleEntry).isInstanceOf[CyclicImport])

    val parseRoot = Files.createTempDirectory("raccoon-modules")
    write(parseRoot, "Lib/Bad.rac", "def\n")
    val parseEntry = write(parseRoot, "Main.rac", "import Lib.Bad\n")
    assert(loadError(parseEntry).isInstanceOf[ModuleParseError])

    val bodyRoot = Files.createTempDirectory("raccoon-modules")
    write(bodyRoot, "Lib/Body.rac", "{ Type }\n")
    val bodyEntry = write(bodyRoot, "Main.rac", "import Lib.Body\n")
    assert(loadError(bodyEntry).isInstanceOf[ImportedModuleHasBody])
  }

  test("loads imports from configured source roots") {
    val root = Files.createTempDirectory("raccoon-modules")
    val srcRoot = root.resolve("src")
    val appRoot = root.resolve("app")
    write(
      srcRoot,
      "Lib/Nat.rac",
      """
        |namespace Lib {
        |  inductive Nat : Type
        |   | zero : Nat
        |}
        |""".stripMargin
    )
    val entry = write(
      appRoot,
      "Main.rac",
      """
        |import Lib.Nat
        |
        |{
        |  Lib.Nat.zero
        |}
        |""".stripMargin
    )

    val loaded = ModuleLoader.load(entry, ModuleLoader.LoadConfig(Vector(srcRoot)))
    assertEquals(ctorName(Interpreter.run(Elaborator.elab(loaded.program)).getOrElse(fail("Program has no body"))), "Lib.Nat.zero")
  }

  test("loaded source diagnostics point at imported files") {
    val root = Files.createTempDirectory("raccoon-modules")
    val badPath = write(
      root,
      "Lib/Bad.rac",
      """
        |namespace Lib {
        |  inline def bad : Missing := Missing
        |}
        |""".stripMargin
    )
    val entry = write(root, "Main.rac", "import Lib.Bad\n")

    val loaded = ModuleLoader.load(entry)
    val error = intercept[NotFound] {
      Elaborator.elab(loaded.program)
    }
    assert(ErrorReporter.pretty(error, loaded).contains(badPath.toRealPath().toString))
  }

  test("same-offset local value ids remain distinct across imported modules") {
    val root = Files.createTempDirectory("raccoon-modules")
    write(
      root,
      "Common.rac",
      """
        |namespace Common {
        |  inductive Nat : Type
        |   | zero : Nat
        |   | succ (_: Nat) : Nat
        |
        |  struct FunBox : Type
        |   | mk (f: (x: Nat) -> Nat) : FunBox
        |}
        |""".stripMargin
    )
    write(
      root,
      "A.rac",
      """
        |import Common
        |
        |open Common
        |
        |namespace A {
        |  inline def make : FunBox := FunBox.mk(fun (x: Nat): Nat => Nat.zero)
        |}
        |""".stripMargin
    )
    write(
      root,
      "B.rac",
      """
        |import Common
        |
        |open Common
        |
        |namespace B {
        |  inline def make : FunBox := FunBox.mk(fun (x: Nat): Nat => x)
        |}
        |""".stripMargin
    )
    val entry = write(
      root,
      "Main.rac",
      """
        |import Common
        |import A
        |import B
        |
        |open Common
        |
        |def bad : Eq((x: Nat) -> Nat, A.make.f, B.make.f) := {
        |  Eq.refl(A.make.f)
        |}
        |""".stripMargin
    )

    val loaded = ModuleLoader.load(entry)
    val core = Elaborator.elab(loaded.program)

    intercept[TypeError] {
      Interpreter.run(core)
    }
  }
}
