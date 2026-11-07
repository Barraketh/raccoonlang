package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

import com.raccoonlang.ModuleChecker.{Options, PreludeSource}

class ModuleLoaderTests extends munit.FunSuite {
  private def write(root: Path, relative: String, source: String): Path = {
    val path = root.resolve(relative)
    Files.createDirectories(path.getParent)
    Files.write(path, source.getBytes(StandardCharsets.UTF_8))
    path
  }

  private val testPrelude = PreludeSource.Given("test", Prelude.test)

  /** The entry `entry` checked as the CLI checks it, over `prelude` and `roots`, or the entry's directory. */
  private def check(
      entry: Path,
      prelude: PreludeSource = testPrelude,
      roots: Vector[Path] = Vector.empty
  ): ModuleChecker.EntryResult =
    new ModuleChecker()
      .run(Options(roots, prelude, allowUserAxioms = true, stackBytes = 0))
      .check(entry, entry.toString)

  private def run(entry: Path, prelude: PreludeSource = testPrelude, roots: Vector[Path] = Vector.empty): Value = {
    val result = check(entry, prelude, roots)
    result.outcome match {
      case Right(body)         => body.getOrElse(fail("Program has no body")).value
      case Left(te: TypeError) => fail(ErrorReporter.pretty(te, result.sources))
      case Left(other)         => throw other
    }
  }

  private def ctorName(v: Value): String =
    v match {
      case Value.VCtor(head, _, _) => head.name
      case other                   => fail(s"Expected constructor value, got $other")
    }

  /** The error the entry is rejected with. */
  private def error(entry: Path, prelude: PreludeSource = testPrelude): Throwable =
    check(entry, prelude).outcome.left.getOrElse(fail("the entry checked"))

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
        |{
        |  Eq.refl(Nat.zero)
        |}
        |""".stripMargin
    )

    assertEquals(ctorName(run(entry)), "Eq.refl")
  }

  test("can run with a custom prelude file") {
    val root = Files.createTempDirectory("raccoon-modules")
    val preludePath = write(
      root,
      "CustomPrelude.rac",
      """
        |inductive Tiny : Type
        | | mk : Tiny
        |""".stripMargin
    )
    val entry = write(
      root,
      "Main.rac",
      """
        |import Init.Prelude
        |
        |{
        |  Tiny.mk
        |}
        |""".stripMargin
    )

    assertEquals(ctorName(run(entry, PreludeSource.File(preludePath))), "Tiny.mk")
  }

  test("can run without an automatic prelude") {
    val root = Files.createTempDirectory("raccoon-modules")
    val noImportEntry = write(root, "NoImport.rac", "{ Prop }\n")
    assertEquals(PrettyPrinter.print(run(noImportEntry, PreludeSource.Absent)), "Prop")

    val explicitImportEntry = write(root, "ExplicitImport.rac", "import Init.Prelude\n{ Prop }\n")
    assert(error(explicitImportEntry, PreludeSource.Absent).isInstanceOf[ModuleNotFound])
  }

  test("small Init-like module can use the default Prelude surface") {
    val root = Files.createTempDirectory("raccoon-modules")
    val entry = write(
      root,
      "Main.rac",
      """
        |namespace InitPilot {
        |  def sameNat (a: Nat)(b: Nat): Bool := beq(derive[BEq(Nat)], a, b)
        |
        |  def oneLeOne : le(derive[LE(Nat)], Nat.succ(Nat.zero), Nat.succ(Nat.zero)) := Eq.refl(Bool.true)
        |}
        |
        |{
        |  InitPilot.sameNat(Nat.zero, Nat.zero)
        |}
        |""".stripMargin
    )

    assertEquals(ctorName(run(entry, PreludeSource.Bundled)), "Bool.true")
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
        |  def idNat (n: Nat): Nat := n
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
        |  def useNat (n: Nat): Nat := n
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
        |  def makeNat : Nat := zero
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
    assert(error(leakingEntry).isInstanceOf[NotFound])
  }

  test("reports missing modules, cycles, parse errors, and imported bodies") {
    val missingRoot = Files.createTempDirectory("raccoon-modules")
    val missingEntry = write(missingRoot, "Main.rac", "import Lib.Missing\n")
    assert(error(missingEntry).isInstanceOf[ModuleNotFound])

    val cycleRoot = Files.createTempDirectory("raccoon-modules")
    write(cycleRoot, "Lib/A.rac", "import Lib.B\n")
    write(cycleRoot, "Lib/B.rac", "import Lib.A\n")
    val cycleEntry = write(cycleRoot, "Main.rac", "import Lib.A\n")
    assert(error(cycleEntry).isInstanceOf[CyclicImport])

    val parseRoot = Files.createTempDirectory("raccoon-modules")
    write(parseRoot, "Lib/Bad.rac", "def\n")
    val parseEntry = write(parseRoot, "Main.rac", "import Lib.Bad\n")
    assert(error(parseEntry).isInstanceOf[ModuleParseError])

    val bodyRoot = Files.createTempDirectory("raccoon-modules")
    write(bodyRoot, "Lib/Body.rac", "{ Type }\n")
    val bodyEntry = write(bodyRoot, "Main.rac", "import Lib.Body\n")
    assert(error(bodyEntry).isInstanceOf[ImportedModuleHasBody])
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

    assertEquals(ctorName(run(entry, roots = Vector(srcRoot))), "Lib.Nat.zero")
  }

  test("loaded source diagnostics point at imported files") {
    val root = Files.createTempDirectory("raccoon-modules")
    val badPath = write(
      root,
      "Lib/Bad.rac",
      """
        |namespace Lib {
        |  def bad : Missing := Missing
        |}
        |""".stripMargin
    )
    val entry = write(root, "Main.rac", "import Lib.Bad\n")

    val result = check(entry)
    val error = result.outcome match {
      case Left(error: NotFound) => error
      case other                 => fail(s"expected NotFound, got $other")
    }
    assert(ErrorReporter.pretty(error, result.sources).contains(badPath.toRealPath().toString))
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
        |  inductive FunBox : Type
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
        |  def make : FunBox := FunBox.mk(fun (x: Nat): Nat => Nat.zero)
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
        |  def make : FunBox := FunBox.mk(fun (x: Nat): Nat => x)
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

    assert(error(entry).isInstanceOf[TypeError])
  }
}
