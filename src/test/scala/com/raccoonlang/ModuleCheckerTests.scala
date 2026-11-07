package com.raccoonlang

import java.io.{ByteArrayOutputStream, PrintStream}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}

import com.raccoonlang.ModuleChecker.{EntryResult, Listener, Options, PreludeSource}

/**
 * Checking each module once (docs/namespaces.md, "Imports"): a module means what it means standalone, so an entry's
 * verdict in a batch is its verdict alone, and a server's kept results are those a fresh check computes.
 */
class ModuleCheckerTests extends munit.FunSuite {
  private def write(root: Path, relative: String, source: String): Path = {
    val path = root.resolve(relative)
    Files.createDirectories(path.getParent)
    Files.write(path, source.getBytes(StandardCharsets.UTF_8))
    path
  }

  private def options(roots: Vector[Path], prelude: PreludeSource = PreludeSource.Bundled): Options =
    Options(roots, prelude, allowUserAxioms = true, stackBytes = 0)

  /** What a verdict is compared by: the result printed, or the error reported, without the checker's numbering. */
  private def verdict(result: EntryResult): Either[String, Option[String]] =
    result.outcome match {
      case Left(te: TypeError) => Left(ErrorReporter.pretty(te, result.sources).replaceAll("#\\d+", ""))
      case Left(other)         => Left(other.toString)
      case Right(body)         => Right(body.map(_.printed))
    }

  /** The modules a check of `entries` in one run of `checker` checked afresh, in order, with each entry's result. */
  private def checking(checker: ModuleChecker, opts: Options, entries: Path*): (Vector[Path], Vector[EntryResult]) = {
    val fresh = Vector.newBuilder[Path]
    val listener = new Listener { override def checked(module: Path): Unit = fresh += module.getFileName }
    val run = checker.run(opts)
    val results = entries.toVector.map(entry => run.check(entry, entry.toString, listener))
    checker.sweep()
    (fresh.result(), results)
  }

  private def rejectedWith[T <: TypeError](result: EntryResult)(implicit ct: reflect.ClassTag[T]): T =
    result.outcome match {
      case Left(error: T) => error
      case other          => fail(s"expected ${ct.runtimeClass.getSimpleName}, got $other")
    }

  /** The file `error` is located in, among `result`'s sources. */
  private def locatedIn(error: TypeError, result: EntryResult): Path =
    error.span
      .flatMap(_.source)
      .flatMap(id => result.sources.find(_.sourceId == id))
      .getOrElse(fail(s"${error.getMessage} is not located in a source"))
      .path

  /**
   * A project of modules, in which `Broken` does not check, `Clash` declares what `Base` does, `Sibling` uses `Base`
   * without importing it, and `Uses` and `Top` import `Broken` and its importer.
   */
  private def project(): Path = {
    val root = Files.createTempDirectory("raccoon-batch")
    write(root, "Base.rac", "namespace Lib {\n  def one : Nat := 1\n}\n")
    write(root, "Mid.rac", "import Base\n\nnamespace Lib {\n  def two : Nat := Nat.succ(Lib.one)\n}\n")
    write(root, "Clash.rac", "namespace Lib {\n  def one : Nat := 7\n}\n")
    write(root, "Sibling.rac", "namespace Lib {\n  def three : Nat := Nat.succ(Lib.one)\n}\n")
    write(root, "Broken.rac", "import Base\n\ndef broken : Nat := Bool.true\n")
    write(root, "Uses.rac", "import Broken\n\ndef uses : Nat := broken\n")
    write(root, "Top.rac", "import Mid\nimport Uses\n\n{ Lib.two }\n")
    write(root, "Ok.rac", "import Mid\n\ndef two : Eq(Nat, Lib.two, 2) := Eq.refl(2)\n\n{ Lib.two }\n")
    write(root, "Both.rac", "import Base\nimport Clash\n")
    write(root, "Siblings.rac", "import Base\nimport Sibling\n")
    root
  }

  test("an entry's verdict in a batch is its verdict alone, for the examples, the protocol library and a project") {
    val examples = Paths.get("examples").toAbsolutePath.normalize
    val library = Paths.get("lib").toAbsolutePath.normalize
    val root = project()
    val groups = Vector(
      Vector(examples) -> Files.list(examples).toArray.toVector.map(_.asInstanceOf[Path]).filter(_.toString.endsWith(".rac")),
      Vector(library) -> Files.list(library.resolve("Protocol")).toArray.toVector.map(_.asInstanceOf[Path]),
      Vector(root) -> Files.list(root).toArray.toVector.map(_.asInstanceOf[Path])
    )
    groups.foreach { case (roots, entries) =>
      assert(entries.nonEmpty)
      val sorted = entries.sortBy(_.toString)
      // One checker for the batch, in two orders, and a fresh one for each entry.
      val batch = new ModuleChecker().run(options(roots))
      val reversed = new ModuleChecker().run(options(roots))
      val inBatch = sorted.map(entry => entry -> verdict(batch.check(entry, entry.toString))).toMap
      val inReverse = sorted.reverse.map(entry => entry -> verdict(reversed.check(entry, entry.toString))).toMap
      sorted.foreach { entry =>
        val alone = verdict(new ModuleChecker().run(options(roots)).check(entry, entry.toString))
        assertEquals(inBatch(entry), alone, entry.toString)
        assertEquals(inReverse(entry), alone, entry.toString)
      }
    }
  }

  test("a module does not see a name its importer's other imports declared") {
    val root = project()
    val run = new ModuleChecker().run(options(Vector(root)))
    // Base precedes Sibling in Siblings' imports, but Sibling does not import it.
    val result = run.check(root.resolve("Siblings.rac"), "Siblings.rac")
    val error = rejectedWith[NotFound](result)
    assertEquals(locatedIn(error, result), root.resolve("Sibling.rac").toRealPath())
    assertEquals(verdict(run.check(root.resolve("Sibling.rac"), "Sibling.rac")), verdict(result))
  }

  test("a module does not find an instance its importer's other imports declared") {
    val root = Files.createTempDirectory("raccoon-batch")
    write(root, "Flag.rac", "inductive Flag : Type\n | mk (b: Bool) : Flag\n")
    write(root, "Inst.rac", "import Flag\n\ndef instance theFlag : Flag := Flag.mk(Bool.true)\n")
    write(root, "Derived.rac", "import Flag\n\ndef flag : Flag := derive[Flag]\n")
    write(root, "Imported.rac", "import Inst\n\ndef flag : Flag := derive[Flag]\n")
    write(root, "Main.rac", "import Inst\nimport Derived\n\n{ flag }\n")
    val run = new ModuleChecker().run(options(Vector(root)))
    assertEquals(verdict(run.check(root.resolve("Imported.rac"), "Imported.rac")), Right(None))
    val result = run.check(root.resolve("Main.rac"), "Main.rac")
    val error = rejectedWith[NoInstanceFound](result)
    assertEquals(locatedIn(error, result), root.resolve("Derived.rac").toRealPath())
  }

  test("a clash between modules neither of which imports the other is found when their importer replays them") {
    val root = project()
    val run = new ModuleChecker().run(options(Vector(root)))
    val clashSource = Files.readString(root.resolve("Clash.rac"))
    Vector("Both.rac", "Both.rac").foreach { entry =>
      val result = run.check(root.resolve(entry), entry)
      val error = rejectedWith[AlreadyDefined](result)
      assertEquals(error.name, "Lib.one")
      assertEquals(locatedIn(error, result), root.resolve("Clash.rac").toRealPath())
      assertEquals(error.span.map(_.start), Some(clashSource.indexOf("one")))
    }
    // An importer of the clash fails with it.
    write(root, "AboveBoth.rac", "import Both\n\ndef four : Nat := 4\n")
    val above = run.check(root.resolve("AboveBoth.rac"), "AboveBoth.rac")
    assertEquals(rejectedWith[AlreadyDefined](above).name, "Lib.one")
    // A clash before a module that fails to elaborate is the error a fresh check meets first.
    write(root, "Unknown.rac", "def unknown : Nat := missing\n")
    write(root, "ClashFirst.rac", "import Base\nimport Clash\nimport Unknown\n")
    assertEquals(rejectedWith[AlreadyDefined](run.check(root.resolve("ClashFirst.rac"), "ClashFirst.rac")).name, "Lib.one")
    write(root, "UnknownFirst.rac", "import Unknown\nimport Base\nimport Clash\n")
    rejectedWith[NotFound](run.check(root.resolve("UnknownFirst.rac"), "UnknownFirst.rac"))
  }

  test("a module that fails fails every entry above it, with its own error, reported once") {
    val root = project()
    val checker = new ModuleChecker()
    val (checked, results) =
      checking(checker, options(Vector(root)), root.resolve("Top.rac"), root.resolve("Uses.rac"), root.resolve("Broken.rac"))
    // Broken checked once, and nothing above it.
    assertEquals(checked.count(_.toString == "Broken.rac"), 1)
    assert(!checked.exists(name => name.toString == "Uses.rac" || name.toString == "Top.rac"), checked)
    val errors = results.map(rejectedWith[TypeMismatch](_))
    assert(errors.forall(_ eq errors.head), "the entries share Broken's failure")
    results.foreach(result => assertEquals(locatedIn(errors.head, result), root.resolve("Broken.rac").toRealPath()))

    val out = new ByteArrayOutputStream
    val err = new ByteArrayOutputStream
    val cli = Main.parseArgs(Seq("--batch", "Top.rac", "Uses.rac", "Broken.rac", "Ok.rac")).get
    val code = Main.run(cli, new ModuleChecker, root, new PrintStream(out, true), new PrintStream(err, true))
    val text = out.toString(StandardCharsets.UTF_8)
    assertEquals(code, 1)
    assertEquals(text.split("\n").count(_.contains("Broken.rac:2:")), 1, text)
    assert(text.contains("Uses.rac: rejected"), text)
    assert(text.contains("Ok.rac: accepted"), text)
    assert(text.contains("4 entries: 1 accepted, 3 rejected"), text)

    val json = new ByteArrayOutputStream
    val jsonCli = Main.parseArgs(Seq("--batch", "--json", "Top.rac", "Ok.rac")).get
    assertEquals(Main.run(jsonCli, new ModuleChecker, root, new PrintStream(json, true), new PrintStream(err, true)), 1)
    val lines = json.toString(StandardCharsets.UTF_8).trim.split("\n").toVector.map(Json.parse(_).asInstanceOf[Map[String, Any]])
    assertEquals(lines.map(_("entry")), Vector("Top.rac", "Ok.rac"))
    assertEquals(lines.map(_("verdict")), Vector("rejected", "accepted"))
    assertEquals(lines(0)("error_module"), root.resolve("Broken.rac").toRealPath().toString)
    assert(lines(0)("stderr").toString.contains("Broken.rac:2:"), lines(0))
    assertEquals(lines(1)("stdout"), "2\n")
  }

  test("kept results serve a later run, which checks afresh only what changed, an imported module's edit included") {
    val root = project()
    val checker = new ModuleChecker()
    val opts = options(Vector(root))
    val ok = root.resolve("Ok.rac")

    val (first, Vector(firstResult)) = checking(checker, opts, ok)
    assertEquals(first.map(_.toString), Vector("Base.rac", "Mid.rac", "Ok.rac"))
    assertEquals(verdict(firstResult), Right(Some("2")))
    assertEquals(checking(checker, opts, ok)._1, Vector.empty)

    // The entry's own edit checks it alone.
    write(root, "Ok.rac", Files.readString(ok).replace("import Mid\n", "import Mid\n\ndef three : Nat := 3\n"))
    assertEquals(checking(checker, opts, ok)._1.map(_.toString), Vector("Ok.rac"))

    // An imported module's edit checks it and what imports it; the entry is rejected for its own proof.
    write(root, "Base.rac", "namespace Lib {\n  def one : Nat := 5\n}\n")
    val (edited, Vector(editedResult)) = checking(checker, opts, ok)
    assertEquals(edited.map(_.toString), Vector("Base.rac", "Mid.rac", "Ok.rac"))
    assertEquals(locatedIn(rejectedWith[TypeError](editedResult), editedResult), ok.toRealPath())

    // Restoring it restores the verdict; a module that only imports Base is checked against its new version.
    write(root, "Base.rac", "namespace Lib {\n  def one : Nat := 1\n}\n")
    val (restored, Vector(restoredResult, sibling)) = checking(checker, opts, ok, root.resolve("Both.rac"))
    assertEquals(restored.map(_.toString), Vector("Base.rac", "Mid.rac", "Ok.rac"))
    assertEquals(verdict(restoredResult), Right(Some("2")))
    assertEquals(rejectedWith[AlreadyDefined](sibling).name, "Lib.one")
  }

  test("CLI arguments: one file alone, several with --batch") {
    def parsed(args: String*) = Main.parseArgs(args)
    assert(parsed("a.rac").nonEmpty)
    assert(parsed("a.rac", "b.rac").isEmpty)
    assertEquals(parsed("--batch", "a.rac", "b.rac").map(_.files), Some(Vector("a.rac", "b.rac")))
    assert(parsed("--batch").isEmpty)
    assert(parsed("--json", "a.rac").isEmpty)
    assert(parsed("--batch", "--json", "a.rac").exists(_.json))
    assert(parsed("--no-prelude", "--prelude", "p.rac", "a.rac").isEmpty)
  }

  test("JSON strings round-trip through quoting and parsing") {
    val text = "a \"quoted\" \\ line\nwith\ttabs, \u0001 and é"
    assertEquals(Json.parse(Json.quote(text)), text)
    assertEquals(
      Json.parse("""{"cwd": "/x", "args": ["--batch", "a.rac"], "stop": false, "n": 2}"""),
      Map("cwd" -> "/x", "args" -> Vector("--batch", "a.rac"), "stop" -> false, "n" -> 2.0)
    )
    intercept[IllegalArgumentException](Json.parse("""{"a": 1"""))
    intercept[IllegalArgumentException](Json.parse("""{"a": 1} x"""))
  }
}
