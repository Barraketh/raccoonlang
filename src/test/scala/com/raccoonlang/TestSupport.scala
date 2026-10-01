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
      case Execution.CheckFailure(diagnostics, strings) =>
        fail(diagnostics.map(ErrorReporter.pretty(_, Source(source), strings)).mkString)
      case diagnostic: Diagnostic => fail(ErrorReporter.pretty(diagnostic, Source(source), None))
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

  /** The time `body` takes, in milliseconds, with its result. */
  /**
   * The deferred proofs evaluation forces while `body` runs. The counter is global, which is sound while suites run one
   * at a time in the forked test JVM, as build.sbt has them.
   */
  protected def forcings(body: => Any): Long = {
    val before = Value.DeferredEvidence.forcings.get()
    body
    Value.DeferredEvidence.forcings.get() - before
  }

  protected def timed[A](body: => A): (A, Long) = {
    val start = System.nanoTime()
    val result = body
    (result, (System.nanoTime() - start) / 1000000)
  }

  /** `body` run on a thread of the JVM's default stack size; what it throws, a stack overflow included, it rethrows. */
  protected def onDefaultStack[A](body: => A): A = Execution.onStack(0)(body)

  protected def ctorName(value: Value): String = value match {
    case Value.ConstructorHead(name, _, _, _, _) => name
    case Value.VCtor(head, _, _)                 => head.name
    case packed: Value.VPacked                   => packed.codec.decodeHead(packed)._1
    case other                                   => fail(s"Expected constructor value, got $other")
  }
}

object TestSupport {
  lazy val bundledPreludeSource: String = resource("/Init/Prelude.rac")

  lazy val testPreludeSource: String = resource("/Init/TestPrelude.rac")

  /**
   * The stack the diagnostic fixtures' programs are checked on, so that the one that exhausts it,
   * `evaluation-too-deep`, does so on every machine, and promptly.
   */
  val FixtureStack: Long = 4L << 20

  /**
   * The sealed Lease and Tok capabilities of spec §5.1 and `withLease` of spec §4.4, with the module's helpers, which
   * alone make and consume them: `issue` mints a token for a lease's holder, in the lease's lifetime, and `burn`
   * consumes one.
   */
  val leaseModule: String =
    """
      |sealed inductive Lease (l: Lifetime) : Type { scope = l }
      | | mk : Lease(l)
      |
      |sealed inductive Tok (l: Lifetime) : Type { kind = lin, scope = l }
      | | mk : Tok(l)
      |
      |def withLease {k: Kind}{S: Lifetime}{A: Type { kind = k, scope = S }}{kf: Kind}{Sf: Lifetime}
      |    (f: { kind = kf, scope = Sf } (l: Lifetime) -> Lease(l) -> A): A :=
      |  scope l => f(l, Lease.mk(l))
      |
      |def issue {l: Lifetime}(h: Lease(l)): Tok(l) := Tok.mk(l)
      |
      |def useLease {l: Lifetime}(h: Lease(l)): Nat := 2
      |
      |def burn {l: Lifetime}(t: Tok(l)): Nat := match t returning Nat with
      | | .mk => 1
      |""".stripMargin

  /**
   * A String layout (docs/kernel.md, "Strings") to follow the bundled prelude, whose `Char.ofNat` returns `charOfNat`
   * of its parameter `value`, with `String.append`, and `someChar`, a character of no known scalar.
   */
  def stringLayoutSource(charOfNat: String): String =
    s"""
       |struct Char : Type
       | | mk (value: Nat) : Char
       |
       |namespace Char {
       |  def ofNat (value: Nat): Char := $charOfNat
       |}
       |
       |struct String : Type
       | | mk (data: List(Char)) : String
       |
       |namespace String {
       |  def append (a: String)(b: String): String := String.mk(List.append(a.data, b.data))
       |}
       |
       |axiom someChar : Char
       |""".stripMargin

  /**
   * The trusted prelude `base` followed by `assumptions`. Only the trusted prelude declares axioms (spec §7.3), so a
   * test assumes one the way a program does, with a custom prelude.
   */
  def preludeAssuming(base: String, assumptions: String): Prelude.Config =
    Prelude.fromSource("assumptions", preludeSourceAssuming(base, assumptions))

  /** The source of `preludeAssuming(base, assumptions)`. */
  def preludeSourceAssuming(base: String, assumptions: String): String = base + "\n" + assumptions

  private def resource(path: String): String = {
    val stream = getClass.getResourceAsStream(path)
    try new String(stream.readAllBytes(), StandardCharsets.UTF_8)
    finally stream.close()
  }
}
