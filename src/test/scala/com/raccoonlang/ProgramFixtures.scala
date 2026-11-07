package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

import com.raccoonlang.ModuleChecker.{Options, PreludeSource}
import munit.Assertions._

/** Shared helpers for suites whose tests are programs given as source text. */
object ProgramFixtures {

  /**
   * A program, checked and run: its body's value, if it has one, or its error, with how to report it and the source id
   * its own spans carry.
   */
  private final case class Checked(
      outcome: Either[TypeError, Option[Value]],
      report: TypeError => String,
      entry: Option[SourceId]
  )

  /**
   * How a suite checks and runs its programs: over `prelude`, with or without user axioms, as the CLI does. With
   * `roots`, a program is an entry file of its own in a directory searched after `roots`, so it can import their
   * modules, and it is checked by a `ModuleChecker` the suite's programs share, so each module of `roots` checks once;
   * otherwise it is a single module that imports nothing, run by `Interpreter.run`.
   */
  final class Programs(prelude: Prelude.Config, allowUserAxioms: Boolean, roots: Vector[Path] = Vector.empty) {
    private lazy val checker = new ModuleChecker
    private lazy val entries = Files.createTempDirectory("raccoon-program")
    private var programCount = 0

    private def single(src: String): SurfaceAst.Program = {
      assert(roots.isEmpty, "a program over source roots is checked as an entry")
      LanguageParser.parseProgram(src) match {
        case Success(program, _, _) => program
        case err: Failure           => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
      }
    }

    private def check(src: String): Checked =
      if (roots.isEmpty) {
        val outcome =
          try Right(Interpreter.run(Elaborator.elab(single(src), prelude), prelude, allowUserAxioms))
          catch { case t: TypeError => Left(t) }
        Checked(outcome, ErrorReporter.pretty(_, ErrorReporter.Source(src)), None)
      } else {
        programCount += 1
        val entry = Files.write(entries.resolve(s"Program$programCount.rac"), src.getBytes(StandardCharsets.UTF_8))
        val options =
          Options(roots :+ entries, PreludeSource.Given("fixture", prelude), allowUserAxioms, stackBytes = 0)
        val result = checker.run(options).check(entry, entry.toString)
        val outcome = result.outcome match {
          case Left(t: TypeError) => Left(t)
          case Left(other)        => throw other
          case Right(body)        => Right(body.map(_.value))
        }
        Checked(outcome, ErrorReporter.pretty(_, result.sources), result.sources.headOption.map(_.sourceId))
      }

    /** The elaborated program, which imports nothing. */
    def parse(src: String): CoreAst.Program = Elaborator.elab(single(src), prelude)

    /** Checks and runs the program, throwing its `TypeError` if it does not check. */
    def runChecked(src: String): Option[Value] = check(src).outcome.fold(throw _, identity)

    /** Checks and runs the program, failing the test with a located report if it does not check. */
    def run(src: String)(implicit loc: munit.Location): Option[Value] = {
      val checked = check(src)
      checked.outcome.fold(t => fail(checked.report(t)), identity)
    }

    /** The value of the program's body. */
    def runProgram(src: String)(implicit loc: munit.Location): Value = run(src).getOrElse(fail("Program has no body"))

    /** The value of the program's body, printed as the CLI prints it, so a proof call in it that fails to run fails. */
    def result(src: String)(implicit loc: munit.Location): String = PrettyPrinter.printResult(runProgram(src))

    /** The environment after the declarations of the program, which imports nothing; they must check. */
    def declsEnv(src: String)(implicit loc: munit.Location): Env = {
      val program = single(src)
      try
        Elaborator.elab(program, prelude).decls.foldLeft(Interpreter.initialEnv(prelude)) { (env, decl) =>
          Interpreter.evalDecl(decl, env)
        }
      catch { case t: TypeError => fail(ErrorReporter.pretty(t, ErrorReporter.Source(src))) }
    }

    /**
     * The program fails to elaborate, check or run with `T` in its own source, located exactly at `at`: at its
     * occurrence inside the last occurrence of `within`, which is `at` itself by default.
     */
    def assertErrorAt[T <: TypeError](src: String, at: String, within: String = null)(implicit
        loc: munit.Location,
        ct: reflect.ClassTag[T]
    ): T = {
      val checked = check(src)
      val error = checked.outcome match {
        case Left(error: T) => error
        case Left(other)    => fail(s"expected ${ct.runtimeClass.getSimpleName}, got ${checked.report(other)}")
        case Right(_)       => fail(s"expected ${ct.runtimeClass.getSimpleName}, but the program checked")
      }
      val span = error.span.getOrElse(fail(s"${error.getMessage} has no span"))
      assertEquals(span.source, checked.entry, "the error is not in the program's own source")
      val context = Option(within).getOrElse(at)
      assert(src.lastIndexOf(context) >= 0 && context.indexOf(at) >= 0, s"$at does not occur in $context")
      val start = src.lastIndexOf(context) + context.indexOf(at)
      assertEquals(src.substring(span.start, span.end), at, error.getMessage)
      assertEquals(span.start, start, s"${error.getMessage} at ${src.substring(span.start, span.end)}")
      error
    }
  }

  /**
   * `LNats`, a linear list of natural numbers, and `count`, its length, which consumes it: linear values with copyable
   * contents, for suites about the ledger. A family in `Lin` is linear whatever its fields.
   */
  val lnats: String =
    """
      |inductive LNats : Lin(Level.zero)
      | | nil : LNats
      | | cons (head: Nat)(tail: LNats) : LNats
      |
      |def count (xs: LNats) : Nat decreases structural(xs) := {
      |  match xs with
      |  | LNats.nil => 0
      |  | LNats.cons h t => Nat.succ(count(t))
      |}
      |
      |""".stripMargin

  /** A linear pair of linear values, which the packet operations return. */
  val both: String =
    """
      |inductive Both (A: Lin($u))(B: Lin($v)) : Lin(Level.max(u, v))
      | | mk (fst: $A in Lin($u))(snd: $B in Lin($v)) : Both(A, B)
      |
      |""".stripMargin

  /**
   * `Both`, and `splitToks` and `joinToks`, packet split and join over any protocol, by structural recursion on the
   * unrestricted first list, matching the packet in each branch (docs/kernel.md, "Resource protocols"). `splitToks`
   * returns a `Both` of packets.
   */
  val packets: String =
    both +
      """
        |def splitToks (Atom: Type)(Step: (consumed: List(Atom)) -> (produced: List(Atom)) -> Prop)(init: List(Atom))
        |    (s: Protocol.Inst(Protocol.Proto.mk(Atom, Step), init))(A: List(Atom))(B: List(Atom))
        |    (toks: Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, List.append(A, B)))
        |    : Both(Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, A), Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, B)) decreases structural(A) := {
        |  match A with
        |  | List.nil => Both.mk(Protocol.Toks.nil(Protocol.Proto.mk(Atom, Step), init, s), toks)
        |  | List.cons a rest => {
        |    match toks with
        |    | Protocol.Toks.cons b t C more => {
        |      let (left, right) := splitToks(Atom, Step, init, s, rest, B, more)
        |      Both.mk(Protocol.Toks.cons(Protocol.Proto.mk(Atom, Step), init, s, a, t, rest, left), right)
        |    }
        |  }
        |}
        |
        |def joinToks (Atom: Type)(Step: (consumed: List(Atom)) -> (produced: List(Atom)) -> Prop)(init: List(Atom))
        |    (s: Protocol.Inst(Protocol.Proto.mk(Atom, Step), init))(A: List(Atom))(B: List(Atom))
        |    (left: Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, A))(right: Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, B))
        |    : Protocol.Toks(Protocol.Proto.mk(Atom, Step), init, s, List.append(A, B)) decreases structural(A) := {
        |  match A with
        |  | List.nil => {
        |    match left with
        |    | Protocol.Toks.nil => right
        |  }
        |  | List.cons a rest => {
        |    match left with
        |    | Protocol.Toks.cons b t C more =>
        |        Protocol.Toks.cons(Protocol.Proto.mk(Atom, Step), init, s, a, t, List.append(rest, B), joinToks(Atom, Step, init, s, rest, B, more, right))
        |  }
        |}
        |
        |""".stripMargin
}
