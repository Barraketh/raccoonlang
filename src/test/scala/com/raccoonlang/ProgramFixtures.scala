package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}

import munit.Assertions._

/** Shared helpers for suites whose tests are programs given as source text. */
object ProgramFixtures {

  /** A parsed program, how to report an error in its sources, and the source id its own spans carry. */
  private final case class Read(program: SurfaceAst.Program, report: TypeError => String, entry: Option[SourceId])

  /**
   * How a suite checks and runs its programs: over `prelude`, with or without user axioms, through `Interpreter.run` as
   * the CLI does. With `roots`, a program is the entry file of a fresh directory searched after `roots`, so it can
   * import their modules; otherwise it is a single module that imports nothing.
   */
  final class Programs(prelude: Prelude.Config, allowUserAxioms: Boolean, roots: Vector[Path] = Vector.empty) {

    private def read(src: String): Read =
      if (roots.isEmpty)
        LanguageParser.parseProgram(src) match {
          case Success(program, _, _) => Read(program, ErrorReporter.pretty(_, ErrorReporter.Source(src)), None)
          case err: Failure           => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
        }
      else {
        val root = Files.createTempDirectory("raccoon-program")
        val entry = Files.write(root.resolve("Main.rac"), src.getBytes(StandardCharsets.UTF_8))
        val loaded = ModuleLoader.load(entry, ModuleLoader.LoadConfig(roots :+ root, prelude))
        Read(
          loaded.program,
          ErrorReporter.pretty(_, loaded),
          loaded.sources.find(_.path == entry.toRealPath()).map(_.sourceId)
        )
      }

    private def check(read: Read): Option[Value] =
      Interpreter.run(Elaborator.elab(read.program, prelude), prelude, allowUserAxioms)

    /** The elaborated program. */
    def parse(src: String): CoreAst.Program = Elaborator.elab(read(src).program, prelude)

    /** Checks and runs the program, throwing its `TypeError` if it does not check. */
    def runChecked(src: String): Option[Value] = check(read(src))

    /** Checks and runs the program, failing the test with a located report if it does not check. */
    def run(src: String)(implicit loc: munit.Location): Option[Value] = {
      val program = read(src)
      try check(program)
      catch { case t: TypeError => fail(program.report(t)) }
    }

    /** The value of the program's body. */
    def runProgram(src: String)(implicit loc: munit.Location): Value = run(src).getOrElse(fail("Program has no body"))

    /** The value of the program's body, printed. */
    def result(src: String)(implicit loc: munit.Location): String = PrettyPrinter.print(runProgram(src))

    /** The environment after the program's declarations, which must check. */
    def declsEnv(src: String)(implicit loc: munit.Location): Env = {
      val program = read(src)
      try
        Elaborator.elab(program.program, prelude).decls.foldLeft(Interpreter.initialEnv(prelude)) { (env, decl) =>
          Interpreter.evalDecl(decl, env)
        }
      catch { case t: TypeError => fail(program.report(t)) }
    }

    /**
     * The program fails to elaborate, check or run with `T` in its own source, located exactly at `at`: at its
     * occurrence inside the last occurrence of `within`, which is `at` itself by default.
     */
    def assertErrorAt[T <: TypeError](src: String, at: String, within: String = null)(implicit
        loc: munit.Location,
        ct: reflect.ClassTag[T]
    ): T = {
      val program = read(src)
      val error = intercept[T](check(program))
      val span = error.span.getOrElse(fail(s"${error.getMessage} has no span"))
      assertEquals(span.source, program.entry, "the error is not in the program's own source")
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
