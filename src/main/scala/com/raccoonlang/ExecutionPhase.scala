package com.raccoonlang

/** Public owner of the staged, checked execution capabilities. */
object Execution {

  /**
   * A surface program after elaboration, but before kernel checking.
   *
   * The constructor, CoreAst payload, and selected prelude are private to this API owner. The latter is deliberately
   * retained so checking cannot accidentally use a context different from the one that resolved names.
   */
  final class ElaboratedProgram private (
      private val core0: CoreAst.Program,
      private val prelude0: Prelude.Config
  )

  private object ElaboratedProgram {
    def make(core: CoreAst.Program, prelude: Prelude.Config): ElaboratedProgram =
      new ElaboratedProgram(core, prelude)

    def checkedInput(program: ElaboratedProgram): (CoreAst.Program, Prelude.Config) =
      (program.core0, program.prelude0)
  }

  /**
   * The result of checking and evaluating an elaborated program.
   *
   * Checking publishes declarations and computes the body in one pass. Keeping only that result here prevents the
   * public runner from accidentally introducing a second, unchecked evaluation world.
   */
  final class CheckedProgram private (private val result0: Option[Value]) {
    def result: Option[Value] = result0
  }

  private object CheckedProgram {
    def make(result: Option[Value]): CheckedProgram = new CheckedProgram(result)
  }

  /** Checking rejected the program: one diagnostic per independent failure, in source order. */
  final case class CheckFailure(diagnostics: Vector[Diagnostic])
    extends RuntimeException
    with scala.util.control.NoStackTrace {
    require(diagnostics.nonEmpty, "a check failure must carry at least one diagnostic")

    override def getMessage: String = diagnostics.map(_.getMessage).mkString("\n")
  }

  /** Elaborate a surface program while binding its selected prelude to the resulting phase artifact. */
  def elaborate(p: SurfaceAst.Program, prelude: Prelude.Config = Prelude.default): ElaboratedProgram =
    ElaboratedProgram.make(Elaborator.elab(p, prelude), prelude)

  /**
   * `body` run on a thread of its own whose stack is `stackBytes` bytes, as `Thread` takes it (the JVM may round it,
   * and zero leaves it to the JVM's default); the caller waits for it. What `body` returns is returned, and what it
   * throws, a stack overflow included, is rethrown here: nothing is caught on the way.
   *
   * Checking and evaluation recurse on the host stack, so this is how a caller chooses their depth: the CLI runs its
   * whole pipeline on one, of `--stack` bytes (PROOF_BY_EVALUATION §2.5). When the thread ends, the checker's
   * thread-local state goes with it, which is part of what `EvaluationTooDeep` leaves unsafe to check on.
   */
  def onStack[A](stackBytes: Long)(body: => A): A = {
    var outcome: Either[Throwable, A] = Left(new IllegalStateException("the checking thread did not finish"))
    val thread = new Thread(
      null,
      () =>
        outcome =
          try Right(body)
          catch { case thrown: Throwable => Left(thrown) },
      "raccoon-check",
      stackBytes
    )
    thread.start()
    thread.join()
    outcome.fold(throw _, identity)
  }

  /** Check using exactly the prelude captured during elaboration. */
  def check(program: ElaboratedProgram): CheckedProgram = {
    val (core, prelude) = ElaboratedProgram.checkedInput(program)
    CheckedProgram.make(TypeChecker.checkRaw(core, prelude))
  }
}
