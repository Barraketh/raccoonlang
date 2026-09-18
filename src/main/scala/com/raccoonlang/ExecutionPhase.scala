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

  /** Elaborate a surface program while binding its selected prelude to the resulting phase artifact. */
  def elaborate(p: SurfaceAst.Program, prelude: Prelude.Config = Prelude.default): ElaboratedProgram =
    ElaboratedProgram.make(Elaborator.elab(p, prelude), prelude)

  /** Check using exactly the prelude captured during elaboration. */
  def check(program: ElaboratedProgram): CheckedProgram = {
    val (core, prelude) = ElaboratedProgram.checkedInput(program)
    CheckedProgram.make(TypeChecker.checkRaw(core, prelude))
  }
}
