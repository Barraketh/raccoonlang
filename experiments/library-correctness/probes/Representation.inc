
// TEMPORARY proof probe appended by run.py to a copy of the defining module.
// This is not an operation available to a client of the unchanged library.
namespace Core {
  def representationBody: Cuda.Block := Cuda.Block.seq(Cuda.Stmt.ifElse(
    Cuda.Expr.bin(Cuda.BinOp.eq, Cuda.Expr.special(Cuda.Builtin.threadX), Cuda.Expr.lit(0)),
    Cuda.Block.seq(Cuda.Stmt.sync, Cuda.Block.done), Cuda.Block.done), Cuda.Block.done)
  def representationCounterexample: Program := Program.mk(Cuda.Kernel.mk("divergent_barrier",
    List.nil(Cuda.Param), 0, Core.representationBody, Option.none(Cuda.Launcher)), 32, 1)
}
