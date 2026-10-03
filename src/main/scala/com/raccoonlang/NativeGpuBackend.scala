package com.raccoonlang

import NativeGpuAst.InputMetadata
import NativeGpuAst.Kernel

/**
 * Opt-in host interpreter for the existing checked Cuda AST. The caller owns only immutable source inputs/results; each
 * invocation allocates all writable device-model state privately.
 */
object NativeGpuBackend {
  final class Plan private[raccoonlang] (
      private[raccoonlang] val kernel: Kernel,
      private[raccoonlang] val metadata: InputMetadata
  )

  final case class Inputs(a: Vector[Int], b: Vector[Int])

  final case class Stats(
      warpSteps: BigInt,
      asyncCompletions: BigInt,
      tmaBytes: BigInt,
      scalarMuls: BigInt,
      scalarAdds: BigInt,
      mmaInstructions: BigInt,
      tmemLoads: BigInt,
      tmaStores: BigInt
  )

  final case class DecodeFailure(path: String, detail: String) {
    def message: String = s"$path: $detail"
  }

  sealed trait Failure {
    def category: String
    def message: String
    final def rendered: String = if (message.isEmpty) category else s"$category: $message"
  }
  case object FuelExhausted extends Failure {
    override val category: String = "fuel-exhausted"
    override val message: String = ""
  }
  case object Deadlocked extends Failure {
    override val category: String = "deadlocked"
    override val message: String = ""
  }
  final case class Unsupported(message: String) extends Failure {
    override val category: String = "unsupported"
  }
  final case class DeviceFault(message: String) extends Failure {
    override val category: String = "device-fault"
  }
  final case class InvalidState(message: String) extends Failure {
    override val category: String = "invalid-state"
  }
  case object IncompleteOutput extends Failure {
    override val category: String = "incomplete-output"
    override val message: String = ""
  }
  case object NotQuiescent extends Failure {
    override val category: String = "not-quiescent"
    override val message: String = ""
  }

  final case class Result(outputs: Vector[Int], stats: Stats, failure: Option[Failure]) {
    def errors: String = failure.fold("ok")(_.rendered)
    def completed: Boolean = failure.isEmpty
  }

  /** Decode the exact `Cuda.Kernel` and `TinyDevice.Inputs` values produced by the checked source API. */
  def decodePlan(
      kernelValue: Value,
      metadataValue: Value,
      strings: Option[Value.ValidatedStringLayout]
  ): Either[DecodeFailure, Plan] =
    for {
      _ <- checkedFamily(kernelValue, "Cuda.Kernel", "Cuda.Kernel.mk")
      _ <- checkedFamily(metadataValue, "Evaluator.TinyDevice.Inputs", "Evaluator.TinyDevice.Inputs.mk")
      kernel <- NativeGpuAst.kernel(kernelValue, strings).left.map(fromAstFailure)
      metadata <- NativeGpuAst.inputsMetadata(metadataValue, strings).left.map(fromAstFailure)
      _ <- validateSubset(kernel, metadata)
    } yield new Plan(kernel, metadata)

  /** Convert the source API's already-prepared row-major Nat lists into immutable Z/257 host input vectors. */
  def decodeInputs(aList: Value, bList: Value): Either[DecodeFailure, Inputs] =
    for {
      a <- NativeGpuAst.naturalList(aList, "TinyDevice.inputAList").left.map(fromAstFailure)
      b <- NativeGpuAst.naturalList(bList, "TinyDevice.inputBList").left.map(fromAstFailure)
      values <- toRingInputs(a, b)
    } yield values

  private def toRingInputs(a: Vector[BigInt], b: Vector[BigInt]): Either[DecodeFailure, Inputs] = {
    val bad = (a.iterator ++ b.iterator).find(value => value < 0 || value >= 257)
    bad match {
      case Some(value) => Left(DecodeFailure("TinyDevice.Inputs", s"input $value is outside Z/257"))
      case None if a.length != 8192 || b.length != 8192 =>
        Left(DecodeFailure("TinyDevice.Inputs", s"expected 8192 A and B cells, got ${a.length} and ${b.length}"))
      case None => Right(Inputs(a.map(_.toInt), b.map(_.toInt)))
    }
  }

  def run(plan: Plan, inputs: Inputs, fuel: BigInt = BigInt(10000000)): Result =
    NativeGpuMachine.run(plan, inputs, fuel)

  private def checkedFamily(value: Value, family: String, constructor: String): Either[DecodeFailure, Unit] =
    value match {
      case Value.VCtor(head, _, tpe)
          if head.name == constructor && Value.InductiveFamilyValue.unapply(tpe).exists(_.head.name == family) =>
        Right(())
      case other => Left(DecodeFailure(family, s"expected checked $constructor value, got $other"))
    }

  private def fromAstFailure(failure: NativeGpuAst.DecodeFailure): DecodeFailure =
    DecodeFailure(failure.path, failure.detail)

  private def validateSubset(kernel: Kernel, metadata: InputMetadata): Either[DecodeFailure, Unit] = {
    val expectedA = NativeGpuAst.MapEncoding(
      "A_map",
      NativeGpuAst.MapUse.Load,
      NativeGpuAst.Param.Input(NativeGpuAst.DType.BF16, "A"),
      "M",
      "K",
      64,
      128
    )
    val expectedB = NativeGpuAst.MapEncoding(
      "B_map",
      NativeGpuAst.MapUse.Load,
      NativeGpuAst.Param.Input(NativeGpuAst.DType.BF16, "B"),
      "N",
      "K",
      64,
      128
    )
    val expectedC = NativeGpuAst.MapEncoding(
      "C_map",
      NativeGpuAst.MapUse.Store,
      NativeGpuAst.Param.Output(NativeGpuAst.DType.F32, "C"),
      "M",
      "N",
      32,
      32
    )
    val expectedParams = Vector(
      NativeGpuAst.Param.TensorMap(NativeGpuAst.MapUse.Load, "A_map"),
      NativeGpuAst.Param.TensorMap(NativeGpuAst.MapUse.Load, "B_map"),
      NativeGpuAst.Param.TensorMap(NativeGpuAst.MapUse.Store, "C_map"),
      NativeGpuAst.Param.Scalar(NativeGpuAst.DType.U32, "M"),
      NativeGpuAst.Param.Scalar(NativeGpuAst.DType.U32, "N"),
      NativeGpuAst.Param.Scalar(NativeGpuAst.DType.U32, "K")
    )
    val launcherParams = Vector(
      NativeGpuAst.Param.Input(NativeGpuAst.DType.BF16, "A"),
      NativeGpuAst.Param.Input(NativeGpuAst.DType.BF16, "B"),
      NativeGpuAst.Param.Output(NativeGpuAst.DType.F32, "C"),
      NativeGpuAst.Param.Scalar(NativeGpuAst.DType.U32, "M"),
      NativeGpuAst.Param.Scalar(NativeGpuAst.DType.U32, "N"),
      NativeGpuAst.Param.Scalar(NativeGpuAst.DType.U32, "K")
    )
    import NativeGpuAst.BinOp
    import NativeGpuAst.Expr
    val ceilDivN = Expr.Bin(BinOp.Div, Expr.Bin(BinOp.Add, Expr.Param("N"), Expr.Lit(127)), Expr.Lit(128))
    val ceilDivM = Expr.Bin(BinOp.Div, Expr.Bin(BinOp.Add, Expr.Param("M"), Expr.Lit(127)), Expr.Lit(128))
    val expectedGrid = NativeGpuAst.Grid.Blocks(ceilDivN, ceilDivM)
    val expectedRequires = Vector(
      Expr.Bin(
        BinOp.Lt,
        Expr.Bin(BinOp.Mul, Expr.Cast(NativeGpuAst.DType.U64, Expr.Param("M")), Expr.Param("N")),
        Expr.Lit64(BigInt(4294967296L))
      ),
      Expr.Bin(BinOp.Lt, Expr.Param("M"), Expr.Lit64(BigInt(2147483648L))),
      Expr.Bin(BinOp.Lt, Expr.Param("N"), Expr.Lit64(BigInt(2147483648L))),
      Expr.Bin(BinOp.Lt, Expr.Param("K"), Expr.Lit64(BigInt(2147483648L))),
      Expr.Bin(BinOp.Eq, Expr.Bin(BinOp.Rem, Expr.Param("N"), Expr.Lit(4)), Expr.Lit(0))
    )
    val validMetadata = metadata.m == 128 && metadata.n == 128 && metadata.k == 64 &&
      metadata.dynamicShared > 0 && metadata.dynamicShared <= 262144 && metadata.dynamicShared % 4 == 0 &&
      metadata.aMap == expectedA && metadata.bMap == expectedB && metadata.cMap == expectedC
    val validKernel = kernel.name == "tinygemm" && kernel.params == expectedParams &&
      kernel.launcher.exists(launcher =>
        launcher.params == launcherParams && launcher.maps == Vector(expectedA, expectedB, expectedC) &&
          launcher.grid == expectedGrid && launcher.requires == expectedRequires && launcher.block == 256
      )
    if (!validMetadata)
      Left(
        DecodeFailure(
          "TinyDevice.Inputs",
          "prepared dimensions, extent, or full map encodings are outside the checked 128x128x64 subset"
        )
      )
    // The exact five checked requirement expressions above hold for this fixed 128/128/64 subset.
    else if (!validKernel || kernel.dynamicShared != metadata.dynamicShared)
      Left(
        DecodeFailure(
          "Cuda.Kernel",
          "kernel launcher parameters or dynamic shared extent are outside the checked TinyGEMM subset"
        )
      )
    else Right(())
  }
}
