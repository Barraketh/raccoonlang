package com.raccoonlang

/**
 * Immutable host representation of the existing `Cuda` AST. Decoding preserves unsupported constructors so a host run
 * rejects one only if control flow reaches it.
 */
private[raccoonlang] object NativeGpuAst {
  sealed trait DType
  object DType {
    case object U32 extends DType
    case object U64 extends DType
    case object F32 extends DType
    case object BF16 extends DType
    case object Bool extends DType
  }

  sealed trait Builtin
  object Builtin {
    case object ThreadX extends Builtin
    case object BlockX extends Builtin
    case object BlockY extends Builtin
    case object GridX extends Builtin
    case object Warp extends Builtin
    case object Lane extends Builtin
  }

  sealed trait BinOp
  object BinOp {
    case object Add extends BinOp
    case object Sub extends BinOp
    case object Mul extends BinOp
    case object Div extends BinOp
    case object Rem extends BinOp
    case object Lt extends BinOp
    case object Eq extends BinOp
    case object Land extends BinOp
    case object Shl extends BinOp
    case object Shr extends BinOp
    case object Bor extends BinOp
    case object Band extends BinOp
    case object Bxor extends BinOp
  }

  sealed trait Expr
  object Expr {
    final case class Var(id: BigInt) extends Expr
    final case class Lit(value: BigInt) extends Expr
    final case class Lit64(value: BigInt) extends Expr
    final case class Zero(tpe: DType) extends Expr
    final case class Param(name: String) extends Expr
    final case class Special(builtin: Builtin) extends Expr
    final case class Bin(op: BinOp, left: Expr, right: Expr) extends Expr
    final case class Max(left: Expr, right: Expr) extends Expr
    final case class Fma(a: Expr, b: Expr, c: Expr) extends Expr
    final case class Select(condition: Expr, yes: Expr, no: Expr) extends Expr
    final case class Index(base: Expr, index: Expr) extends Expr
    final case class Cast(tpe: DType, value: Expr) extends Expr
    final case class SharedAddr(offset: BigInt) extends Expr
    final case class SharedPtr(tpe: DType, offset: BigInt) extends Expr
    final case class ParamAddr(name: String) extends Expr
  }

  sealed trait MapUse
  object MapUse {
    case object Load extends MapUse
    case object Store extends MapUse
  }

  sealed trait Param
  object Param {
    final case class Input(tpe: DType, name: String) extends Param
    final case class Output(tpe: DType, name: String) extends Param
    final case class Scalar(tpe: DType, name: String) extends Param
    final case class TensorMap(use: MapUse, name: String) extends Param
  }

  final case class MapEncoding(
      param: String,
      use: MapUse,
      source: Param,
      rows: String,
      cols: String,
      inner: BigInt,
      outer: BigInt
  )

  sealed trait Grid
  object Grid {
    final case class Blocks(x: Expr, y: Expr) extends Grid
    final case class Pairs(x: Expr, y: Expr) extends Grid
    final case class PersistentPairs(tiles: Expr) extends Grid
  }

  sealed trait Group
  object Group {
    case object One extends Group
    case object Two extends Group
  }

  sealed trait Window
  object Window {
    case object Cta extends Window
    case object Cluster extends Window
  }

  sealed trait BarrierScope
  object BarrierScope {
    case object Cta extends BarrierScope
    case object Cluster extends BarrierScope
  }

  sealed trait Scope
  object Scope {
    case object Cta extends Scope
    case object Cluster extends Scope
    case object Gpu extends Scope
  }

  sealed trait Arrival
  object Arrival {
    case object One extends Arrival
    final case class Count(value: Expr) extends Arrival
    final case class ExpectTx(bytes: Expr) extends Arrival
  }

  sealed trait ThreadSync
  object ThreadSync {
    case object Before extends ThreadSync
    case object After extends ThreadSync
  }

  sealed trait BulkWaitKind
  object BulkWaitKind {
    case object Read extends BulkWaitKind
    case object Complete extends BulkWaitKind
  }

  sealed trait TmemWaitKind
  object TmemWaitKind {
    case object Load extends TmemWaitKind
    case object Store extends TmemWaitKind
  }

  sealed trait TmemShape
  object TmemShape {
    case object S32x32b extends TmemShape
  }

  sealed trait Word
  object Word {
    case object U32 extends Word
    case object F32 extends Word
  }

  sealed trait Rounding
  object Rounding {
    case object Rn extends Rounding
    case object Rz extends Rounding
    case object Rm extends Rounding
    case object Rp extends Rounding
  }

  sealed trait RegChange
  object RegChange {
    case object Inc extends RegChange
    case object Dec extends RegChange
  }

  sealed trait SpecialReg
  object SpecialReg {
    case object ClusterCtaRank extends SpecialReg
    case object ClusterIdX extends SpecialReg
    case object NClusterIdX extends SpecialReg
  }

  final case class SmemDesc(base: Expr, lbo: BigInt, step: BigInt)
  final case class InstrDesc(m: BigInt, n: BigInt, transposeB: Boolean)

  sealed trait MmaA
  object MmaA {
    final case class Smem(desc: SmemDesc) extends MmaA
    final case class Tmem(address: Expr) extends MmaA
  }

  sealed trait Instr
  object Instr {
    final case class BarSync(id: Expr, threads: Expr) extends Instr
    final case class MbarInit(bar: Expr, count: Expr) extends Instr
    final case class MbarInval(bar: Expr) extends Instr
    final case class MbarArrive(window: Window, bar: Expr, arrival: Arrival) extends Instr
    final case class MbarWait(scope: BarrierScope, bar: Expr, parity: Expr) extends Instr
    case object FenceMbarInit extends Instr
    case object FenceProxyAsync extends Instr
    final case class TcFence(side: ThreadSync) extends Instr
    case object ClusterArrive extends Instr
    case object ClusterWait extends Instr
    final case class TmaLoad(group: Group, dst: Expr, map: Expr, x: Expr, y: Expr, bar: Expr) extends Instr
    final case class TmaStore(map: Expr, x: Expr, y: Expr, src: Expr) extends Instr
    case object BulkCommit extends Instr
    final case class BulkWait(kind: BulkWaitKind, pending: BigInt) extends Instr
    final case class TmemAlloc(group: Group, slot: Expr, cols: Expr) extends Instr
    final case class TmemRelinquish(group: Group) extends Instr
    final case class TmemDealloc(group: Group, address: Expr, cols: Expr) extends Instr
    final case class Mma(
        group: Group,
        accumulator: Expr,
        a: MmaA,
        b: SmemDesc,
        descriptor: InstrDesc,
        accumulate: Expr
    ) extends Instr
    final case class TcCommit(group: Group, bar: Expr, multicast: Option[BigInt]) extends Instr
    final case class TmemLoad(shape: TmemShape, destinations: Vector[BigInt], address: Expr) extends Instr
    final case class TmemStore(shape: TmemShape, word: Word, address: Expr, values: Vector[Expr]) extends Instr
    final case class TmemWait(kind: TmemWaitKind) extends Instr
    final case class Elect(flag: BigInt) extends Instr
    final case class Shfl(destination: BigInt, value: Expr, lane: BigInt) extends Instr
    final case class VoteAny(destination: BigInt, predicate: Expr) extends Instr
    final case class SetMaxNReg(change: RegChange, count: BigInt) extends Instr
    final case class MovF32(destination: BigInt, bits: BigInt) extends Instr
    final case class Ex2(destination: BigInt, value: Expr) extends Instr
    final case class Lg2(destination: BigInt, value: Expr) extends Instr
    final case class Ex2Emulated(destination: BigInt, value: Expr) extends Instr
    final case class Rcp(rounding: Rounding, destination: BigInt, value: Expr) extends Instr
    final case class CvtBf16x2(destination: BigInt, high: Expr, low: Expr) extends Instr
    final case class LdRelaxed(scope: Scope, destination: BigInt, address: Expr) extends Instr
    final case class CasRelaxed(scope: Scope, destination: BigInt, address: Expr, expected: Expr, desired: Expr)
      extends Instr
    final case class MovSpecial(destination: BigInt, reg: SpecialReg) extends Instr
    final case class Mapa(destination: BigInt, address: Expr, rank: Expr) extends Instr
    final case class StShared(address: Expr, values: Vector[Expr]) extends Instr
  }

  sealed trait Stmt
  object Stmt {
    final case class Decl(tpe: DType, id: BigInt, init: Expr, mutable: Boolean) extends Stmt
    final case class DeclOut(tpe: DType, id: BigInt) extends Stmt
    final case class Assign(id: BigInt, value: Expr) extends Stmt
    final case class Store(base: Expr, index: Expr, value: Expr) extends Stmt
    final case class Shared(tpe: DType, id: BigInt, size: BigInt) extends Stmt
    final case class ForLoop(id: BigInt, start: Expr, stop: Expr, body: Block) extends Stmt
    final case class ForStride(id: BigInt, start: Expr, stop: Expr, step: Expr, body: Block) extends Stmt
    final case class IfElse(condition: Expr, yes: Block, no: Block) extends Stmt
    final case class Scoped(body: Block) extends Stmt
    case object Sync extends Stmt
    case object SyncWarp extends Stmt
    final case class Instruction(value: Instr) extends Stmt
    final case class Error(message: String) extends Stmt
  }
  final case class Block(statements: Vector[Stmt])

  final case class Launcher(
      params: Vector[Param],
      requires: Vector[Expr],
      maps: Vector[MapEncoding],
      grid: Grid,
      block: BigInt
  )
  final case class Kernel(
      name: String,
      params: Vector[Param],
      dynamicShared: BigInt,
      body: Block,
      launcher: Option[Launcher]
  )

  final case class DecodeFailure(path: String, detail: String) {
    def message: String = s"$path: $detail"
  }

  def kernel(value: Value, strings: Option[Value.ValidatedStringLayout]): Either[DecodeFailure, Kernel] =
    decode("Cuda.Kernel", value)((v, path) => new Decoder(strings).decodeKernel(v, path))

  def inputsMetadata(
      value: Value,
      strings: Option[Value.ValidatedStringLayout]
  ): Either[DecodeFailure, InputMetadata] =
    decode("TinyDevice.Inputs", value)((v, path) => new Decoder(strings).decodeInputMetadata(v, path))

  def naturalList(value: Value, path: String): Either[DecodeFailure, Vector[BigInt]] =
    decode(path, value)((v, p) => list(v, p)((item, itemPath) => nat(item, itemPath)))

  final case class InputMetadata(
      m: BigInt,
      n: BigInt,
      k: BigInt,
      dynamicShared: BigInt,
      aMap: MapEncoding,
      bMap: MapEncoding,
      cMap: MapEncoding
  )

  private def decode[A](path: String, value: Value)(f: (Value, String) => A): Either[DecodeFailure, A] =
    try Right(f(value, path))
    catch {
      case e: DecodeError              => Left(DecodeFailure(e.path, e.getMessage))
      case e: IllegalArgumentException => Left(DecodeFailure(path, e.getMessage))
    }

  private final class DecodeError(val path: String, message: String) extends RuntimeException(message)
  private def malformed(path: String, detail: String): Nothing = throw new DecodeError(path, detail)

  private def constructor(value: Value, path: String): (String, Vector[Value]) = value match {
    case Value.VCtor(head, fields, _)                        => head.name -> fields
    case head: Value.ConstructorHead if head.totalArity == 0 => head.name -> Vector.empty
    case other => malformed(path, s"expected a constructor value, got ${other.getClass.getSimpleName}")
  }

  private def expectName(actual: String, expected: String, path: String): Unit =
    if (actual != expected)
      malformed(path, s"expected $expected, got $actual")

  private def expectArity(fields: Vector[Value], expected: Int, path: String): Unit =
    if (fields.length != expected) malformed(path, s"expected $expected fields, got ${fields.length}")

  private def nat(value: Value, path: String): BigInt = value match {
    case packed: Value.VPacked => packed.natValue.getOrElse(malformed(path, "expected Nat"))
    case _ =>
      val (name, fields) = constructor(value, path)
      name match {
        case "Nat.zero"                       => BigInt(0)
        case "Nat.succ" if fields.length == 1 => nat(fields.head, s"$path.pred") + 1
        case _                                => malformed(path, s"expected Nat, got $name")
      }
  }

  private def bool(value: Value, path: String): Boolean = {
    val (name, fields) = constructor(value, path)
    expectArity(fields, 0, path)
    name match {
      case "Bool.true"  => true
      case "Bool.false" => false
      case _            => malformed(path, s"expected Bool, got $name")
    }
  }

  private def optional[A](value: Value, path: String)(f: (Value, String) => A): Option[A] = {
    val (name, fields) = constructor(value, path)
    name match {
      case "Option.none" => expectArity(fields, 0, path); None
      case "Option.some" => expectArity(fields, 1, path); Some(f(fields.head, s"$path.some"))
      case _             => malformed(path, s"expected Option, got $name")
    }
  }

  private def list[A](value: Value, path: String)(f: (Value, String) => A): Vector[A] = {
    val builder = Vector.newBuilder[A]
    var current = value
    var index = 0
    var done = false
    while (!done) {
      val (name, fields) = constructor(current, s"$path[$index]")
      name match {
        case "List.nil" =>
          expectArity(fields, 0, s"$path[$index]")
          done = true
        case "List.cons" =>
          expectArity(fields, 2, s"$path[$index]")
          builder += f(fields(0), s"$path[$index]")
          current = fields(1)
          index += 1
        case _ => malformed(s"$path[$index]", s"expected List.nil/cons, got $name")
      }
    }
    builder.result()
  }

  private final class Decoder(strings: Option[Value.ValidatedStringLayout]) {
    private def str(value: Value, path: String): String =
      PrettyPrinter.rawString(value, strings).getOrElse(malformed(path, "expected checked String value"))

    def decodeInputMetadata(value: Value, path: String): InputMetadata = {
      val (name, fields) = constructor(value, path)
      expectName(name, "Evaluator.TinyDevice.Inputs.mk", path)
      expectArity(fields, 9, path)
      InputMetadata(
        nat(fields(0), s"$path.m"),
        nat(fields(1), s"$path.n"),
        nat(fields(2), s"$path.k"),
        nat(fields(3), s"$path.dynamicSharedBytes"),
        decodeMap(fields(4), s"$path.aMap"),
        decodeMap(fields(5), s"$path.bMap"),
        decodeMap(fields(6), s"$path.cMap")
      )
    }

    def decodeKernel(value: Value, path: String): Kernel = {
      val (name, fields) = constructor(value, path)
      expectName(name, "Cuda.Kernel.mk", path)
      expectArity(fields, 5, path)
      Kernel(
        str(fields(0), s"$path.name"),
        list(fields(1), s"$path.params")(decodeParam),
        nat(fields(2), s"$path.dynamicShared"),
        decodeBlock(fields(3), s"$path.body"),
        optional(fields(4), s"$path.launcher")(decodeLauncher)
      )
    }

    private def decodeLauncher(value: Value, path: String): Launcher = {
      val (name, fields) = constructor(value, path)
      expectName(name, "Cuda.Launcher.mk", path)
      expectArity(fields, 5, path)
      Launcher(
        list(fields(0), s"$path.params")(decodeParam),
        list(fields(1), s"$path.requires")(decodeExpr),
        list(fields(2), s"$path.maps")(decodeMap),
        decodeGrid(fields(3), s"$path.grid"),
        nat(fields(4), s"$path.block")
      )
    }

    private def decodeDType(value: Value, path: String): DType = {
      val (name, fields) = constructor(value, path)
      expectArity(fields, 0, path)
      name match {
        case "Cuda.DType.u32"  => DType.U32
        case "Cuda.DType.u64"  => DType.U64
        case "Cuda.DType.f32"  => DType.F32
        case "Cuda.DType.bf16" => DType.BF16
        case "Cuda.DType.bool" => DType.Bool
        case _                 => malformed(path, s"unknown Cuda.DType $name")
      }
    }

    private def decodeParam(value: Value, path: String): Param = {
      val (name, fields) = constructor(value, path)
      name match {
        case "Cuda.Param.input" | "Cuda.Param.output" | "Cuda.Param.scalar" =>
          expectArity(fields, 2, path)
          val tpe = decodeDType(fields(0), s"$path.dtype")
          val paramName = str(fields(1), s"$path.name")
          name match {
            case "Cuda.Param.input"  => Param.Input(tpe, paramName)
            case "Cuda.Param.output" => Param.Output(tpe, paramName)
            case _                   => Param.Scalar(tpe, paramName)
          }
        case "Cuda.Param.tensorMap" =>
          expectArity(fields, 2, path)
          Param.TensorMap(decodeMapUse(fields(0), s"$path.use"), str(fields(1), s"$path.name"))
        case _ => malformed(path, s"unknown Cuda.Param $name")
      }
    }

    private def decodeMapUse(value: Value, path: String): MapUse = {
      val (name, fields) = constructor(value, path)
      expectArity(fields, 0, path)
      name match {
        case "Cuda.MapUse.load"  => MapUse.Load
        case "Cuda.MapUse.store" => MapUse.Store
        case _                   => malformed(path, s"unknown Cuda.MapUse $name")
      }
    }

    private def decodeMap(value: Value, path: String): MapEncoding = {
      val (name, fields) = constructor(value, path)
      expectName(name, "Cuda.MapEncoding.mk", path)
      expectArity(fields, 7, path)
      MapEncoding(
        str(fields(0), s"$path.param"),
        decodeMapUse(fields(1), s"$path.use"),
        decodeParam(fields(2), s"$path.source"),
        str(fields(3), s"$path.rows"),
        str(fields(4), s"$path.cols"),
        nat(fields(5), s"$path.inner"),
        nat(fields(6), s"$path.outer")
      )
    }

    private def decodeEnum[A](value: Value, path: String, cases: Map[String, A]): A = {
      val (name, fields) = constructor(value, path)
      expectArity(fields, 0, path)
      cases.getOrElse(name, malformed(path, s"unknown constructor $name"))
    }

    private def decodeBuiltin(value: Value, path: String): Builtin = decodeEnum(
      value,
      path,
      Map(
        "Cuda.Builtin.threadX" -> Builtin.ThreadX,
        "Cuda.Builtin.blockX" -> Builtin.BlockX,
        "Cuda.Builtin.blockY" -> Builtin.BlockY,
        "Cuda.Builtin.gridX" -> Builtin.GridX,
        "Cuda.Builtin.warp" -> Builtin.Warp,
        "Cuda.Builtin.lane" -> Builtin.Lane
      )
    )

    private def decodeBinOp(value: Value, path: String): BinOp = decodeEnum(
      value,
      path,
      Map(
        "Cuda.BinOp.add" -> BinOp.Add,
        "Cuda.BinOp.sub" -> BinOp.Sub,
        "Cuda.BinOp.mul" -> BinOp.Mul,
        "Cuda.BinOp.div" -> BinOp.Div,
        "Cuda.BinOp.rem" -> BinOp.Rem,
        "Cuda.BinOp.lt" -> BinOp.Lt,
        "Cuda.BinOp.eq" -> BinOp.Eq,
        "Cuda.BinOp.land" -> BinOp.Land,
        "Cuda.BinOp.shl" -> BinOp.Shl,
        "Cuda.BinOp.shr" -> BinOp.Shr,
        "Cuda.BinOp.bor" -> BinOp.Bor,
        "Cuda.BinOp.band" -> BinOp.Band,
        "Cuda.BinOp.bxor" -> BinOp.Bxor
      )
    )

    private def decodeExpr(value: Value, path: String): Expr = {
      val (name, fields) = constructor(value, path)
      name match {
        case "Cuda.Expr.var"   => expectArity(fields, 1, path); Expr.Var(nat(fields.head, s"$path.id"))
        case "Cuda.Expr.lit"   => expectArity(fields, 1, path); Expr.Lit(nat(fields.head, s"$path.value"))
        case "Cuda.Expr.lit64" => expectArity(fields, 1, path); Expr.Lit64(nat(fields.head, s"$path.value"))
        case "Cuda.Expr.zero"  => expectArity(fields, 1, path); Expr.Zero(decodeDType(fields.head, s"$path.dtype"))
        case "Cuda.Expr.param" => expectArity(fields, 1, path); Expr.Param(str(fields.head, s"$path.name"))
        case "Cuda.Expr.special" =>
          expectArity(fields, 1, path); Expr.Special(decodeBuiltin(fields.head, s"$path.builtin"))
        case "Cuda.Expr.bin" =>
          expectArity(fields, 3, path);
          Expr.Bin(
            decodeBinOp(fields(0), s"$path.op"),
            decodeExpr(fields(1), s"$path.left"),
            decodeExpr(fields(2), s"$path.right")
          )
        case "Cuda.Expr.max" =>
          expectArity(fields, 2, path);
          Expr.Max(decodeExpr(fields(0), s"$path.left"), decodeExpr(fields(1), s"$path.right"))
        case "Cuda.Expr.fma" =>
          expectArity(fields, 3, path);
          Expr.Fma(
            decodeExpr(fields(0), s"$path.a"),
            decodeExpr(fields(1), s"$path.b"),
            decodeExpr(fields(2), s"$path.c")
          )
        case "Cuda.Expr.select" =>
          expectArity(fields, 3, path);
          Expr.Select(
            decodeExpr(fields(0), s"$path.condition"),
            decodeExpr(fields(1), s"$path.yes"),
            decodeExpr(fields(2), s"$path.no")
          )
        case "Cuda.Expr.index" =>
          expectArity(fields, 2, path);
          Expr.Index(decodeExpr(fields(0), s"$path.base"), decodeExpr(fields(1), s"$path.index"))
        case "Cuda.Expr.cast" =>
          expectArity(fields, 2, path);
          Expr.Cast(decodeDType(fields(0), s"$path.dtype"), decodeExpr(fields(1), s"$path.value"))
        case "Cuda.Expr.sharedAddr" => expectArity(fields, 1, path); Expr.SharedAddr(nat(fields.head, s"$path.offset"))
        case "Cuda.Expr.sharedPtr" =>
          expectArity(fields, 2, path);
          Expr.SharedPtr(decodeDType(fields(0), s"$path.dtype"), nat(fields(1), s"$path.offset"))
        case "Cuda.Expr.paramAddr" => expectArity(fields, 1, path); Expr.ParamAddr(str(fields.head, s"$path.name"))
        case _                     => malformed(path, s"unknown Cuda.Expr $name")
      }
    }

    private def decodeGrid(value: Value, path: String): Grid = {
      val (name, fields) = constructor(value, path)
      name match {
        case "Cuda.Grid.blocks" =>
          expectArity(fields, 2, path);
          Grid.Blocks(decodeExpr(fields(0), s"$path.x"), decodeExpr(fields(1), s"$path.y"))
        case "Cuda.Grid.pairs" =>
          expectArity(fields, 2, path); Grid.Pairs(decodeExpr(fields(0), s"$path.x"), decodeExpr(fields(1), s"$path.y"))
        case "Cuda.Grid.persistentPairs" =>
          expectArity(fields, 1, path); Grid.PersistentPairs(decodeExpr(fields.head, s"$path.tiles"))
        case _ => malformed(path, s"unknown Cuda.Grid $name")
      }
    }

    private def decodeBlock(value: Value, path: String): Block = {
      val statements = Vector.newBuilder[Stmt]
      var current = value
      var index = 0
      var done = false
      while (!done) {
        val (name, fields) = constructor(current, s"$path[$index]")
        name match {
          case "Cuda.Block.done" => expectArity(fields, 0, s"$path[$index]"); done = true
          case "Cuda.Block.seq" =>
            expectArity(fields, 2, s"$path[$index]")
            statements += decodeStmt(fields(0), s"$path[$index].statement")
            current = fields(1)
            index += 1
          case _ => malformed(s"$path[$index]", s"expected Cuda.Block.done/seq, got $name")
        }
      }
      Block(statements.result())
    }

    private def decodeStmt(value: Value, path: String): Stmt = {
      val (name, fields) = constructor(value, path)
      name match {
        case "Cuda.Stmt.decl" | "Cuda.Stmt.declMut" =>
          expectArity(fields, 3, path)
          Stmt.Decl(
            decodeDType(fields(0), s"$path.dtype"),
            nat(fields(1), s"$path.id"),
            decodeExpr(fields(2), s"$path.init"),
            name.endsWith("declMut")
          )
        case "Cuda.Stmt.declOut" =>
          expectArity(fields, 2, path);
          Stmt.DeclOut(decodeDType(fields(0), s"$path.dtype"), nat(fields(1), s"$path.id"))
        case "Cuda.Stmt.assign" =>
          expectArity(fields, 2, path); Stmt.Assign(nat(fields(0), s"$path.id"), decodeExpr(fields(1), s"$path.value"))
        case "Cuda.Stmt.store" =>
          expectArity(fields, 3, path);
          Stmt.Store(
            decodeExpr(fields(0), s"$path.base"),
            decodeExpr(fields(1), s"$path.index"),
            decodeExpr(fields(2), s"$path.value")
          )
        case "Cuda.Stmt.shared" =>
          expectArity(fields, 3, path);
          Stmt.Shared(
            decodeDType(fields(0), s"$path.dtype"),
            nat(fields(1), s"$path.id"),
            nat(fields(2), s"$path.size")
          )
        case "Cuda.Stmt.forLoop" =>
          expectArity(fields, 4, path);
          Stmt.ForLoop(
            nat(fields(0), s"$path.id"),
            decodeExpr(fields(1), s"$path.start"),
            decodeExpr(fields(2), s"$path.stop"),
            decodeBlock(fields(3), s"$path.body")
          )
        case "Cuda.Stmt.forStride" =>
          expectArity(fields, 5, path);
          Stmt.ForStride(
            nat(fields(0), s"$path.id"),
            decodeExpr(fields(1), s"$path.start"),
            decodeExpr(fields(2), s"$path.stop"),
            decodeExpr(fields(3), s"$path.step"),
            decodeBlock(fields(4), s"$path.body")
          )
        case "Cuda.Stmt.ifElse" =>
          expectArity(fields, 3, path);
          Stmt.IfElse(
            decodeExpr(fields(0), s"$path.condition"),
            decodeBlock(fields(1), s"$path.yes"),
            decodeBlock(fields(2), s"$path.no")
          )
        case "Cuda.Stmt.scoped"   => expectArity(fields, 1, path); Stmt.Scoped(decodeBlock(fields.head, s"$path.body"))
        case "Cuda.Stmt.sync"     => expectArity(fields, 0, path); Stmt.Sync
        case "Cuda.Stmt.syncWarp" => expectArity(fields, 0, path); Stmt.SyncWarp
        case "Cuda.Stmt.instr" =>
          expectArity(fields, 1, path); Stmt.Instruction(decodeInstr(fields.head, s"$path.instr"))
        case "Cuda.Stmt.error" => expectArity(fields, 1, path); Stmt.Error(str(fields.head, s"$path.message"))
        case _                 => malformed(path, s"unknown Cuda.Stmt $name")
      }
    }

    // The decoder for instruction payloads follows below; each constructor is represented even when execution rejects it.
    private def decodeInstr(value: Value, path: String): Instr = decodeInstruction(value, path)

    private def decodeInstruction(value: Value, path: String): Instr = {
      val (name, fields) = constructor(value, path)
      name match {
        case "Cuda.Instr.barSync" =>
          expectArity(fields, 2, path);
          Instr.BarSync(decodeExpr(fields(0), s"$path.id"), decodeExpr(fields(1), s"$path.threads"))
        case "Cuda.Instr.mbarInit" =>
          expectArity(fields, 2, path);
          Instr.MbarInit(decodeExpr(fields(0), s"$path.bar"), decodeExpr(fields(1), s"$path.count"))
        case "Cuda.Instr.mbarInval" =>
          expectArity(fields, 1, path); Instr.MbarInval(decodeExpr(fields.head, s"$path.bar"))
        case "Cuda.Instr.mbarArrive" =>
          expectArity(fields, 3, path);
          Instr.MbarArrive(
            decodeEnum(
              fields(0),
              s"$path.window",
              Map("Cuda.Window.cta" -> Window.Cta, "Cuda.Window.cluster" -> Window.Cluster)
            ),
            decodeExpr(fields(1), s"$path.bar"),
            decodeArrival(fields(2), s"$path.arrival")
          )
        case "Cuda.Instr.mbarWait" =>
          expectArity(fields, 3, path);
          Instr.MbarWait(
            decodeEnum(
              fields(0),
              s"$path.scope",
              Map("Cuda.BarrierScope.cta" -> BarrierScope.Cta, "Cuda.BarrierScope.cluster" -> BarrierScope.Cluster)
            ),
            decodeExpr(fields(1), s"$path.bar"),
            decodeExpr(fields(2), s"$path.parity")
          )
        case "Cuda.Instr.fenceMbarInit"   => expectArity(fields, 0, path); Instr.FenceMbarInit
        case "Cuda.Instr.fenceProxyAsync" => expectArity(fields, 0, path); Instr.FenceProxyAsync
        case "Cuda.Instr.tcFence" =>
          expectArity(fields, 1, path);
          Instr.TcFence(
            decodeEnum(
              fields.head,
              s"$path.side",
              Map("Cuda.ThreadSync.before" -> ThreadSync.Before, "Cuda.ThreadSync.after" -> ThreadSync.After)
            )
          )
        case "Cuda.Instr.clusterArrive" => expectArity(fields, 0, path); Instr.ClusterArrive
        case "Cuda.Instr.clusterWait"   => expectArity(fields, 0, path); Instr.ClusterWait
        case "Cuda.Instr.tmaLoad" =>
          expectArity(fields, 6, path);
          Instr.TmaLoad(
            decodeGroup(fields(0), s"$path.group"),
            decodeExpr(fields(1), s"$path.dst"),
            decodeExpr(fields(2), s"$path.map"),
            decodeExpr(fields(3), s"$path.x"),
            decodeExpr(fields(4), s"$path.y"),
            decodeExpr(fields(5), s"$path.bar")
          )
        case "Cuda.Instr.tmaStore" =>
          expectArity(fields, 4, path);
          Instr.TmaStore(
            decodeExpr(fields(0), s"$path.map"),
            decodeExpr(fields(1), s"$path.x"),
            decodeExpr(fields(2), s"$path.y"),
            decodeExpr(fields(3), s"$path.src")
          )
        case "Cuda.Instr.bulkCommit" => expectArity(fields, 0, path); Instr.BulkCommit
        case "Cuda.Instr.bulkWait" =>
          expectArity(fields, 2, path);
          Instr.BulkWait(
            decodeEnum(
              fields(0),
              s"$path.what",
              Map("Cuda.BulkWait.read" -> BulkWaitKind.Read, "Cuda.BulkWait.complete" -> BulkWaitKind.Complete)
            ),
            nat(fields(1), s"$path.pending")
          )
        case "Cuda.Instr.tmemAlloc" =>
          expectArity(fields, 3, path);
          Instr.TmemAlloc(
            decodeGroup(fields(0), s"$path.group"),
            decodeExpr(fields(1), s"$path.slot"),
            decodeExpr(fields(2), s"$path.cols")
          )
        case "Cuda.Instr.tmemRelinquish" =>
          expectArity(fields, 1, path); Instr.TmemRelinquish(decodeGroup(fields.head, s"$path.group"))
        case "Cuda.Instr.tmemDealloc" =>
          expectArity(fields, 3, path);
          Instr.TmemDealloc(
            decodeGroup(fields(0), s"$path.group"),
            decodeExpr(fields(1), s"$path.address"),
            decodeExpr(fields(2), s"$path.cols")
          )
        case "Cuda.Instr.mma" =>
          expectArity(fields, 6, path);
          Instr.Mma(
            decodeGroup(fields(0), s"$path.group"),
            decodeExpr(fields(1), s"$path.acc"),
            decodeMmaA(fields(2), s"$path.a"),
            decodeSmemDesc(fields(3), s"$path.b"),
            decodeInstrDesc(fields(4), s"$path.descriptor"),
            decodeExpr(fields(5), s"$path.accumulate")
          )
        case "Cuda.Instr.tcCommit" =>
          expectArity(fields, 3, path);
          Instr.TcCommit(
            decodeGroup(fields(0), s"$path.group"),
            decodeExpr(fields(1), s"$path.bar"),
            optional(fields(2), s"$path.multicast")((v, p) => nat(v, p))
          )
        case "Cuda.Instr.tmemLoad" =>
          expectArity(fields, 3, path);
          Instr.TmemLoad(
            decodeEnum(fields(0), s"$path.shape", Map("Cuda.TmemShape.s32x32b" -> TmemShape.S32x32b)),
            list(fields(1), s"$path.destinations")((v, p) => nat(v, p)),
            decodeExpr(fields(2), s"$path.address")
          )
        case "Cuda.Instr.tmemStore" =>
          expectArity(fields, 4, path);
          Instr.TmemStore(
            decodeEnum(fields(0), s"$path.shape", Map("Cuda.TmemShape.s32x32b" -> TmemShape.S32x32b)),
            decodeEnum(fields(1), s"$path.word", Map("Cuda.Word.u32" -> Word.U32, "Cuda.Word.f32" -> Word.F32)),
            decodeExpr(fields(2), s"$path.address"),
            list(fields(3), s"$path.values")(decodeExpr)
          )
        case "Cuda.Instr.tmemWait" =>
          expectArity(fields, 1, path);
          Instr.TmemWait(
            decodeEnum(
              fields.head,
              s"$path.what",
              Map("Cuda.TmemWait.load" -> TmemWaitKind.Load, "Cuda.TmemWait.store" -> TmemWaitKind.Store)
            )
          )
        case "Cuda.Instr.elect" => expectArity(fields, 1, path); Instr.Elect(nat(fields.head, s"$path.flag"))
        case "Cuda.Instr.shfl" =>
          expectArity(fields, 3, path);
          Instr.Shfl(nat(fields(0), s"$path.d"), decodeExpr(fields(1), s"$path.value"), nat(fields(2), s"$path.lane"))
        case "Cuda.Instr.voteAny" =>
          expectArity(fields, 2, path);
          Instr.VoteAny(nat(fields(0), s"$path.d"), decodeExpr(fields(1), s"$path.predicate"))
        case "Cuda.Instr.setMaxNReg" =>
          expectArity(fields, 2, path);
          Instr.SetMaxNReg(
            decodeEnum(
              fields(0),
              s"$path.change",
              Map("Cuda.RegChange.inc" -> RegChange.Inc, "Cuda.RegChange.dec" -> RegChange.Dec)
            ),
            nat(fields(1), s"$path.count")
          )
        case "Cuda.Instr.movF32" =>
          expectArity(fields, 2, path); Instr.MovF32(nat(fields(0), s"$path.d"), nat(fields(1), s"$path.bits"))
        case "Cuda.Instr.ex2" =>
          expectArity(fields, 2, path); Instr.Ex2(nat(fields(0), s"$path.d"), decodeExpr(fields(1), s"$path.value"))
        case "Cuda.Instr.lg2" =>
          expectArity(fields, 2, path); Instr.Lg2(nat(fields(0), s"$path.d"), decodeExpr(fields(1), s"$path.value"))
        case "Cuda.Instr.ex2Emulated" =>
          expectArity(fields, 2, path);
          Instr.Ex2Emulated(nat(fields(0), s"$path.d"), decodeExpr(fields(1), s"$path.value"))
        case "Cuda.Instr.rcp" =>
          expectArity(fields, 3, path);
          Instr.Rcp(
            decodeEnum(
              fields(0),
              s"$path.rounding",
              Map(
                "Cuda.Rounding.rn" -> Rounding.Rn,
                "Cuda.Rounding.rz" -> Rounding.Rz,
                "Cuda.Rounding.rm" -> Rounding.Rm,
                "Cuda.Rounding.rp" -> Rounding.Rp
              )
            ),
            nat(fields(1), s"$path.d"),
            decodeExpr(fields(2), s"$path.value")
          )
        case "Cuda.Instr.cvtBf16x2" =>
          expectArity(fields, 3, path);
          Instr.CvtBf16x2(
            nat(fields(0), s"$path.d"),
            decodeExpr(fields(1), s"$path.high"),
            decodeExpr(fields(2), s"$path.low")
          )
        case "Cuda.Instr.ldRelaxed" =>
          expectArity(fields, 3, path);
          Instr.LdRelaxed(
            decodeScope(fields(0), s"$path.scope"),
            nat(fields(1), s"$path.d"),
            decodeExpr(fields(2), s"$path.address")
          )
        case "Cuda.Instr.casRelaxed" =>
          expectArity(fields, 5, path);
          Instr.CasRelaxed(
            decodeScope(fields(0), s"$path.scope"),
            nat(fields(1), s"$path.d"),
            decodeExpr(fields(2), s"$path.address"),
            decodeExpr(fields(3), s"$path.expected"),
            decodeExpr(fields(4), s"$path.desired")
          )
        case "Cuda.Instr.movSpecial" =>
          expectArity(fields, 2, path);
          Instr.MovSpecial(
            nat(fields(0), s"$path.d"),
            decodeEnum(
              fields(1),
              s"$path.reg",
              Map(
                "Cuda.SpecialReg.clusterCtaRank" -> SpecialReg.ClusterCtaRank,
                "Cuda.SpecialReg.clusterIdX" -> SpecialReg.ClusterIdX,
                "Cuda.SpecialReg.nclusterIdX" -> SpecialReg.NClusterIdX
              )
            )
          )
        case "Cuda.Instr.mapa" =>
          expectArity(fields, 3, path);
          Instr.Mapa(
            nat(fields(0), s"$path.d"),
            decodeExpr(fields(1), s"$path.address"),
            decodeExpr(fields(2), s"$path.rank")
          )
        case "Cuda.Instr.stShared" =>
          expectArity(fields, 2, path);
          Instr.StShared(decodeExpr(fields(0), s"$path.address"), list(fields(1), s"$path.values")(decodeExpr))
        case _ => malformed(path, s"unknown Cuda.Instr $name")
      }
    }

    private def decodeGroup(value: Value, path: String): Group = decodeEnum(
      value,
      path,
      Map(
        "Cuda.CtaGroup.one" -> Group.One,
        "Cuda.CtaGroup.two" -> Group.Two
      )
    )

    private def decodeArrival(value: Value, path: String): Arrival = {
      val (name, fields) = constructor(value, path)
      name match {
        case "Cuda.Arrival.one" => expectArity(fields, 0, path); Arrival.One
        case "Cuda.Arrival.count" =>
          expectArity(fields, 1, path); Arrival.Count(decodeExpr(fields.head, s"$path.count"))
        case "Cuda.Arrival.expectTx" =>
          expectArity(fields, 1, path); Arrival.ExpectTx(decodeExpr(fields.head, s"$path.bytes"))
        case _ => malformed(path, s"unknown Cuda.Arrival $name")
      }
    }

    private def decodeScope(value: Value, path: String): Scope = decodeEnum(
      value,
      path,
      Map(
        "Cuda.Scope.cta" -> Scope.Cta,
        "Cuda.Scope.cluster" -> Scope.Cluster,
        "Cuda.Scope.gpu" -> Scope.Gpu
      )
    )

    private def decodeSmemDesc(value: Value, path: String): SmemDesc = {
      val (name, fields) = constructor(value, path)
      expectName(name, "Cuda.SmemDesc.mk", path)
      expectArity(fields, 3, path)
      SmemDesc(decodeExpr(fields(0), s"$path.base"), nat(fields(1), s"$path.lbo"), nat(fields(2), s"$path.step"))
    }

    private def decodeInstrDesc(value: Value, path: String): InstrDesc = {
      val (name, fields) = constructor(value, path)
      expectName(name, "Cuda.InstrDesc.mk", path)
      expectArity(fields, 3, path)
      InstrDesc(nat(fields(0), s"$path.m"), nat(fields(1), s"$path.n"), bool(fields(2), s"$path.transposeB"))
    }

    private def decodeMmaA(value: Value, path: String): MmaA = {
      val (name, fields) = constructor(value, path)
      name match {
        case "Cuda.MmaA.smem" => expectArity(fields, 1, path); MmaA.Smem(decodeSmemDesc(fields.head, s"$path.desc"))
        case "Cuda.MmaA.tmem" => expectArity(fields, 1, path); MmaA.Tmem(decodeExpr(fields.head, s"$path.address"))
        case _                => malformed(path, s"unknown Cuda.MmaA $name")
      }
    }
  }
}
