package com.raccoonlang.translator

import java.nio.file.Path
import scala.collection.mutable

object LeanExportIr {
  final case class NameId(value: Int) extends AnyVal
  final case class LevelId(value: Int) extends AnyVal
  final case class ExprId(value: Int) extends AnyVal

  sealed trait NameNode
  final case class NameStr(prefix: NameId, value: String) extends NameNode
  final case class NameNum(prefix: NameId, value: BigInt) extends NameNode

  sealed trait LevelNode
  case object LevelZero extends LevelNode
  final case class LevelSucc(of: LevelId) extends LevelNode
  final case class LevelMax(left: LevelId, right: LevelId) extends LevelNode
  final case class LevelIMax(left: LevelId, right: LevelId) extends LevelNode
  final case class LevelParam(name: NameId) extends LevelNode

  sealed trait BinderInfo
  case object Default extends BinderInfo
  case object Implicit extends BinderInfo
  case object StrictImplicit extends BinderInfo
  case object InstImplicit extends BinderInfo

  sealed trait ExprNode
  final case class BVar(index: Int) extends ExprNode
  final case class Sort(level: LevelId) extends ExprNode
  final case class Const(name: NameId, levels: Vector[LevelId]) extends ExprNode
  final case class App(fn: ExprId, arg: ExprId) extends ExprNode
  final case class Lam(name: NameId, binderType: ExprId, body: ExprId, binderInfo: BinderInfo) extends ExprNode
  final case class ForallE(name: NameId, binderType: ExprId, body: ExprId, binderInfo: BinderInfo) extends ExprNode
  final case class LetE(
      name: NameId,
      binderType: ExprId,
      value: ExprId,
      body: ExprId,
      nonDependent: Boolean
  ) extends ExprNode
  final case class Proj(typeName: NameId, fieldIndex: Int, struct: ExprId) extends ExprNode
  final case class NatVal(value: BigInt) extends ExprNode
  final case class StrVal(scalars: Vector[Int]) extends ExprNode
  final case class MData(expr: ExprId) extends ExprNode

  final case class ExportMeta(
      exporterName: String,
      exporterVersion: String,
      leanVersion: String,
      leanGitHash: String,
      formatVersion: String
  )

  final case class ExportProvenance(
      source: Path,
      line: Long,
      column: Int,
      objectOrdinal: Long,
      kind: String,
      internId: Option[Int],
      declaration: Option[String]
  )

  sealed trait ExportDecl { def provenance: ExportProvenance }
  final case class ExportAxiom(
      name: NameId,
      levelParams: Vector[NameId],
      tpe: ExprId,
      isUnsafe: Boolean,
      provenance: ExportProvenance
  ) extends ExportDecl

  sealed trait ExportDefHint
  case object HintOpaque extends ExportDefHint
  case object HintAbbrev extends ExportDefHint
  final case class HintRegular(height: BigInt) extends ExportDefHint

  sealed trait ExportSafety
  case object Safe extends ExportSafety
  case object Unsafe extends ExportSafety
  case object Partial extends ExportSafety

  final case class ExportDef(
      name: NameId,
      levelParams: Vector[NameId],
      tpe: ExprId,
      value: ExprId,
      hint: ExportDefHint,
      safety: ExportSafety,
      all: Vector[NameId],
      provenance: ExportProvenance
  ) extends ExportDecl

  final case class ExportOpaque(
      name: NameId,
      levelParams: Vector[NameId],
      tpe: ExprId,
      value: ExprId,
      isUnsafe: Boolean,
      all: Vector[NameId],
      provenance: ExportProvenance
  ) extends ExportDecl

  final case class ExportTheorem(
      name: NameId,
      levelParams: Vector[NameId],
      tpe: ExprId,
      value: ExprId,
      all: Vector[NameId],
      provenance: ExportProvenance
  ) extends ExportDecl

  sealed trait ExportQuotKind
  case object QuotType extends ExportQuotKind
  case object QuotCtor extends ExportQuotKind
  case object QuotLift extends ExportQuotKind
  case object QuotInd extends ExportQuotKind

  final case class ExportQuot(
      name: NameId,
      levelParams: Vector[NameId],
      tpe: ExprId,
      kind: ExportQuotKind,
      provenance: ExportProvenance
  ) extends ExportDecl

  final case class ExportInductiveValue(
      name: NameId,
      levelParams: Vector[NameId],
      tpe: ExprId,
      numParams: Int,
      numIndices: Int,
      all: Vector[NameId],
      ctors: Vector[NameId],
      numNested: Int,
      isRec: Boolean,
      isUnsafe: Boolean,
      isReflexive: Boolean
  )

  final case class ExportConstructorValue(
      name: NameId,
      levelParams: Vector[NameId],
      tpe: ExprId,
      inductive: NameId,
      constructorIndex: Int,
      numParams: Int,
      numFields: Int,
      isUnsafe: Boolean
  )

  final case class ExportRecursorRule(constructor: NameId, numFields: Int, rhs: ExprId)

  final case class ExportRecursorValue(
      name: NameId,
      levelParams: Vector[NameId],
      tpe: ExprId,
      all: Vector[NameId],
      numParams: Int,
      numIndices: Int,
      numMotives: Int,
      numMinors: Int,
      rules: Vector[ExportRecursorRule],
      supportsK: Boolean,
      isUnsafe: Boolean
  )

  final case class ExportInductive(
      types: Vector[ExportInductiveValue],
      constructors: Vector[ExportConstructorValue],
      recursors: Vector[ExportRecursorValue],
      provenance: ExportProvenance
  ) extends ExportDecl

  trait LeanExportConsumer {
    def onMeta(meta: ExportMeta): Unit
    def onDeclaration(decl: ExportDecl, tables: ExportTables): Unit
    def finish(tables: ExportTables): Unit
  }

  object LeanExportConsumer {
    val ignore: LeanExportConsumer = new LeanExportConsumer {
      override def onMeta(meta: ExportMeta): Unit = ()
      override def onDeclaration(decl: ExportDecl, tables: ExportTables): Unit = ()
      override def finish(tables: ExportTables): Unit = ()
    }
  }

  /**
   * Compact append-only intern tables. Fixed-width node fields live in primitive arrays; only genuinely variable
   * payloads (strings, argument slices, big integers) allocate objects. Cursor methods materialize semantic nodes on
   * demand, so a full export does not retain a recursive Scala object graph.
   */
  final class ExportTables private[translator] (val source: Path) {
    private val nameTags = mutable.ArrayBuffer[Byte](0)
    private val namePrefix = mutable.ArrayBuffer[Int](0)
    private val namePayload = mutable.ArrayBuffer[AnyRef]("")
    private val nameLine = mutable.ArrayBuffer[Long](0L)
    private val nameColumn = mutable.ArrayBuffer[Int](0)
    private val nameOrdinal = mutable.ArrayBuffer[Long](0L)

    private val levelTags = mutable.ArrayBuffer[Byte](0)
    private val levelLeft = mutable.ArrayBuffer[Int](0)
    private val levelRight = mutable.ArrayBuffer[Int](0)
    private val levelLine = mutable.ArrayBuffer[Long](0L)
    private val levelColumn = mutable.ArrayBuffer[Int](0)
    private val levelOrdinal = mutable.ArrayBuffer[Long](0L)

    private val exprTags = mutable.ArrayBuffer.empty[Byte]
    private val exprA = mutable.ArrayBuffer.empty[Int]
    private val exprB = mutable.ArrayBuffer.empty[Int]
    private val exprC = mutable.ArrayBuffer.empty[Int]
    private val exprPayload = mutable.ArrayBuffer.empty[AnyRef]
    private val exprLine = mutable.ArrayBuffer.empty[Long]
    private val exprColumn = mutable.ArrayBuffer.empty[Int]
    private val exprOrdinal = mutable.ArrayBuffer.empty[Long]

    private var payloadBytes = 0L

    private var bytesHighWater0 = estimatedBytes

    def nameCount: Int = nameTags.length
    def levelCount: Int = levelTags.length
    def expressionCount: Int = exprTags.length
    def currentBytes: Long = estimatedBytes
    def highWaterBytes: Long = bytesHighWater0

    def nameProvenance(id: NameId): ExportProvenance = {
      requireName(id)
      internProvenance("name", id.value, nameLine(id.value), nameColumn(id.value), nameOrdinal(id.value))
    }
    def levelProvenance(id: LevelId): ExportProvenance = {
      requireLevel(id)
      internProvenance("level", id.value, levelLine(id.value), levelColumn(id.value), levelOrdinal(id.value))
    }
    def exprProvenance(id: ExprId): ExportProvenance = {
      requireExpr(id)
      internProvenance("expression", id.value, exprLine(id.value), exprColumn(id.value), exprOrdinal(id.value))
    }

    def nameNode(id: NameId): NameNode = {
      requireName(id)
      nameTags(id.value) match {
        case 1 => NameStr(NameId(namePrefix(id.value)), namePayload(id.value).asInstanceOf[String])
        case 2 => NameNum(NameId(namePrefix(id.value)), namePayload(id.value).asInstanceOf[BigInt])
        case _ => throw new IllegalArgumentException("anonymous name has no NameNode")
      }
    }

    def nameComponents(id: NameId): Vector[Either[String, BigInt]] = {
      requireName(id)
      val reversed = Vector.newBuilder[Either[String, BigInt]]
      var cur = id.value
      while (cur != 0) {
        nameTags(cur) match {
          case 1 => reversed += Left(namePayload(cur).asInstanceOf[String])
          case 2 => reversed += Right(namePayload(cur).asInstanceOf[BigInt])
          case _ => throw new IllegalStateException(s"invalid name tag at $cur")
        }
        cur = namePrefix(cur)
      }
      reversed.result().reverse
    }

    def dottedName(id: NameId): String =
      nameComponents(id).map(_.fold(identity, _.toString)).mkString(".")

    def levelNode(id: LevelId): LevelNode = {
      requireLevel(id)
      levelTags(id.value) match {
        case 0   => LevelZero
        case 1   => LevelSucc(LevelId(levelLeft(id.value)))
        case 2   => LevelMax(LevelId(levelLeft(id.value)), LevelId(levelRight(id.value)))
        case 3   => LevelIMax(LevelId(levelLeft(id.value)), LevelId(levelRight(id.value)))
        case 4   => LevelParam(NameId(levelLeft(id.value)))
        case tag => throw new IllegalStateException(s"invalid level tag $tag")
      }
    }

    def exprNode(id: ExprId): ExprNode = {
      requireExpr(id)
      val i = id.value
      exprTags(i) match {
        case 0 => BVar(exprA(i))
        case 1 => Sort(LevelId(exprA(i)))
        case 2 => Const(NameId(exprA(i)), exprPayload(i).asInstanceOf[Vector[LevelId]])
        case 3 => App(ExprId(exprA(i)), ExprId(exprB(i)))
        case 4 => Lam(NameId(exprA(i)), ExprId(exprB(i)), ExprId(exprC(i)), exprPayload(i).asInstanceOf[BinderInfo])
        case 5 => ForallE(NameId(exprA(i)), ExprId(exprB(i)), ExprId(exprC(i)), exprPayload(i).asInstanceOf[BinderInfo])
        case 6 =>
          val pair = exprPayload(i).asInstanceOf[(Int, Boolean)]
          LetE(NameId(exprA(i)), ExprId(exprB(i)), ExprId(exprC(i)), ExprId(pair._1), pair._2)
        case 7   => Proj(NameId(exprA(i)), exprB(i), ExprId(exprC(i)))
        case 8   => NatVal(exprPayload(i).asInstanceOf[BigInt])
        case 9   => StrVal(exprPayload(i).asInstanceOf[Vector[Int]])
        case 10  => MData(ExprId(exprA(i)))
        case tag => throw new IllegalStateException(s"invalid expression tag $tag")
      }
    }

    private[translator] def appendName(node: NameNode, at: ExportProvenance): NameId = {
      val id = NameId(nameTags.length)
      node match {
        case NameStr(prefix, value) =>
          nameTags += 1; namePrefix += prefix.value; namePayload += value; payloadBytes += value.length.toLong * 2L
        case NameNum(prefix, value) =>
          nameTags += 2; namePrefix += prefix.value; namePayload += value; payloadBytes += value.toByteArray.length
      }
      nameLine += at.line; nameColumn += at.column; nameOrdinal += at.objectOrdinal
      updateHighWater()
      id
    }

    private[translator] def appendLevel(node: LevelNode, at: ExportProvenance): LevelId = {
      val id = LevelId(levelTags.length)
      node match {
        case LevelSucc(of)          => levelTags += 1; levelLeft += of.value; levelRight += 0
        case LevelMax(left, right)  => levelTags += 2; levelLeft += left.value; levelRight += right.value
        case LevelIMax(left, right) => levelTags += 3; levelLeft += left.value; levelRight += right.value
        case LevelParam(name)       => levelTags += 4; levelLeft += name.value; levelRight += 0
        case LevelZero              => throw new IllegalArgumentException("level zero is pre-seeded")
      }
      levelLine += at.line; levelColumn += at.column; levelOrdinal += at.objectOrdinal
      updateHighWater()
      id
    }

    private[translator] def appendExpr(node: ExprNode, at: ExportProvenance): ExprId = {
      val id = ExprId(exprTags.length)
      var tag: Byte = 0
      var a = 0
      var b = 0
      var c = 0
      var payload: AnyRef = null
      node match {
        case BVar(index)         => tag = 0; a = index
        case Sort(level)         => tag = 1; a = level.value
        case Const(name, levels) => tag = 2; a = name.value; payload = levels; payloadBytes += levels.length.toLong * 4L
        case App(fn, arg)        => tag = 3; a = fn.value; b = arg.value
        case Lam(name, ty, body, info)     => tag = 4; a = name.value; b = ty.value; c = body.value; payload = info
        case ForallE(name, ty, body, info) => tag = 5; a = name.value; b = ty.value; c = body.value; payload = info
        case LetE(name, ty, value, body, nonDep) =>
          tag = 6; a = name.value; b = ty.value; c = value.value; payload = (body.value, nonDep)
        case Proj(typeName, index, struct) => tag = 7; a = typeName.value; b = index; c = struct.value
        case NatVal(value)                 => tag = 8; payload = value; payloadBytes += value.toByteArray.length
        case StrVal(scalars)               => tag = 9; payload = scalars; payloadBytes += scalars.length.toLong * 4L
        case MData(expr)                   => tag = 10; a = expr.value
      }
      exprTags += tag; exprA += a; exprB += b; exprC += c; exprPayload += payload
      exprLine += at.line; exprColumn += at.column; exprOrdinal += at.objectOrdinal
      updateHighWater()
      id
    }

    private def requireName(id: NameId): Unit =
      require(id.value >= 0 && id.value < nameCount, s"name ${id.value} is out of range")
    private def requireLevel(id: LevelId): Unit =
      require(id.value >= 0 && id.value < levelCount, s"level ${id.value} is out of range")
    private def requireExpr(id: ExprId): Unit =
      require(id.value >= 0 && id.value < expressionCount, s"expression ${id.value} is out of range")

    private def internProvenance(kind: String, id: Int, line: Long, column: Int, ordinal: Long): ExportProvenance =
      ExportProvenance(source, line, column, ordinal, kind, Some(id), None)

    private def estimatedBytes: Long =
      nameTags.length.toLong * 33L + levelTags.length.toLong * 29L + exprTags.length.toLong * 41L + payloadBytes
    private def updateHighWater(): Unit = bytesHighWater0 = math.max(bytesHighWater0, estimatedBytes)
  }
}
