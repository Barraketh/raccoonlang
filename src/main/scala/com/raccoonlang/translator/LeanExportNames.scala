package com.raccoonlang.translator

import com.raccoonlang.IdentifierSyntax
import com.raccoonlang.translator.LeanExportIr._

import java.nio.charset.StandardCharsets

object LeanExportNames {
  private val EncodedPrefix = "$lean.name"

  def encode(id: NameId, tables: ExportTables): String = encode(tables.nameComponents(id))

  def encode(components: Vector[Either[String, BigInt]]): String = {
    if (components.isEmpty) ""
    else if (
      components.forall {
        case Left(value) =>
          IdentifierSyntax.isAtom(value) &&
          !value.startsWith("$lean") && !value.startsWith("$raccoon")
        case Right(_) => false
      }
    ) components.collect { case Left(value) => value }.mkString(".")
    else
      EncodedPrefix + components.map {
        case Left(value) =>
          val bytes = value.getBytes(StandardCharsets.UTF_8)
          s".s${bytes.length}_${bytes.map(b => f"${b & 0xff}%02x").mkString}"
        case Right(value) => s".n${value.toString.length}_${value}"
      }.mkString
  }

  def decode(name: String): Option[Vector[Either[String, BigInt]]] = {
    if (!name.startsWith(EncodedPrefix)) {
      if (name.isEmpty) Some(Vector.empty)
      else {
        val components = name.split("\\.", -1).toVector
        if (
          components.forall(component =>
            IdentifierSyntax.isAtom(component) && !component.startsWith("$lean") && !component.startsWith("$raccoon")
          )
        ) Some(components.map(Left(_)))
        else None
      }
    } else {
      var offset = EncodedPrefix.length
      val result = Vector.newBuilder[Either[String, BigInt]]
      try {
        while (offset < name.length) {
          if (name.charAt(offset) != '.') return None
          offset += 1
          if (offset >= name.length) return None
          val tag = name.charAt(offset); offset += 1
          val underscore = name.indexOf('_', offset)
          if (underscore < 0) return None
          val lengthDigits = name.substring(offset, underscore)
          if (
            lengthDigits.isEmpty || !lengthDigits.forall(_.isDigit) ||
            (lengthDigits.length > 1 && lengthDigits.head == '0')
          ) return None
          val length = lengthDigits.toInt
          offset = underscore + 1
          tag match {
            case 's' =>
              val hexLength = Math.multiplyExact(length, 2)
              if (offset + hexLength > name.length) return None
              val bytes = Array.ofDim[Byte](length)
              var i = 0
              while (i < length) {
                val byte = Integer.parseInt(name.substring(offset + i * 2, offset + i * 2 + 2), 16)
                bytes(i) = byte.toByte; i += 1
              }
              result += Left(new String(bytes, StandardCharsets.UTF_8)); offset += hexLength
            case 'n' =>
              if (offset + length > name.length) return None
              val digits = name.substring(offset, offset + length)
              if (digits.isEmpty || !digits.forall(_.isDigit)) return None
              result += Right(BigInt(digits)); offset += length
            case _ => return None
          }
        }
        val decoded = result.result()
        if (encode(decoded) == name) Some(decoded) else None
      } catch {
        case _: ArithmeticException | _: NumberFormatException | _: IndexOutOfBoundsException |
            _: NegativeArraySizeException =>
          None
      }
    }
  }
}

sealed trait ImportedGlobalStatus
case object Installed extends ImportedGlobalStatus
case object SkippedUnsafe extends ImportedGlobalStatus

final case class ImportedGlobal(
    sourceName: LeanExportIr.NameId,
    coreName: String,
    provenance: LeanExportIr.ExportProvenance,
    status: ImportedGlobalStatus,
    levelParameters: Vector[LeanExportIr.NameId],
    callingConvention: Option[ImportedCallingConvention] = None,
    primitiveCapability: Option[String] = None
)

final class LeanGlobalRegistry private (private val entries: Map[Vector[Either[String, BigInt]], ImportedGlobal]) {
  def get(name: LeanExportIr.NameId, tables: LeanExportIr.ExportTables): Option[ImportedGlobal] =
    entries.get(tables.nameComponents(name))

  def add(global: ImportedGlobal, tables: LeanExportIr.ExportTables): LeanGlobalRegistry = {
    val key = tables.nameComponents(global.sourceName)
    if (entries.contains(key)) throw new IllegalArgumentException(s"duplicate imported global ${global.coreName}")
    new LeanGlobalRegistry(entries + (key -> global))
  }

  def values: Vector[ImportedGlobal] = entries.values.toVector
}

object LeanGlobalRegistry {
  val empty: LeanGlobalRegistry = new LeanGlobalRegistry(Map.empty)
}
