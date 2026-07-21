package com.raccoonlang.translator

import com.fasterxml.jackson.core.{JsonFactory, JsonGenerator}
import com.raccoonlang.translator.LeanExportIr._

import java.io.{ByteArrayOutputStream, InputStream}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.util.Using
import scala.util.control.NonFatal

/** Statistics consumer for the shared lean4export semantic reader. */
object LeanExportM0 {
  final val SupportedFormatVersion: String = LeanExportReader.FormatVersion
  type Metadata = ExportMeta

  private val NativeNatOps = Set(
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.pow",
    "Nat.beq",
    "Nat.ble",
    "Nat.blt",
    "Nat.div",
    "Nat.mod",
    "Nat.gcd",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "Nat.lxor",
    "Nat.shiftl",
    "Nat.shiftr"
  )
  private val AccFixCluster = Set(
    "Acc.rec",
    "WellFounded.recursion",
    "WellFounded.fixF",
    "WellFounded.fixF_eq",
    "WellFounded.fix",
    "WellFounded.fix_eq"
  )

  final case class MutualBlock(typeNames: Vector[String])
  final case class NestedInductive(name: String, nestedOccurrences: Int)

  final case class Report(
      source: String,
      metadata: Metadata,
      objects: Long,
      names: Int,
      levels: Int,
      expressions: Int,
      declarations: Long,
      inductiveBlocks: Long,
      sortImaxDeclaredTypes: Vector[String],
      mutualBlocks: Vector[MutualBlock],
      nestedInductives: Vector[NestedInductive],
      sortMotiveAccRecOutsideFixCluster: Vector[String],
      projectionNodes: Long,
      natLiteralNodes: Long,
      stringLiteralNodes: Long,
      nativeNatOps: Vector[(String, Long)],
      irreducibleDeclarations: Vector[String],
      nodeStoreBytes: Long = 0L,
      nodeStoreHighWaterBytes: Long = 0L
  ) {
    def renderText: String = {
      val out = new StringBuilder
      out.append(s"M0 Mathlib-export statistics: $source\n")
      out.append(
        s"  format ${metadata.formatVersion}; Lean ${metadata.leanVersion} (${metadata.leanGitHash}); " +
          s"${metadata.exporterName} ${metadata.exporterVersion}\n"
      )
      out.append(s"  objects: $objects; names: $names; levels: $levels; expressions: $expressions\n")
      out.append(s"  declarations: $declarations; inductive blocks: $inductiveBlocks\n")
      appendNames(out, "declared types containing Sort(imax ...)", sortImaxDeclaredTypes)
      appendGroups(out, "mutual inductive blocks", mutualBlocks.map(_.typeNames))
      appendNames(out, "nested inductives", nestedInductives.map(i => s"${i.name} (${i.nestedOccurrences})"))
      appendNames(out, "Sort-motive Acc.rec outside the fix cluster", sortMotiveAccRecOutsideFixCluster)
      out.append(
        s"  expression nodes: proj=$projectionNodes; Nat literals=$natLiteralNodes; String literals=$stringLiteralNodes\n"
      )
      appendNames(out, "native Nat operations", nativeNatOps.map { case (name, count) => s"$name ($count)" })
      appendNames(out, "irreducible declarations", irreducibleDeclarations)
      out.result()
    }

    def renderJson: String = {
      val bytes = new ByteArrayOutputStream
      val generator = new JsonFactory().createGenerator(bytes)
      try writeJson(generator)
      finally generator.close()
      bytes.toString(StandardCharsets.UTF_8.name())
    }

    private def appendNames(out: StringBuilder, label: String, values: Seq[String]): Unit = {
      out.append(s"  $label: ${values.size}\n")
      values.foreach(value => out.append(s"    $value\n"))
    }
    private def appendGroups(out: StringBuilder, label: String, groups: Seq[Seq[String]]): Unit = {
      out.append(s"  $label: ${groups.size}\n")
      groups.foreach(group => out.append(s"    ${group.mkString(", ")}\n"))
    }
    private def writeJson(g: JsonGenerator): Unit = {
      g.writeStartObject(); g.writeStringField("source", source); g.writeObjectFieldStart("metadata")
      g.writeStringField("exporterName", metadata.exporterName);
      g.writeStringField("exporterVersion", metadata.exporterVersion)
      g.writeStringField("leanVersion", metadata.leanVersion); g.writeStringField("leanGitHash", metadata.leanGitHash)
      g.writeStringField("formatVersion", metadata.formatVersion); g.writeEndObject()
      g.writeNumberField("objects", objects); g.writeNumberField("names", names); g.writeNumberField("levels", levels)
      g.writeNumberField("expressions", expressions); g.writeNumberField("declarations", declarations)
      g.writeNumberField("inductiveBlocks", inductiveBlocks)
      writeStrings(g, "sortImaxDeclaredTypes", sortImaxDeclaredTypes)
      g.writeArrayFieldStart("mutualBlocks");
      mutualBlocks.foreach { b => g.writeStartArray(); b.typeNames.foreach(g.writeString); g.writeEndArray() };
      g.writeEndArray()
      g.writeArrayFieldStart("nestedInductives");
      nestedInductives.foreach { i =>
        g.writeStartObject(); g.writeStringField("name", i.name);
        g.writeNumberField("nestedOccurrences", i.nestedOccurrences); g.writeEndObject()
      }; g.writeEndArray()
      writeStrings(g, "sortMotiveAccRecOutsideFixCluster", sortMotiveAccRecOutsideFixCluster)
      g.writeNumberField("projectionNodes", projectionNodes); g.writeNumberField("natLiteralNodes", natLiteralNodes)
      g.writeNumberField("stringLiteralNodes", stringLiteralNodes); g.writeObjectFieldStart("nativeNatOps")
      nativeNatOps.foreach { case (name, count) => g.writeNumberField(name, count) }; g.writeEndObject()
      writeStrings(g, "irreducibleDeclarations", irreducibleDeclarations); g.writeEndObject()
    }
    private def writeStrings(g: JsonGenerator, field: String, values: Seq[String]): Unit = {
      g.writeArrayFieldStart(field); values.foreach(g.writeString); g.writeEndArray()
    }
  }

  final case class ScanError(source: String, line: Long, column: Long, detail: String)
    extends RuntimeException(s"$source:$line:$column: $detail")

  def scan(path: Path): Report = Using.resource(Files.newInputStream(path))(scan(_, path.toString))

  def scan(input: InputStream, source: String = "<input>"): Report = {
    val collector = new Collector(source)
    try {
      val result = LeanExportReader.read(input, source, collector)
      collector.report(result)
    } catch {
      case diagnostic: LeanImportDiagnostic =>
        throw ScanError(source, diagnostic.provenance.line, diagnostic.provenance.column, diagnostic.message)
    }
  }

  private final class Collector(source: String) extends LeanExportConsumer {
    private var metadata: Option[Metadata] = None
    private val declarations = mutable.ArrayBuffer.empty[ExportDecl]
    override def onMeta(meta: ExportMeta): Unit = metadata = Some(meta)
    override def onDeclaration(decl: ExportDecl, tables: ExportTables): Unit = declarations += decl
    override def finish(tables: ExportTables): Unit = ()

    def report(result: LeanExportReader.ReadResult): Report = {
      val tables = result.tables
      val levelImax = mutable.BitSet.empty
      val levelZero = mutable.BitSet(0)
      var level = 1
      while (level < tables.levelCount) {
        val node = tables.levelNode(LevelId(level))
        val has = node match {
          case LevelIMax(_, _)           => true
          case LevelSucc(of)             => levelImax(of.value)
          case LevelMax(left, right)     => levelImax(left.value) || levelImax(right.value)
          case LevelParam(_) | LevelZero => false
        }
        if (has) levelImax += level
        val isZero = node match {
          case LevelMax(left, right) => levelZero(left.value) && levelZero(right.value)
          case LevelIMax(_, right)   => levelZero(right.value)
          case LevelZero             => true
          case _                     => false
        }
        if (isZero) levelZero += level
        level += 1
      }

      val exprImax = mutable.BitSet.empty
      val exprAcc = mutable.BitSet.empty
      val nativeCounts = mutable.Map.empty[String, Long]
      var projections = 0L; var natLiterals = 0L; var stringLiterals = 0L
      var expr = 0
      while (expr < tables.expressionCount) {
        val node = tables.exprNode(ExprId(expr))
        val children: Vector[ExprId] = node match {
          case App(fn, arg)                => Vector(fn, arg)
          case Lam(_, ty, body, _)         => Vector(ty, body)
          case ForallE(_, ty, body, _)     => Vector(ty, body)
          case LetE(_, ty, value, body, _) => Vector(ty, value, body)
          case Proj(_, _, struct)          => projections += 1; Vector(struct)
          case MData(child)                => Vector(child)
          case NatVal(_)                   => natLiterals += 1; Vector.empty
          case StrVal(_)                   => stringLiterals += 1; Vector.empty
          case _                           => Vector.empty
        }
        val directImax = node match { case Sort(l) => levelImax(l.value); case _ => false }
        if (directImax || children.exists(id => exprImax(id.value))) exprImax += expr
        val directAcc = node match {
          case Const(name, universes) =>
            val decoded = tables.dottedName(name)
            if (NativeNatOps(decoded)) nativeCounts.update(decoded, nativeCounts.getOrElse(decoded, 0L) + 1L)
            decoded == "Acc.rec" && universes.headOption.exists(id => !levelZero(id.value))
          case _ => false
        }
        if (directAcc || children.exists(id => exprAcc(id.value))) exprAcc += expr
        expr += 1
      }

      val imaxDecls = Vector.newBuilder[String]; val outsideAcc = Vector.newBuilder[String]
      val mutual = Vector.newBuilder[MutualBlock]; val nested = Vector.newBuilder[NestedInductive]
      val irreducible = Vector.newBuilder[String]
      var blocks = 0L

      def inspect(name: NameId, tpe: ExprId, bodies: Vector[ExprId], opaque: Boolean): Unit = {
        val decoded = tables.dottedName(name)
        if (exprImax(tpe.value)) imaxDecls += decoded
        if (!AccFixCluster(decoded) && (exprAcc(tpe.value) || bodies.exists(id => exprAcc(id.value))))
          outsideAcc += decoded
        if (opaque) irreducible += decoded
      }

      declarations.foreach {
        case d: ExportAxiom   => inspect(d.name, d.tpe, Vector.empty, opaque = false)
        case d: ExportDef     => inspect(d.name, d.tpe, Vector(d.value), d.hint == HintOpaque)
        case d: ExportOpaque  => inspect(d.name, d.tpe, Vector(d.value), opaque = true)
        case d: ExportTheorem => inspect(d.name, d.tpe, Vector(d.value), opaque = false)
        case d: ExportQuot    => inspect(d.name, d.tpe, Vector.empty, opaque = false)
        case d: ExportInductive =>
          blocks += 1
          if (d.types.length > 1) mutual += MutualBlock(d.types.map(t => tables.dottedName(t.name)))
          d.types.foreach { t =>
            inspect(t.name, t.tpe, Vector.empty, opaque = false)
            if (t.numNested > 0) nested += NestedInductive(tables.dottedName(t.name), t.numNested)
          }
          d.constructors.foreach(c => inspect(c.name, c.tpe, Vector.empty, opaque = false))
          d.recursors.foreach(r => inspect(r.name, r.tpe, r.rules.map(_.rhs), opaque = false))
      }

      Report(
        source,
        metadata.getOrElse(result.meta),
        result.objects,
        tables.nameCount,
        tables.levelCount,
        tables.expressionCount,
        result.declarations,
        blocks,
        imaxDecls.result(),
        mutual.result(),
        nested.result(),
        outsideAcc.result(),
        projections,
        natLiterals,
        stringLiterals,
        nativeCounts.toVector.sortBy(_._1),
        irreducible.result(),
        tables.currentBytes,
        tables.highWaterBytes
      )
    }
  }
}

object MathlibExportStats {
  def main(args: Array[String]): Unit = {
    val (flags, paths) = args.toList.partition(_ == "--json")
    if (paths.isEmpty || paths.exists(_.startsWith("--"))) {
      System.err.println("Usage: MathlibExportStats [--json] <export.ndjson> [<export.ndjson> ...]")
      sys.exit(2)
    }
    try {
      val reports = paths.map(path => LeanExportM0.scan(Paths.get(path)))
      if (flags.nonEmpty) reports.foreach(r => println(r.renderJson)) else reports.foreach(r => print(r.renderText))
    } catch {
      case NonFatal(error) => System.err.println(Option(error.getMessage).getOrElse(error.toString)); sys.exit(1)
    }
  }
}
