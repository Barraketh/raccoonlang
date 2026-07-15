package com.raccoonlang

import com.fasterxml.jackson.core.{JsonFactory, JsonGenerator, JsonParser, JsonToken}

import java.io.{ByteArrayOutputStream, InputStream}
import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path, Paths}
import scala.collection.mutable
import scala.util.Using
import scala.util.control.NonFatal

/** Reader-only Mathlib export pass for docs/mathlib-export-port.md's M0 milestone. */
object LeanExportM0 {
  final val SupportedFormatVersion = "3.1.0"

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
    // Names reserved by Raccoon's native-literal plan; retained in case T1 maps before scanning.
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

  final case class Metadata(
      exporterName: String,
      exporterVersion: String,
      leanVersion: String,
      leanGitHash: String,
      formatVersion: String
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
      irreducibleDeclarations: Vector[String]
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
      appendNames(
        out,
        "nested inductives",
        nestedInductives.map(item => s"${item.name} (${item.nestedOccurrences})")
      )
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

    private def writeJson(generator: JsonGenerator): Unit = {
      generator.writeStartObject()
      generator.writeStringField("source", source)
      generator.writeObjectFieldStart("metadata")
      generator.writeStringField("exporterName", metadata.exporterName)
      generator.writeStringField("exporterVersion", metadata.exporterVersion)
      generator.writeStringField("leanVersion", metadata.leanVersion)
      generator.writeStringField("leanGitHash", metadata.leanGitHash)
      generator.writeStringField("formatVersion", metadata.formatVersion)
      generator.writeEndObject()
      generator.writeNumberField("objects", objects)
      generator.writeNumberField("names", names)
      generator.writeNumberField("levels", levels)
      generator.writeNumberField("expressions", expressions)
      generator.writeNumberField("declarations", declarations)
      generator.writeNumberField("inductiveBlocks", inductiveBlocks)
      writeStringArray(generator, "sortImaxDeclaredTypes", sortImaxDeclaredTypes)
      generator.writeArrayFieldStart("mutualBlocks")
      mutualBlocks.foreach { block =>
        generator.writeStartArray()
        block.typeNames.foreach(generator.writeString)
        generator.writeEndArray()
      }
      generator.writeEndArray()
      generator.writeArrayFieldStart("nestedInductives")
      nestedInductives.foreach { item =>
        generator.writeStartObject()
        generator.writeStringField("name", item.name)
        generator.writeNumberField("nestedOccurrences", item.nestedOccurrences)
        generator.writeEndObject()
      }
      generator.writeEndArray()
      writeStringArray(generator, "sortMotiveAccRecOutsideFixCluster", sortMotiveAccRecOutsideFixCluster)
      generator.writeNumberField("projectionNodes", projectionNodes)
      generator.writeNumberField("natLiteralNodes", natLiteralNodes)
      generator.writeNumberField("stringLiteralNodes", stringLiteralNodes)
      generator.writeObjectFieldStart("nativeNatOps")
      nativeNatOps.foreach { case (name, count) => generator.writeNumberField(name, count) }
      generator.writeEndObject()
      writeStringArray(generator, "irreducibleDeclarations", irreducibleDeclarations)
      generator.writeEndObject()
    }

    private def writeStringArray(generator: JsonGenerator, field: String, values: Seq[String]): Unit = {
      generator.writeArrayFieldStart(field)
      values.foreach(generator.writeString)
      generator.writeEndArray()
    }
  }

  final case class ScanError(source: String, line: Long, column: Long, detail: String)
    extends RuntimeException(s"$source:$line:$column: $detail")

  def scan(path: Path): Report =
    Using.resource(Files.newInputStream(path))(input => scan(input, path.toString))

  def scan(input: InputStream, source: String = "<input>"): Report = {
    val parser = new JsonFactory().createParser(input)
    try new Scanner(parser, source).scan()
    catch {
      case error: ScanError => throw error
      case NonFatal(error) =>
        val location = parser.currentLocation()
        throw ScanError(source, location.getLineNr.toLong, location.getColumnNr.toLong, error.getMessage)
    } finally parser.close()
  }

  private sealed trait PendingPrimitive {
    def indexField: String
  }
  private final case class PendingName(value: String) extends PendingPrimitive {
    override val indexField: String = "in"
  }
  private final case class PendingLevel(hasImax: Boolean, definitelyZero: Boolean) extends PendingPrimitive {
    override val indexField: String = "il"
  }
  private final case class PendingExpr(hasSortImax: Boolean, hasSortMotiveAccRec: Boolean) extends PendingPrimitive {
    override val indexField: String = "ie"
  }

  private final case class SimpleDeclaration(
      name: Int,
      tpe: Int,
      bodies: Vector[Int],
      irreducible: Boolean
  )
  private final case class InductiveValue(name: Int, tpe: Int, numNested: Int)
  private final case class ConstructorValue(name: Int, tpe: Int)
  private final case class RecursorValue(name: Int, tpe: Int, ruleBodies: Vector[Int])

  private final class Scanner(parser: JsonParser, source: String) {
    private val names = mutable.ArrayBuffer("")
    private var levelCount = 1
    private val levelsWithImax = mutable.BitSet.empty
    private val definitelyZeroLevels = mutable.BitSet(0)
    private var exprCount = 0
    private val exprsWithSortImax = mutable.BitSet.empty
    private val exprsWithSortMotiveAccRec = mutable.BitSet.empty

    private var metadata: Option[Metadata] = None
    private var objectCount = 0L
    private var declarationCount = 0L
    private var inductiveBlockCount = 0L
    private val sortImaxDeclaredTypes = mutable.ArrayBuffer.empty[String]
    private val mutualBlocks = mutable.ArrayBuffer.empty[MutualBlock]
    private val nestedInductives = mutable.ArrayBuffer.empty[NestedInductive]
    private val sortMotiveAccRecOutsideFixCluster = mutable.ArrayBuffer.empty[String]
    private var projectionNodes = 0L
    private var natLiteralNodes = 0L
    private var stringLiteralNodes = 0L
    private val nativeNatOpCounts = mutable.Map.empty[String, Long]
    private val irreducibleDeclarations = mutable.ArrayBuffer.empty[String]

    def scan(): Report = {
      var token = parser.nextToken()
      while (token != null) {
        expect(JsonToken.START_OBJECT)
        objectCount += 1
        parseTopObject()
        token = parser.nextToken()
      }
      val meta = metadata.getOrElse(fail("export is missing its initial metadata object"))
      Report(
        source = source,
        metadata = meta,
        objects = objectCount,
        names = names.size,
        levels = levelCount,
        expressions = exprCount,
        declarations = declarationCount,
        inductiveBlocks = inductiveBlockCount,
        sortImaxDeclaredTypes = sortImaxDeclaredTypes.toVector,
        mutualBlocks = mutualBlocks.toVector,
        nestedInductives = nestedInductives.toVector,
        sortMotiveAccRecOutsideFixCluster = sortMotiveAccRecOutsideFixCluster.toVector,
        projectionNodes = projectionNodes,
        natLiteralNodes = natLiteralNodes,
        stringLiteralNodes = stringLiteralNodes,
        nativeNatOps = nativeNatOpCounts.toVector.sortBy(_._1),
        irreducibleDeclarations = irreducibleDeclarations.toVector
      )
    }

    private def parseTopObject(): Unit = {
      var pending: Option[PendingPrimitive] = None
      var index = Option.empty[Int]
      var indexField = Option.empty[String]
      var payloads = 0

      objectFields { field =>
        field match {
          case "in" | "il" | "ie" =>
            if (index.nonEmpty) fail("primitive object contains more than one index")
            index = Some(readInt())
            indexField = Some(field)
          case "meta" =>
            payloads += 1
            if (objectCount != 1) fail("metadata must be the first export object")
            if (metadata.nonEmpty) fail("export contains more than one metadata object")
            metadata = Some(parseMetadata())
          case "str" =>
            payloads += 1
            pending = Some(PendingName(parseNameString()))
          case "num" =>
            payloads += 1
            pending = Some(PendingName(parseNameNumber()))
          case "succ" =>
            payloads += 1
            val child = readInt()
            requireLevel(child)
            pending = Some(PendingLevel(levelsWithImax(child), definitelyZero = false))
          case "max" =>
            payloads += 1
            val refs = readFixedIntArray(2)
            refs.foreach(requireLevel)
            pending = Some(
              PendingLevel(
                hasImax = refs.exists(levelsWithImax),
                definitelyZero = refs.forall(definitelyZeroLevels)
              )
            )
          case "imax" =>
            payloads += 1
            val refs = readFixedIntArray(2)
            refs.foreach(requireLevel)
            pending = Some(PendingLevel(hasImax = true, definitelyZero = definitelyZeroLevels(refs(1))))
          case "param" =>
            payloads += 1
            requireName(readInt())
            pending = Some(PendingLevel(hasImax = false, definitelyZero = false))
          case "bvar" =>
            payloads += 1
            readInt()
            pending = Some(PendingExpr(hasSortImax = false, hasSortMotiveAccRec = false))
          case "sort" =>
            payloads += 1
            val level = readInt()
            requireLevel(level)
            pending = Some(PendingExpr(hasSortImax = levelsWithImax(level), hasSortMotiveAccRec = false))
          case "const" =>
            payloads += 1
            pending = Some(parseConst())
          case "app" =>
            payloads += 1
            pending = Some(exprFromChildren(parseExprRefs(Set("fn", "arg"))))
          case "lam" | "forallE" =>
            payloads += 1
            pending = Some(exprFromChildren(parseExprRefs(Set("type", "body"), nameFields = Set("name"))))
          case "letE" =>
            payloads += 1
            pending = Some(
              exprFromChildren(parseExprRefs(Set("type", "value", "body"), nameFields = Set("name")))
            )
          case "proj" =>
            payloads += 1
            projectionNodes += 1
            pending = Some(exprFromChildren(parseProjection()))
          case "natVal" =>
            payloads += 1
            readString()
            natLiteralNodes += 1
            pending = Some(PendingExpr(hasSortImax = false, hasSortMotiveAccRec = false))
          case "strVal" =>
            payloads += 1
            readString()
            stringLiteralNodes += 1
            pending = Some(PendingExpr(hasSortImax = false, hasSortMotiveAccRec = false))
          case "mdata" =>
            payloads += 1
            pending = Some(exprFromChildren(parseMetadataExpr()))
          case "axiom" | "def" | "opaque" | "thm" | "quot" =>
            payloads += 1
            register(parseSimpleDeclaration(field))
          case "inductive" =>
            payloads += 1
            registerInductiveBlock()
          case other => fail(s"unknown top-level export field '$other'")
        }
      }

      if (payloads != 1) fail(s"export object must contain exactly one payload, found $payloads")
      pending match {
        case Some(value) =>
          val actualIndex = index.getOrElse(fail(s"${value.indexField} is missing from primitive object"))
          if (indexField.get != value.indexField)
            fail(s"primitive uses index field '${indexField.get}', expected '${value.indexField}'")
          appendPrimitive(actualIndex, value)
        case None if index.nonEmpty => fail("declaration or metadata object contains a primitive index")
        case None                   =>
      }
    }

    private def appendPrimitive(index: Int, pending: PendingPrimitive): Unit =
      pending match {
        case PendingName(value) =>
          requireNextIndex("name", index, names.size)
          names += value
        case PendingLevel(hasImax, definitelyZero) =>
          requireNextIndex("level", index, levelCount)
          if (hasImax) levelsWithImax += index
          if (definitelyZero) definitelyZeroLevels += index
          levelCount += 1
        case PendingExpr(hasSortImax, hasSortMotiveAccRec) =>
          requireNextIndex("expression", index, exprCount)
          if (hasSortImax) exprsWithSortImax += index
          if (hasSortMotiveAccRec) exprsWithSortMotiveAccRec += index
          exprCount += 1
      }

    private def parseMetadata(): Metadata = {
      var exporterName = Option.empty[String]
      var exporterVersion = Option.empty[String]
      var leanVersion = Option.empty[String]
      var leanGitHash = Option.empty[String]
      var formatVersion = Option.empty[String]
      objectFields {
        case "exporter" =>
          objectFields {
            case "name"    => exporterName = Some(readString())
            case "version" => exporterVersion = Some(readString())
            case _         => parser.skipChildren()
          }
        case "lean" =>
          objectFields {
            case "version" => leanVersion = Some(readString())
            case "githash" => leanGitHash = Some(readString())
            case _         => parser.skipChildren()
          }
        case "format" =>
          objectFields {
            case "version" => formatVersion = Some(readString())
            case _         => parser.skipChildren()
          }
        case _ => parser.skipChildren()
      }
      val result = Metadata(
        required(exporterName, "meta.exporter.name"),
        required(exporterVersion, "meta.exporter.version"),
        required(leanVersion, "meta.lean.version"),
        required(leanGitHash, "meta.lean.githash"),
        required(formatVersion, "meta.format.version")
      )
      if (result.formatVersion != SupportedFormatVersion)
        fail(s"unsupported lean4export format ${result.formatVersion}; expected $SupportedFormatVersion")
      result
    }

    private def parseNameString(): String = {
      var prefix = Option.empty[Int]
      var component = Option.empty[String]
      objectFields {
        case "pre" => prefix = Some(readInt())
        case "str" => component = Some(readString())
        case field => fail(s"unknown Name.str field '$field'")
      }
      appendName(required(prefix, "Name.str.pre"), required(component, "Name.str.str"))
    }

    private def parseNameNumber(): String = {
      var prefix = Option.empty[Int]
      var component = Option.empty[String]
      objectFields {
        case "pre" => prefix = Some(readInt())
        case "i"   => component = Some(readIntegerText())
        case field => fail(s"unknown Name.num field '$field'")
      }
      appendName(required(prefix, "Name.num.pre"), required(component, "Name.num.i"))
    }

    private def appendName(prefix: Int, component: String): String = {
      requireName(prefix)
      val base = names(prefix)
      if (base.isEmpty) component else s"$base.$component"
    }

    private def parseConst(): PendingExpr = {
      var nameIndex = Option.empty[Int]
      var universes = Vector.empty[Int]
      objectFields {
        case "name" => nameIndex = Some(readInt())
        case "us"   => universes = readIntArray()
        case field  => fail(s"unknown Expr.const field '$field'")
      }
      val resolvedNameIndex = required(nameIndex, "Expr.const.name")
      requireName(resolvedNameIndex)
      universes.foreach(requireLevel)
      val name = names(resolvedNameIndex)
      if (NativeNatOps(name)) nativeNatOpCounts.update(name, nativeNatOpCounts.getOrElse(name, 0L) + 1L)
      val sortMotiveAccRec =
        if (name == "Acc.rec") {
          val motiveLevel = universes.headOption.getOrElse(fail("Acc.rec constant is missing its motive universe"))
          !definitelyZeroLevels(motiveLevel)
        } else false
      PendingExpr(hasSortImax = false, hasSortMotiveAccRec = sortMotiveAccRec)
    }

    private def parseExprRefs(requiredExprFields: Set[String], nameFields: Set[String] = Set.empty): Vector[Int] = {
      val refs = mutable.Map.empty[String, Int]
      objectFields { field =>
        if (requiredExprFields(field)) refs.update(field, readInt())
        else if (nameFields(field)) requireName(readInt())
        else parser.skipChildren()
      }
      requiredExprFields.toVector.sorted.map(field =>
        refs.getOrElse(field, fail(s"expression field '$field' is missing"))
      )
    }

    private def parseProjection(): Vector[Int] = {
      var struct = Option.empty[Int]
      objectFields {
        case "typeName" => requireName(readInt())
        case "idx"      => readInt()
        case "struct"   => struct = Some(readInt())
        case field      => fail(s"unknown Expr.proj field '$field'")
      }
      Vector(required(struct, "Expr.proj.struct"))
    }

    private def parseMetadataExpr(): Vector[Int] = {
      var expr = Option.empty[Int]
      objectFields {
        case "expr" => expr = Some(readInt())
        case "data" => parser.skipChildren()
        case field  => fail(s"unknown Expr.mdata field '$field'")
      }
      Vector(required(expr, "Expr.mdata.expr"))
    }

    private def exprFromChildren(children: Vector[Int]): PendingExpr = {
      children.foreach(requireExpr)
      PendingExpr(
        hasSortImax = children.exists(exprsWithSortImax),
        hasSortMotiveAccRec = children.exists(exprsWithSortMotiveAccRec)
      )
    }

    private def parseSimpleDeclaration(kind: String): SimpleDeclaration = {
      var name = Option.empty[Int]
      var tpe = Option.empty[Int]
      val bodies = mutable.ArrayBuffer.empty[Int]
      var opaqueHint = false
      objectFields {
        case "name"  => name = Some(readInt())
        case "type"  => tpe = Some(readInt())
        case "value" => bodies += readInt()
        case "hints" =>
          opaqueHint = parser.currentToken() == JsonToken.VALUE_STRING && parser.getText == "opaque"
          parser.skipChildren()
        case _ => parser.skipChildren()
      }
      SimpleDeclaration(
        name = required(name, s"$kind.name"),
        tpe = required(tpe, s"$kind.type"),
        bodies = bodies.toVector,
        irreducible = kind == "opaque" || (kind == "def" && opaqueHint)
      )
    }

    private def register(declaration: SimpleDeclaration): Unit = {
      requireName(declaration.name)
      requireExpr(declaration.tpe)
      declaration.bodies.foreach(requireExpr)
      val name = names(declaration.name)
      declarationCount += 1
      if (exprsWithSortImax(declaration.tpe)) sortImaxDeclaredTypes += name
      if (
        !AccFixCluster(name) &&
        (exprsWithSortMotiveAccRec(declaration.tpe) || declaration.bodies.exists(exprsWithSortMotiveAccRec))
      ) sortMotiveAccRecOutsideFixCluster += name
      if (declaration.irreducible) irreducibleDeclarations += name
    }

    private def registerInductiveBlock(): Unit = {
      var inductives = Vector.empty[InductiveValue]
      var constructors = Vector.empty[ConstructorValue]
      var recursors = Vector.empty[RecursorValue]
      objectFields {
        case "types" => inductives = readObjectArray(parseInductiveValue())
        case "ctors" => constructors = readObjectArray(parseConstructorValue())
        case "recs"  => recursors = readObjectArray(parseRecursorValue())
        case field   => fail(s"unknown inductive block field '$field'")
      }
      if (inductives.isEmpty) fail("inductive block contains no types")
      inductiveBlockCount += 1
      val typeNames = inductives.map(value => resolveName(value.name))
      if (typeNames.size > 1) mutualBlocks += MutualBlock(typeNames)
      inductives.foreach { value =>
        register(SimpleDeclaration(value.name, value.tpe, Vector.empty, irreducible = false))
        if (value.numNested > 0)
          nestedInductives += NestedInductive(resolveName(value.name), value.numNested)
      }
      constructors.foreach(value =>
        register(SimpleDeclaration(value.name, value.tpe, Vector.empty, irreducible = false))
      )
      recursors.foreach { value =>
        register(SimpleDeclaration(value.name, value.tpe, value.ruleBodies, irreducible = false))
      }
    }

    private def parseInductiveValue(): InductiveValue = {
      var name = Option.empty[Int]
      var tpe = Option.empty[Int]
      var numNested = Option.empty[Int]
      objectFields {
        case "name"      => name = Some(readInt())
        case "type"      => tpe = Some(readInt())
        case "numNested" => numNested = Some(readInt())
        case _           => parser.skipChildren()
      }
      InductiveValue(
        required(name, "InductiveVal.name"),
        required(tpe, "InductiveVal.type"),
        required(numNested, "InductiveVal.numNested")
      )
    }

    private def parseConstructorValue(): ConstructorValue = {
      var name = Option.empty[Int]
      var tpe = Option.empty[Int]
      objectFields {
        case "name" => name = Some(readInt())
        case "type" => tpe = Some(readInt())
        case _      => parser.skipChildren()
      }
      ConstructorValue(required(name, "ConstructorVal.name"), required(tpe, "ConstructorVal.type"))
    }

    private def parseRecursorValue(): RecursorValue = {
      var name = Option.empty[Int]
      var tpe = Option.empty[Int]
      var rules = Vector.empty[Int]
      objectFields {
        case "name"  => name = Some(readInt())
        case "type"  => tpe = Some(readInt())
        case "rules" => rules = readObjectArray(parseRecursorRule())
        case _       => parser.skipChildren()
      }
      RecursorValue(required(name, "RecursorVal.name"), required(tpe, "RecursorVal.type"), rules)
    }

    private def parseRecursorRule(): Int = {
      var rhs = Option.empty[Int]
      objectFields {
        case "rhs" => rhs = Some(readInt())
        case _     => parser.skipChildren()
      }
      required(rhs, "RecursorRule.rhs")
    }

    private def objectFields(consume: String => Unit): Unit = {
      expect(JsonToken.START_OBJECT)
      var token = parser.nextToken()
      while (token != JsonToken.END_OBJECT) {
        if (token == null) fail("unexpected end of input inside object")
        expect(JsonToken.FIELD_NAME)
        val field = parser.currentName()
        if (parser.nextToken() == null) fail(s"missing value for field '$field'")
        consume(field)
        token = parser.nextToken()
      }
    }

    private def readObjectArray[A](read: => A): Vector[A] = {
      expect(JsonToken.START_ARRAY)
      val result = Vector.newBuilder[A]
      var token = parser.nextToken()
      while (token != JsonToken.END_ARRAY) {
        if (token == null) fail("unexpected end of input inside array")
        expect(JsonToken.START_OBJECT)
        result += read
        token = parser.nextToken()
      }
      result.result()
    }

    private def readIntArray(): Vector[Int] = {
      expect(JsonToken.START_ARRAY)
      val result = Vector.newBuilder[Int]
      var token = parser.nextToken()
      while (token != JsonToken.END_ARRAY) {
        if (token == null) fail("unexpected end of input inside array")
        result += readInt()
        token = parser.nextToken()
      }
      result.result()
    }

    private def readFixedIntArray(size: Int): Vector[Int] = {
      val result = readIntArray()
      if (result.size != size) fail(s"expected an array of $size integers, found ${result.size}")
      result
    }

    private def readInt(): Int = {
      expect(JsonToken.VALUE_NUMBER_INT)
      try parser.getIntValue
      catch {
        case NonFatal(_) => fail(s"integer is out of 32-bit range: ${parser.getText}")
      }
    }

    private def readIntegerText(): String = {
      expect(JsonToken.VALUE_NUMBER_INT)
      parser.getText
    }

    private def readString(): String = {
      expect(JsonToken.VALUE_STRING)
      parser.getText
    }

    private def resolveName(index: Int): String = {
      requireName(index)
      names(index)
    }

    private def requireName(index: Int): Unit =
      if (index < 0 || index >= names.size) fail(s"name reference $index has not been defined")

    private def requireLevel(index: Int): Unit =
      if (index < 0 || index >= levelCount) fail(s"level reference $index has not been defined")

    private def requireExpr(index: Int): Unit =
      if (index < 0 || index >= exprCount) fail(s"expression reference $index has not been defined")

    private def requireNextIndex(kind: String, actual: Int, expected: Int): Unit =
      if (actual != expected) fail(s"$kind index $actual is out of sequence; expected $expected")

    private def expect(expected: JsonToken): Unit =
      if (parser.currentToken() != expected)
        fail(s"expected $expected, found ${Option(parser.currentToken()).fold("end of input")(_.toString)}")

    private def required[A](value: Option[A], field: String): A =
      value.getOrElse(fail(s"required field '$field' is missing"))

    private def fail(detail: String): Nothing = {
      val location = parser.currentLocation()
      throw ScanError(source, location.getLineNr.toLong, location.getColumnNr.toLong, detail)
    }
  }
}

object MathlibExportStats {
  def main(args: Array[String]): Unit = {
    val (json, paths) = args.toList.partition(_ == "--json") match {
      case (flags, rest) => (flags.nonEmpty, rest)
    }
    if (paths.isEmpty || paths.exists(_.startsWith("--"))) {
      System.err.println("Usage: MathlibExportStats [--json] <export.ndjson> [<export.ndjson> ...]")
      sys.exit(2)
    }
    try {
      val reports = paths.map(path => LeanExportM0.scan(Paths.get(path)))
      if (json) reports.foreach(report => println(report.renderJson))
      else reports.foreach(report => print(report.renderText))
    } catch {
      case NonFatal(error) =>
        System.err.println(Option(error.getMessage).getOrElse(error.toString))
        sys.exit(1)
    }
  }
}
