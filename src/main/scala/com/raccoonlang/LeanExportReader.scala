package com.raccoonlang

import com.fasterxml.jackson.core.{JsonFactory, JsonParser, JsonToken}
import com.raccoonlang.LeanExportIr._

import java.io.InputStream
import java.nio.file.{Path, Paths}
import scala.collection.mutable
import scala.util.control.NonFatal

object LeanExportReader {
  final val ExporterName = "lean4export"
  final val ExporterVersion = "3.1.0"
  final val LeanVersion = "4.24.0-rc1"
  final val LeanGitHash = "919e297292280cdb27598edd4e03437be5850221"
  final val FormatVersion = "3.1.0"

  final case class ReadResult(meta: ExportMeta, tables: ExportTables, objects: Long, declarations: Long)

  def read(input: InputStream, source: String, consumer: LeanExportConsumer): ReadResult = {
    val parser = new JsonFactory().createParser(input)
    val reader = new Reader(parser, Paths.get(source), consumer)
    try reader.read()
    catch {
      case diagnostic: LeanImportDiagnostic => throw diagnostic
      case NonFatal(error) =>
        throw MalformedExport(
          reader.provenance("json"),
          Option(error.getMessage).getOrElse(error.toString)
        )
    } finally parser.close()
  }

  private sealed trait PendingPrimitive { def indexField: String }
  private final case class PendingName(node: NameNode) extends PendingPrimitive { val indexField = "in" }
  private final case class PendingLevel(node: LevelNode) extends PendingPrimitive { val indexField = "il" }
  private final case class PendingExpr(node: ExprNode) extends PendingPrimitive { val indexField = "ie" }

  private final class Reader(parser: JsonParser, source: Path, consumer: LeanExportConsumer) {
    private val tables = new ExportTables(source)
    private var objectOrdinal = 0L
    private var declarationCount = 0L
    private var meta: Option[ExportMeta] = None
    private val declarationNames = mutable.HashSet.empty[Vector[Either[String, BigInt]]]

    def provenance(kind: String, internId: Option[Int] = None, declaration: Option[String] = None): ExportProvenance = {
      val location = parser.currentLocation()
      ExportProvenance(
        source,
        location.getLineNr.toLong,
        location.getColumnNr,
        objectOrdinal,
        kind,
        internId,
        declaration
      )
    }

    def read(): ReadResult = {
      var token = parser.nextToken()
      while (token != null) {
        expect(JsonToken.START_OBJECT)
        objectOrdinal += 1
        parseTopObject()
        token = parser.nextToken()
      }
      val metadata = meta.getOrElse(fail("export is missing its initial metadata object"))
      consumer.finish(tables)
      ReadResult(metadata, tables, objectOrdinal, declarationCount)
    }

    private def parseTopObject(): Unit = {
      var pending: Option[PendingPrimitive] = None
      var index: Option[Int] = None
      var indexField: Option[String] = None
      var decl: Option[ExportDecl] = None
      var payloadCount = 0
      var payloadKind = "object"

      objectFields("top-level object") { field =>
        field match {
          case "in" | "il" | "ie" =>
            if (index.nonEmpty) fail("primitive object contains more than one index")
            index = Some(readNonNegativeInt(field))
            indexField = Some(field)
          case "meta" =>
            payloadCount += 1; payloadKind = "meta"
            if (objectOrdinal != 1) fail("metadata must be the first export object")
            if (meta.nonEmpty) fail("export contains more than one metadata object")
            val parsed = parseMeta()
            validateMeta(parsed)
            meta = Some(parsed)
            consumer.onMeta(parsed)
          case "str" => payloadCount += 1; payloadKind = "name"; pending = Some(PendingName(parseNameStr()))
          case "num" => payloadCount += 1; payloadKind = "name"; pending = Some(PendingName(parseNameNum()))
          case "succ" =>
            payloadCount += 1; payloadKind = "level"
            pending = Some(PendingLevel(LevelSucc(requireLevel(readNonNegativeInt("succ")))))
          case "max" =>
            payloadCount += 1; payloadKind = "level"
            val refs = readFixedIntArray(2, "max").map(requireLevel)
            pending = Some(PendingLevel(LevelMax(refs(0), refs(1))))
          case "imax" =>
            payloadCount += 1; payloadKind = "level"
            val refs = readFixedIntArray(2, "imax").map(requireLevel)
            pending = Some(PendingLevel(LevelIMax(refs(0), refs(1))))
          case "param" =>
            payloadCount += 1; payloadKind = "level"
            pending = Some(PendingLevel(LevelParam(requireName(readNonNegativeInt("param")))))
          case "bvar" =>
            payloadCount += 1; payloadKind = "expression"
            pending = Some(PendingExpr(BVar(readNonNegativeInt("bvar"))))
          case "sort" =>
            payloadCount += 1; payloadKind = "expression"
            pending = Some(PendingExpr(Sort(requireLevel(readNonNegativeInt("sort")))))
          case "const" => payloadCount += 1; payloadKind = "expression"; pending = Some(PendingExpr(parseConst()))
          case "app" => payloadCount += 1; payloadKind = "expression"; pending = Some(PendingExpr(parseApp()))
          case "lam" => payloadCount += 1; payloadKind = "expression"; pending = Some(PendingExpr(parseBinder(isPi = false)))
          case "forallE" => payloadCount += 1; payloadKind = "expression"; pending = Some(PendingExpr(parseBinder(isPi = true)))
          case "letE" => payloadCount += 1; payloadKind = "expression"; pending = Some(PendingExpr(parseLet()))
          case "proj" => payloadCount += 1; payloadKind = "expression"; pending = Some(PendingExpr(parseProj()))
          case "natVal" => payloadCount += 1; payloadKind = "expression"; pending = Some(PendingExpr(parseNat()))
          case "strVal" => payloadCount += 1; payloadKind = "expression"; pending = Some(PendingExpr(parseStringValue()))
          case "mdata" => payloadCount += 1; payloadKind = "expression"; pending = Some(PendingExpr(parseMData()))
          case "axiom" => payloadCount += 1; payloadKind = field; decl = Some(parseAxiom())
          case "def" => payloadCount += 1; payloadKind = field; decl = Some(parseDef())
          case "opaque" => payloadCount += 1; payloadKind = field; decl = Some(parseOpaque())
          case "thm" => payloadCount += 1; payloadKind = field; decl = Some(parseTheorem())
          case "quot" => payloadCount += 1; payloadKind = field; decl = Some(parseQuot())
          case "inductive" => payloadCount += 1; payloadKind = field; decl = Some(parseInductive())
          case other => fail(s"unknown top-level export field '$other'")
        }
      }

      if (payloadCount != 1) fail(s"export object must contain exactly one payload, found $payloadCount")
      if (meta.isEmpty && objectOrdinal != 1) fail("metadata must be the first export object")
      pending match {
        case Some(value) =>
          val actual = index.getOrElse(fail(s"${value.indexField} is missing from primitive object"))
          if (indexField.get != value.indexField)
            fail(s"primitive uses index field '${indexField.get}', expected '${value.indexField}'")
          value match {
            case PendingName(node) =>
              requireNextIndex("name", actual, tables.nameCount)
              tables.appendName(node, provenance("name", Some(actual)))
            case PendingLevel(node) =>
              requireNextIndex("level", actual, tables.levelCount)
              tables.appendLevel(node, provenance("level", Some(actual)))
            case PendingExpr(node) =>
              requireNextIndex("expression", actual, tables.expressionCount)
              tables.appendExpr(node, provenance("expression", Some(actual)))
          }
        case None if index.nonEmpty => fail("declaration or metadata object contains a primitive index")
        case None =>
      }
      decl.foreach(registerDeclaration(_, payloadKind))
    }

    private def validateMeta(value: ExportMeta): Unit = {
      val mismatch =
        if (value.exporterName != ExporterName) Some(s"exporter ${value.exporterName}; expected $ExporterName")
        else if (value.exporterVersion != ExporterVersion)
          Some(s"lean4export version ${value.exporterVersion}; expected $ExporterVersion")
        else if (value.leanVersion != LeanVersion) Some(s"Lean version ${value.leanVersion}; expected $LeanVersion")
        else if (value.leanGitHash != LeanGitHash)
          Some(s"Lean commit ${value.leanGitHash}; expected $LeanGitHash")
        else if (value.formatVersion != FormatVersion)
          Some(s"unsupported lean4export format ${value.formatVersion}; expected $FormatVersion")
        else None
      mismatch.foreach(detail => throw UnsupportedProducer(provenance("meta"), s"unsupported producer: $detail"))
    }

    private def parseMeta(): ExportMeta = {
      var exporterName: Option[String] = None
      var exporterVersion: Option[String] = None
      var leanVersion: Option[String] = None
      var leanHash: Option[String] = None
      var formatVersion: Option[String] = None
      objectFields("meta") {
        case "exporter" =>
          objectFields("meta.exporter") {
            case "name" => exporterName = Some(readString("meta.exporter.name"))
            case "version" => exporterVersion = Some(readString("meta.exporter.version"))
            case field => fail(s"unknown meta.exporter field '$field'")
          }
        case "lean" =>
          objectFields("meta.lean") {
            case "version" => leanVersion = Some(readString("meta.lean.version"))
            case "githash" => leanHash = Some(readString("meta.lean.githash"))
            case field => fail(s"unknown meta.lean field '$field'")
          }
        case "format" =>
          objectFields("meta.format") {
            case "version" => formatVersion = Some(readString("meta.format.version"))
            case field => fail(s"unknown meta.format field '$field'")
          }
        case field => fail(s"unknown meta field '$field'")
      }
      ExportMeta(
        required(exporterName, "meta.exporter.name"),
        required(exporterVersion, "meta.exporter.version"),
        required(leanVersion, "meta.lean.version"),
        required(leanHash, "meta.lean.githash"),
        required(formatVersion, "meta.format.version")
      )
    }

    private def parseNameStr(): NameNode = {
      var pre: Option[NameId] = None
      var value: Option[String] = None
      objectFields("Name.str") {
        case "pre" => pre = Some(requireName(readNonNegativeInt("Name.str.pre")))
        case "str" => value = Some(readString("Name.str.str"))
        case field => fail(s"unknown Name.str field '$field'")
      }
      NameStr(required(pre, "Name.str.pre"), required(value, "Name.str.str"))
    }

    private def parseNameNum(): NameNode = {
      var pre: Option[NameId] = None
      var value: Option[BigInt] = None
      objectFields("Name.num") {
        case "pre" => pre = Some(requireName(readNonNegativeInt("Name.num.pre")))
        case "i" => value = Some(readNonNegativeBigInt("Name.num.i"))
        case field => fail(s"unknown Name.num field '$field'")
      }
      NameNum(required(pre, "Name.num.pre"), required(value, "Name.num.i"))
    }

    private def parseConst(): ExprNode = {
      var name: Option[NameId] = None
      var levels: Option[Vector[LevelId]] = None
      objectFields("Expr.const") {
        case "name" => name = Some(requireName(readNonNegativeInt("Expr.const.name")))
        case "us" => levels = Some(readIntArray("Expr.const.us").map(requireLevel))
        case field => fail(s"unknown Expr.const field '$field'")
      }
      Const(required(name, "Expr.const.name"), required(levels, "Expr.const.us"))
    }

    private def parseApp(): ExprNode = {
      var fn: Option[ExprId] = None
      var arg: Option[ExprId] = None
      objectFields("Expr.app") {
        case "fn" => fn = Some(requireExpr(readNonNegativeInt("Expr.app.fn")))
        case "arg" => arg = Some(requireExpr(readNonNegativeInt("Expr.app.arg")))
        case field => fail(s"unknown Expr.app field '$field'")
      }
      App(required(fn, "Expr.app.fn"), required(arg, "Expr.app.arg"))
    }

    private def parseBinder(isPi: Boolean): ExprNode = {
      val label = if (isPi) "Expr.forallE" else "Expr.lam"
      var name: Option[NameId] = None
      var tpe: Option[ExprId] = None
      var body: Option[ExprId] = None
      var info: Option[BinderInfo] = None
      objectFields(label) {
        case "name" => name = Some(requireName(readNonNegativeInt(s"$label.name")))
        case "type" => tpe = Some(requireExpr(readNonNegativeInt(s"$label.type")))
        case "body" => body = Some(requireExpr(readNonNegativeInt(s"$label.body")))
        case "binderInfo" => info = Some(parseBinderInfo(readString(s"$label.binderInfo")))
        case field => fail(s"unknown $label field '$field'")
      }
      val values = (required(name, s"$label.name"), required(tpe, s"$label.type"), required(body, s"$label.body"))
      if (isPi) ForallE(values._1, values._2, values._3, required(info, s"$label.binderInfo"))
      else Lam(values._1, values._2, values._3, required(info, s"$label.binderInfo"))
    }

    private def parseLet(): ExprNode = {
      var name: Option[NameId] = None
      var tpe: Option[ExprId] = None
      var value: Option[ExprId] = None
      var body: Option[ExprId] = None
      var nonDep: Option[Boolean] = None
      objectFields("Expr.letE") {
        case "name" => name = Some(requireName(readNonNegativeInt("Expr.letE.name")))
        case "type" => tpe = Some(requireExpr(readNonNegativeInt("Expr.letE.type")))
        case "value" => value = Some(requireExpr(readNonNegativeInt("Expr.letE.value")))
        case "body" => body = Some(requireExpr(readNonNegativeInt("Expr.letE.body")))
        case "nondep" => nonDep = Some(readBoolean("Expr.letE.nondep"))
        case field => fail(s"unknown Expr.letE field '$field'")
      }
      LetE(
        required(name, "Expr.letE.name"), required(tpe, "Expr.letE.type"),
        required(value, "Expr.letE.value"), required(body, "Expr.letE.body"),
        required(nonDep, "Expr.letE.nondep")
      )
    }

    private def parseProj(): ExprNode = {
      var typeName: Option[NameId] = None
      var idx: Option[Int] = None
      var struct: Option[ExprId] = None
      objectFields("Expr.proj") {
        case "typeName" => typeName = Some(requireName(readNonNegativeInt("Expr.proj.typeName")))
        case "idx" => idx = Some(readNonNegativeInt("Expr.proj.idx"))
        case "struct" => struct = Some(requireExpr(readNonNegativeInt("Expr.proj.struct")))
        case field => fail(s"unknown Expr.proj field '$field'")
      }
      Proj(required(typeName, "Expr.proj.typeName"), required(idx, "Expr.proj.idx"), required(struct, "Expr.proj.struct"))
    }

    private def parseNat(): ExprNode = NatVal(readNonNegativeBigInt("Expr.natVal"))

    private def parseStringValue(): ExprNode = {
      val text = readString("Expr.strVal")
      val scalars = Vector.newBuilder[Int]
      var offset = 0
      while (offset < text.length) {
        val ch = text.charAt(offset)
        if (Character.isHighSurrogate(ch)) {
          if (offset + 1 >= text.length || !Character.isLowSurrogate(text.charAt(offset + 1)))
            fail(s"Expr.strVal contains an unpaired high surrogate at UTF-16 offset $offset")
          scalars += Character.toCodePoint(ch, text.charAt(offset + 1))
          offset += 2
        } else if (Character.isLowSurrogate(ch)) {
          fail(s"Expr.strVal contains an unpaired low surrogate at UTF-16 offset $offset")
        } else {
          scalars += ch.toInt
          offset += 1
        }
      }
      StrVal(scalars.result())
    }

    private def parseMData(): ExprNode = {
      var expr: Option[ExprId] = None
      objectFields("Expr.mdata") {
        case "expr" => expr = Some(requireExpr(readNonNegativeInt("Expr.mdata.expr")))
        case "data" => parser.skipChildren()
        case field => fail(s"unknown Expr.mdata field '$field'")
      }
      MData(required(expr, "Expr.mdata.expr"))
    }

    private def parseAxiom(): ExportDecl = {
      var name: Option[NameId] = None; var params: Option[Vector[NameId]] = None
      var tpe: Option[ExprId] = None; var unsafe: Option[Boolean] = None
      objectFields("axiom") {
        case "name" => name = Some(requireName(readNonNegativeInt("axiom.name")))
        case "levelParams" => params = Some(readIntArray("axiom.levelParams").map(requireName))
        case "type" => tpe = Some(requireExpr(readNonNegativeInt("axiom.type")))
        case "isUnsafe" => unsafe = Some(readBoolean("axiom.isUnsafe"))
        case field => fail(s"unknown axiom field '$field'")
      }
      val n = required(name, "axiom.name")
      ExportAxiom(n, required(params, "axiom.levelParams"), required(tpe, "axiom.type"),
        required(unsafe, "axiom.isUnsafe"), declarationProvenance("axiom", n))
    }

    private def parseDef(): ExportDecl = {
      var name: Option[NameId] = None; var params: Option[Vector[NameId]] = None; var tpe: Option[ExprId] = None
      var value: Option[ExprId] = None; var hint: Option[ExportDefHint] = None; var safety: Option[ExportSafety] = None
      var all: Option[Vector[NameId]] = None
      objectFields("def") {
        case "name" => name = Some(requireName(readNonNegativeInt("def.name")))
        case "levelParams" => params = Some(readIntArray("def.levelParams").map(requireName))
        case "type" => tpe = Some(requireExpr(readNonNegativeInt("def.type")))
        case "value" => value = Some(requireExpr(readNonNegativeInt("def.value")))
        case "hints" => hint = Some(parseHint())
        case "safety" => safety = Some(parseSafety(readString("def.safety")))
        case "all" => all = Some(readIntArray("def.all").map(requireName))
        case field => fail(s"unknown def field '$field'")
      }
      val n = required(name, "def.name")
      val group = required(all, "def.all")
      requireSelfInAll(n, group, "def")
      ExportDef(n, required(params, "def.levelParams"), required(tpe, "def.type"), required(value, "def.value"),
        required(hint, "def.hints"), required(safety, "def.safety"), group, declarationProvenance("def", n))
    }

    private def parseOpaque(): ExportDecl = {
      var name: Option[NameId] = None; var params: Option[Vector[NameId]] = None; var tpe: Option[ExprId] = None
      var value: Option[ExprId] = None; var unsafe: Option[Boolean] = None; var all: Option[Vector[NameId]] = None
      objectFields("opaque") {
        case "name" => name = Some(requireName(readNonNegativeInt("opaque.name")))
        case "levelParams" => params = Some(readIntArray("opaque.levelParams").map(requireName))
        case "type" => tpe = Some(requireExpr(readNonNegativeInt("opaque.type")))
        case "value" => value = Some(requireExpr(readNonNegativeInt("opaque.value")))
        case "isUnsafe" => unsafe = Some(readBoolean("opaque.isUnsafe"))
        case "all" => all = Some(readIntArray("opaque.all").map(requireName))
        case field => fail(s"unknown opaque field '$field'")
      }
      val n = required(name, "opaque.name"); val group = required(all, "opaque.all"); requireSelfInAll(n, group, "opaque")
      ExportOpaque(n, required(params, "opaque.levelParams"), required(tpe, "opaque.type"),
        required(value, "opaque.value"), required(unsafe, "opaque.isUnsafe"), group, declarationProvenance("opaque", n))
    }

    private def parseTheorem(): ExportDecl = {
      var name: Option[NameId] = None; var params: Option[Vector[NameId]] = None; var tpe: Option[ExprId] = None
      var value: Option[ExprId] = None; var all: Option[Vector[NameId]] = None
      objectFields("thm") {
        case "name" => name = Some(requireName(readNonNegativeInt("thm.name")))
        case "levelParams" => params = Some(readIntArray("thm.levelParams").map(requireName))
        case "type" => tpe = Some(requireExpr(readNonNegativeInt("thm.type")))
        case "value" => value = Some(requireExpr(readNonNegativeInt("thm.value")))
        case "all" => all = Some(readIntArray("thm.all").map(requireName))
        case field => fail(s"unknown thm field '$field'")
      }
      val n = required(name, "thm.name"); val group = required(all, "thm.all"); requireSelfInAll(n, group, "thm")
      ExportTheorem(n, required(params, "thm.levelParams"), required(tpe, "thm.type"),
        required(value, "thm.value"), group, declarationProvenance("thm", n))
    }

    private def parseQuot(): ExportDecl = {
      var name: Option[NameId] = None; var params: Option[Vector[NameId]] = None
      var tpe: Option[ExprId] = None; var kind: Option[ExportQuotKind] = None
      objectFields("quot") {
        case "name" => name = Some(requireName(readNonNegativeInt("quot.name")))
        case "levelParams" => params = Some(readIntArray("quot.levelParams").map(requireName))
        case "type" => tpe = Some(requireExpr(readNonNegativeInt("quot.type")))
        case "kind" => kind = Some(parseQuotKind(readString("quot.kind")))
        case field => fail(s"unknown quot field '$field'")
      }
      val n = required(name, "quot.name")
      ExportQuot(n, required(params, "quot.levelParams"), required(tpe, "quot.type"),
        required(kind, "quot.kind"), declarationProvenance("quot", n))
    }

    private def parseInductive(): ExportDecl = {
      var types: Option[Vector[ExportInductiveValue]] = None
      var ctors: Option[Vector[ExportConstructorValue]] = None
      var recs: Option[Vector[ExportRecursorValue]] = None
      objectFields("inductive") {
        case "types" => types = Some(readObjectArray("inductive.types")(parseInductiveValue()))
        case "ctors" => ctors = Some(readObjectArray("inductive.ctors")(parseConstructorValue()))
        case "recs" => recs = Some(readObjectArray("inductive.recs")(parseRecursorValue()))
        case field => fail(s"unknown inductive field '$field'")
      }
      val typeValues = required(types, "inductive.types")
      if (typeValues.isEmpty) fail("inductive block contains no types")
      val ctorValues = required(ctors, "inductive.ctors")
      val recValues = required(recs, "inductive.recs")
      val familyNames = typeValues.map(_.name)
      typeValues.foreach { value =>
        if (value.all != familyNames)
          fail(s"${tables.dottedName(value.name)}.all does not equal the inductive block's ordered family list")
        val actual = ctorValues.filter(_.inductive == value.name).sortBy(_.constructorIndex).map(_.name)
        if (value.ctors != actual)
          fail(s"${tables.dottedName(value.name)}.ctors does not agree with constructor ownership/order")
      }
      ctorValues.foreach { value =>
        if (!familyNames.contains(value.inductive))
          fail(s"constructor ${tables.dottedName(value.name)} names an owner outside its inductive block")
      }
      recValues.foreach { value =>
        if (value.all != familyNames)
          fail(s"${tables.dottedName(value.name)}.all does not equal the inductive block's ordered family list")
      }
      ExportInductive(typeValues, ctorValues, recValues,
        provenance("inductive", declaration = Some(tables.dottedName(typeValues.head.name))))
    }

    private def parseInductiveValue(): ExportInductiveValue = {
      var name: Option[NameId] = None; var params: Option[Vector[NameId]] = None; var tpe: Option[ExprId] = None
      var numParams: Option[Int] = None; var numIndices: Option[Int] = None; var all: Option[Vector[NameId]] = None
      var ctors: Option[Vector[NameId]] = None; var nested: Option[Int] = None; var rec: Option[Boolean] = None
      var unsafe: Option[Boolean] = None; var reflexive: Option[Boolean] = None
      objectFields("InductiveVal") {
        case "name" => name = Some(requireName(readNonNegativeInt("InductiveVal.name")))
        case "levelParams" => params = Some(readIntArray("InductiveVal.levelParams").map(requireName))
        case "type" => tpe = Some(requireExpr(readNonNegativeInt("InductiveVal.type")))
        case "numParams" => numParams = Some(readNonNegativeInt("InductiveVal.numParams"))
        case "numIndices" => numIndices = Some(readNonNegativeInt("InductiveVal.numIndices"))
        case "all" => all = Some(readIntArray("InductiveVal.all").map(requireName))
        case "ctors" => ctors = Some(readIntArray("InductiveVal.ctors").map(requireName))
        case "numNested" => nested = Some(readNonNegativeInt("InductiveVal.numNested"))
        case "isRec" => rec = Some(readBoolean("InductiveVal.isRec"))
        case "isUnsafe" => unsafe = Some(readBoolean("InductiveVal.isUnsafe"))
        case "isReflexive" => reflexive = Some(readBoolean("InductiveVal.isReflexive"))
        case field => fail(s"unknown InductiveVal field '$field'")
      }
      ExportInductiveValue(required(name,"InductiveVal.name"), required(params,"InductiveVal.levelParams"),
        required(tpe,"InductiveVal.type"), required(numParams,"InductiveVal.numParams"),
        required(numIndices,"InductiveVal.numIndices"), required(all,"InductiveVal.all"),
        required(ctors,"InductiveVal.ctors"), required(nested,"InductiveVal.numNested"),
        required(rec,"InductiveVal.isRec"), required(unsafe,"InductiveVal.isUnsafe"),
        required(reflexive,"InductiveVal.isReflexive"))
    }

    private def parseConstructorValue(): ExportConstructorValue = {
      var name: Option[NameId] = None; var params: Option[Vector[NameId]] = None; var tpe: Option[ExprId] = None
      var owner: Option[NameId] = None; var cidx: Option[Int] = None; var numParams: Option[Int] = None
      var numFields: Option[Int] = None; var unsafe: Option[Boolean] = None
      objectFields("ConstructorVal") {
        case "name" => name = Some(requireName(readNonNegativeInt("ConstructorVal.name")))
        case "levelParams" => params = Some(readIntArray("ConstructorVal.levelParams").map(requireName))
        case "type" => tpe = Some(requireExpr(readNonNegativeInt("ConstructorVal.type")))
        case "induct" | "inductive" => owner = Some(requireName(readNonNegativeInt("ConstructorVal.induct")))
        case "cidx" => cidx = Some(readNonNegativeInt("ConstructorVal.cidx"))
        case "numParams" => numParams = Some(readNonNegativeInt("ConstructorVal.numParams"))
        case "numFields" => numFields = Some(readNonNegativeInt("ConstructorVal.numFields"))
        case "isUnsafe" => unsafe = Some(readBoolean("ConstructorVal.isUnsafe"))
        case field => fail(s"unknown ConstructorVal field '$field'")
      }
      ExportConstructorValue(required(name,"ConstructorVal.name"), required(params,"ConstructorVal.levelParams"),
        required(tpe,"ConstructorVal.type"), required(owner,"ConstructorVal.induct"),
        required(cidx,"ConstructorVal.cidx"), required(numParams,"ConstructorVal.numParams"),
        required(numFields,"ConstructorVal.numFields"), required(unsafe,"ConstructorVal.isUnsafe"))
    }

    private def parseRecursorValue(): ExportRecursorValue = {
      var name: Option[NameId] = None; var params: Option[Vector[NameId]] = None; var tpe: Option[ExprId] = None
      var all: Option[Vector[NameId]] = None; var np: Option[Int] = None; var ni: Option[Int] = None
      var nm: Option[Int] = None; var nmin: Option[Int] = None; var rules: Option[Vector[ExportRecursorRule]] = None
      var k: Option[Boolean] = None; var unsafe: Option[Boolean] = None
      objectFields("RecursorVal") {
        case "name" => name = Some(requireName(readNonNegativeInt("RecursorVal.name")))
        case "levelParams" => params = Some(readIntArray("RecursorVal.levelParams").map(requireName))
        case "type" => tpe = Some(requireExpr(readNonNegativeInt("RecursorVal.type")))
        case "all" => all = Some(readIntArray("RecursorVal.all").map(requireName))
        case "numParams" => np = Some(readNonNegativeInt("RecursorVal.numParams"))
        case "numIndices" => ni = Some(readNonNegativeInt("RecursorVal.numIndices"))
        case "numMotives" => nm = Some(readNonNegativeInt("RecursorVal.numMotives"))
        case "numMinors" => nmin = Some(readNonNegativeInt("RecursorVal.numMinors"))
        case "rules" => rules = Some(readObjectArray("RecursorVal.rules")(parseRecursorRule()))
        case "k" => k = Some(readBoolean("RecursorVal.k"))
        case "isUnsafe" => unsafe = Some(readBoolean("RecursorVal.isUnsafe"))
        case field => fail(s"unknown RecursorVal field '$field'")
      }
      ExportRecursorValue(required(name,"RecursorVal.name"), required(params,"RecursorVal.levelParams"),
        required(tpe,"RecursorVal.type"), required(all,"RecursorVal.all"), required(np,"RecursorVal.numParams"),
        required(ni,"RecursorVal.numIndices"), required(nm,"RecursorVal.numMotives"),
        required(nmin,"RecursorVal.numMinors"), required(rules,"RecursorVal.rules"),
        required(k,"RecursorVal.k"), required(unsafe,"RecursorVal.isUnsafe"))
    }

    private def parseRecursorRule(): ExportRecursorRule = {
      var ctor: Option[NameId] = None; var fields: Option[Int] = None; var rhs: Option[ExprId] = None
      objectFields("RecursorRule") {
        case "ctor" => ctor = Some(requireName(readNonNegativeInt("RecursorRule.ctor")))
        case "nfields" => fields = Some(readNonNegativeInt("RecursorRule.nfields"))
        case "rhs" => rhs = Some(requireExpr(readNonNegativeInt("RecursorRule.rhs")))
        case field => fail(s"unknown RecursorRule field '$field'")
      }
      ExportRecursorRule(required(ctor,"RecursorRule.ctor"), required(fields,"RecursorRule.nfields"),
        required(rhs,"RecursorRule.rhs"))
    }

    private def registerDeclaration(decl: ExportDecl, kind: String): Unit = {
      val names: Vector[NameId] = decl match {
        case value: ExportAxiom => Vector(value.name)
        case value: ExportDef => Vector(value.name)
        case value: ExportOpaque => Vector(value.name)
        case value: ExportTheorem => Vector(value.name)
        case value: ExportQuot => Vector(value.name)
        case value: ExportInductive => value.types.map(_.name) ++ value.constructors.map(_.name) ++ value.recursors.map(_.name)
      }
      names.foreach { id =>
        val name = tables.dottedName(id)
        if (name.isEmpty) fail("a declaration cannot use the anonymous name")
        if (!declarationNames.add(tables.nameComponents(id))) fail(s"duplicate declaration '$name'")
      }
      declarationCount += names.length
      consumer.onDeclaration(decl, tables)
    }

    private def parseBinderInfo(value: String): BinderInfo = value match {
      case "default" => Default
      case "implicit" => Implicit
      case "strictImplicit" => StrictImplicit
      case "instImplicit" => InstImplicit
      case other => fail(s"unknown binderInfo '$other'")
    }

    private def parseSafety(value: String): ExportSafety = value match {
      case "safe" => Safe
      case "unsafe" => Unsafe
      case "partial" => Partial
      case other => fail(s"unknown definition safety '$other'")
    }

    private def parseHint(): ExportDefHint = parser.currentToken() match {
      case JsonToken.VALUE_STRING =>
        readString("def.hints") match {
          case "opaque" => HintOpaque
          case "abbrev" => HintAbbrev
          case other => fail(s"unknown definition hint '$other'")
        }
      case JsonToken.START_OBJECT =>
        var height: Option[BigInt] = None
        objectFields("def.hints") {
          case "regular" => height = Some(readNonNegativeBigInt("def.hints.regular"))
          case field => fail(s"unknown definition hint field '$field'")
        }
        HintRegular(required(height, "def.hints.regular"))
      case _ => fail("def.hints must be a string or regular-height object")
    }

    private def parseQuotKind(value: String): ExportQuotKind = value match {
      case "type" => QuotType
      case "ctor" => QuotCtor
      case "lift" => QuotLift
      case "ind" => QuotInd
      case other => fail(s"unknown quotient declaration kind '$other'")
    }

    private def declarationProvenance(kind: String, name: NameId): ExportProvenance =
      provenance(kind, declaration = Some(tables.dottedName(name)))

    private def requireSelfInAll(name: NameId, all: Vector[NameId], kind: String): Unit = {
      if (all.isEmpty) fail(s"$kind.all must be nonempty")
      if (!all.contains(name)) fail(s"$kind.all does not contain its declaration name")
    }

    private def objectFields(label: String)(consume: String => Unit): Unit = {
      expect(JsonToken.START_OBJECT)
      val seen = mutable.HashSet.empty[String]
      var token = parser.nextToken()
      while (token != JsonToken.END_OBJECT) {
        if (token == null) fail(s"unexpected end of input inside $label")
        expect(JsonToken.FIELD_NAME)
        val field = parser.currentName()
        if (!seen.add(field)) fail(s"duplicate field '$field' in $label")
        if (parser.nextToken() == null) fail(s"missing value for field '$field'")
        consume(field)
        token = parser.nextToken()
      }
    }

    private def readObjectArray[A](label: String)(readValue: => A): Vector[A] = {
      expect(JsonToken.START_ARRAY)
      val result = Vector.newBuilder[A]
      var token = parser.nextToken()
      while (token != JsonToken.END_ARRAY) {
        if (token == null) fail(s"unexpected end of input inside $label")
        expect(JsonToken.START_OBJECT)
        result += readValue
        token = parser.nextToken()
      }
      result.result()
    }

    private def readIntArray(label: String): Vector[Int] = {
      expect(JsonToken.START_ARRAY)
      val result = Vector.newBuilder[Int]
      var token = parser.nextToken()
      while (token != JsonToken.END_ARRAY) {
        if (token == null) fail(s"unexpected end of input inside $label")
        result += readNonNegativeInt(label)
        token = parser.nextToken()
      }
      result.result()
    }

    private def readFixedIntArray(size: Int, label: String): Vector[Int] = {
      val result = readIntArray(label)
      if (result.length != size) fail(s"$label must contain exactly $size integers")
      result
    }

    private def readNonNegativeInt(label: String): Int = {
      expect(JsonToken.VALUE_NUMBER_INT)
      val value = try BigInt(parser.getText) catch { case NonFatal(_) => fail(s"$label is not an integer") }
      if (value < 0) fail(s"$label must be non-negative")
      if (!value.isValidInt) throw IndexOverflow(provenance(label), s"$label is outside the 32-bit index range: $value")
      value.toInt
    }

    private def readNonNegativeBigInt(label: String): BigInt = {
      parser.currentToken() match {
        case JsonToken.VALUE_NUMBER_INT | JsonToken.VALUE_STRING =>
        case _ => fail(s"$label must be an integer or decimal string")
      }
      val value = try BigInt(parser.getText) catch { case NonFatal(_) => fail(s"$label is not a decimal integer") }
      if (value < 0) fail(s"$label must be non-negative")
      value
    }

    private def readString(label: String): String = { expect(JsonToken.VALUE_STRING); parser.getText }
    private def readBoolean(label: String): Boolean = parser.currentToken() match {
      case JsonToken.VALUE_TRUE => true
      case JsonToken.VALUE_FALSE => false
      case _ => fail(s"$label must be a boolean")
    }

    private def requireName(index: Int): NameId = {
      if (index >= tables.nameCount) throw MissingIntern(provenance("name", Some(index)), s"name reference $index has not been defined")
      NameId(index)
    }
    private def requireLevel(index: Int): LevelId = {
      if (index >= tables.levelCount) throw MissingIntern(provenance("level", Some(index)), s"level reference $index has not been defined")
      LevelId(index)
    }
    private def requireExpr(index: Int): ExprId = {
      if (index >= tables.expressionCount) throw MissingIntern(provenance("expression", Some(index)), s"expression reference $index has not been defined")
      ExprId(index)
    }
    private def requireNextIndex(kind: String, actual: Int, expected: Int): Unit =
      if (actual != expected) throw InternOrder(provenance(kind, Some(actual)), s"$kind index $actual is out of sequence; expected $expected")

    private def required[A](value: Option[A], field: String): A = value.getOrElse(fail(s"required field '$field' is missing"))
    private def expect(token: JsonToken): Unit =
      if (parser.currentToken() != token) fail(s"expected $token, found ${Option(parser.currentToken()).getOrElse("end of input")}")
    private def fail(message: String): Nothing = throw MalformedExport(provenance("parse"), message)
  }
}
