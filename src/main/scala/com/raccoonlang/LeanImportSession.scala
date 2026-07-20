package com.raccoonlang

import com.raccoonlang.CoreAst.{ConstBody, Decl}
import com.raccoonlang.LeanExportIr._

import java.io.InputStream
import scala.util.control.NonFatal

final case class LeanManifestEntry(name: String, kind: String, opaque: Boolean, provenance: ExportProvenance)
final case class LeanImportManifest(installed: Vector[LeanManifestEntry], skipped: Vector[LeanManifestEntry])
final case class LeanImportMetrics(objects: Long, declarations: Long, nodeStoreBytes: Long, nodeStoreHighWaterBytes: Long)
final case class LeanImportResult(env: Env, manifest: LeanImportManifest, metrics: LeanImportMetrics)

object LeanImportSession {
  def importStream(input: InputStream, source: String = "<input>"): Either[Vector[LeanImportDiagnostic], LeanImportResult] =
    LeanImportBootstrap.build().flatMap { bootstrap =>
      val session = new Session(bootstrap)
      try {
        val read = LeanExportReader.read(input, source, session)
        Right(LeanImportResult(session.env, LeanImportManifest(session.installed, session.skipped),
          LeanImportMetrics(read.objects, read.declarations, read.tables.currentBytes, read.tables.highWaterBytes)))
      } catch {
        case diagnostic: LeanImportDiagnostic => Left(Vector(diagnostic))
        case NonFatal(error) =>
          val provenance = ExportProvenance(java.nio.file.Paths.get(source), 0L, 0, 0L, "import", None, None)
          Left(Vector(DeclarationTypeError(provenance, Option(error.getMessage).getOrElse(error.toString))))
      }
    }

  private final class Session(private var currentEnv: Env) extends LeanExportConsumer {
    private var registry = LeanGlobalRegistry.empty
    private var installed0 = Vector.empty[LeanManifestEntry]
    private var skipped0 = Vector.empty[LeanManifestEntry]

    def env: Env = currentEnv
    def installed: Vector[LeanManifestEntry] = installed0
    def skipped: Vector[LeanManifestEntry] = skipped0

    override def onMeta(meta: ExportMeta): Unit = ()
    override def finish(tables: ExportTables): Unit = ()

    override def onDeclaration(decl: ExportDecl, tables: ExportTables): Unit = decl match {
      case value: ExportAxiom if !value.isUnsafe =>
        publish(value.name, value.levelParams, value.provenance, "axiom", opaque = true, tables) { (name, lowerer) =>
          val lowered = lowerer.lowerDeclarationType(value.levelParams, value.tpe)
          Decl.AxiomDecl(name, lowered.term, coreSpan(value.provenance))
        }
      case value: ExportDef if value.safety == Safe =>
        publish(value.name, value.levelParams, value.provenance, "def", value.hint == HintOpaque, tables) { (name, lowerer) =>
          val lowered = lowerer.lowerDeclarationType(value.levelParams, value.tpe)
          val body = lowerer.lowerDeclarationBody(value.value, lowered, name)
          Decl.ConstDecl(value.hint == HintOpaque, name, lowered.term, ConstBody.TermBody(body), coreSpan(value.provenance))
        }
      case value: ExportTheorem =>
        publish(value.name, value.levelParams, value.provenance, "theorem", opaque = true, tables) { (name, lowerer) =>
          val lowered = lowerer.lowerDeclarationType(value.levelParams, value.tpe)
          val body = lowerer.lowerDeclarationBody(value.value, lowered, name)
          Decl.ConstDecl(isOpaque = true, name, lowered.term, ConstBody.TermBody(body), coreSpan(value.provenance))
        }
      case value: ExportAxiom => unsupported(value.name, value.provenance, tables, "unsafe filtering requires T1.4")
      case value: ExportDef => unsupported(value.name, value.provenance, tables, "unsafe/partial filtering requires T1.4")
      case value: ExportOpaque => unsupported(value.name, value.provenance, tables, "opaque declarations require T1.4")
      case value: ExportQuot => unsupported(value.name, value.provenance, tables, "quotient declarations require T1.5")
      case value: ExportInductive =>
        throw UnsupportedFeature(value.provenance, "inductive blocks require T1.5/K6/T2", value.provenance.declaration)
    }

    private def publish(
        sourceName: NameId,
        levelParams: Vector[NameId],
        provenance: ExportProvenance,
        kind: String,
        opaque: Boolean,
        tables: ExportTables
    )(build: (String, LeanTermLowerer) => Decl): Unit = {
      val name = LeanExportNames.encode(sourceName, tables)
      if (name.isEmpty) throw TypeLowering(provenance, "anonymous declaration name", Some(name))
      val lowerer = new LeanTermLowerer(tables, currentEnv, registry, name)
      try {
        val next = Interpreter.evalDecl(build(name, lowerer), currentEnv)
        val global = ImportedGlobal(sourceName, name, provenance, Installed, levelParams)
        currentEnv = next
        registry = registry.add(global, tables)
        installed0 :+= LeanManifestEntry(name, kind, opaque, provenance)
      } catch {
        case diagnostic: LeanImportDiagnostic => throw diagnostic
        case error: TypeError => throw DeclarationTypeError(provenance, error.getMessage, Some(name))
      }
    }

    private def unsupported(name: NameId, provenance: ExportProvenance, tables: ExportTables, reason: String): Nothing =
      throw UnsupportedFeature(provenance, reason, Some(LeanExportNames.encode(name, tables)))

    private def coreSpan(provenance: ExportProvenance): Span =
      Span(0, 1, Some(SourceId.fresh()))
  }
}
