package com.raccoonlang

import com.raccoonlang.CoreAst.{ConstBody, Decl}
import com.raccoonlang.LeanExportIr._

import java.io.InputStream
import scala.util.control.NonFatal

final case class LeanManifestEntry(
    name: String,
    kind: String,
    opaque: Boolean,
    provenance: ExportProvenance,
    callingConvention: Option[ImportedCallingConvention],
    hint: Option[ExportDefHint] = None,
    safety: Option[ExportSafety] = None
)
final case class LeanImportManifest(installed: Vector[LeanManifestEntry], skipped: Vector[LeanManifestEntry])
final case class LeanImportMetrics(
    objects: Long,
    declarations: Long,
    nodeStoreBytes: Long,
    nodeStoreHighWaterBytes: Long,
    requestedImplicits: Long,
    retainedImplicits: Long,
    demotedImplicits: Long,
    transparentGlobals: Long,
    opaqueGlobals: Long
)
final case class LeanImportResult(env: Env, manifest: LeanImportManifest, metrics: LeanImportMetrics)

object LeanImportSession {
  def importStream(
      input: InputStream,
      source: String = "<input>"
  ): Either[Vector[LeanImportDiagnostic], LeanImportResult] =
    LeanImportBootstrap.build().flatMap { bootstrap =>
      val session = new Session(bootstrap)
      try {
        val read = LeanExportReader.read(input, source, session)
        val installed = session.installed
        val binders = installed.flatMap(_.callingConvention.toVector.flatMap(_.telescopes).flatMap(_.binders))
        Right(
          LeanImportResult(
            session.env,
            LeanImportManifest(installed, session.skipped),
            LeanImportMetrics(
              read.objects,
              read.declarations,
              read.tables.currentBytes,
              read.tables.highWaterBytes,
              binders.count(_.requestedImplicit),
              binders.count(_.checkedImplicit),
              binders.count(b => b.requestedImplicit && !b.checkedImplicit),
              installed.count(!_.opaque),
              installed.count(_.opaque)
            )
          )
        )
      } catch {
        case diagnostic: LeanImportDiagnostic => Left(Vector(diagnostic))
        case _: StackOverflowError =>
          val provenance = importProvenance(source)
          Left(Vector(DeclarationTypeError(provenance, "export nesting exceeds the supported depth")))
        case NonFatal(error) =>
          val provenance = importProvenance(source)
          Left(Vector(DeclarationTypeError(provenance, bounded(Option(error.getMessage).getOrElse(error.toString)))))
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

    override def onDeclaration(decl: ExportDecl, tables: ExportTables): Unit =
      try handleDeclaration(decl, tables)
      catch {
        case diagnostic: LeanImportDiagnostic => throw diagnostic
        case _: StackOverflowError =>
          throw DeclarationTypeError(
            decl.provenance,
            "export nesting exceeds the supported depth",
            decl.provenance.declaration
          )
        case NonFatal(error) =>
          throw DeclarationTypeError(
            decl.provenance,
            bounded(Option(error.getMessage).getOrElse(error.toString)),
            decl.provenance.declaration
          )
      }

    private def handleDeclaration(decl: ExportDecl, tables: ExportTables): Unit = decl match {
      case value: ExportAxiom if !value.isUnsafe =>
        val coreName = LeanExportNames.encode(value.name, tables)
        if (coreName == "propext" || coreName == "Classical.choice")
          throw MissingKernelGate(value.provenance, s"$coreName requires K7", Some(coreName))
        publish(value.name, value.levelParams, value.provenance, "axiom", opaque = true, tables, safety = Some(Safe)) {
          (name, lowerer) =>
            val lowered = lowerer.lowerDeclarationType(value.levelParams, value.tpe)
            Decl.AxiomDecl(name, lowered.term, coreSpan(value.provenance)) -> lowered.convention
        }
      case value: ExportDef if value.safety == Safe =>
        publish(
          value.name,
          value.levelParams,
          value.provenance,
          "def",
          value.hint == HintOpaque,
          tables,
          hint = Some(value.hint),
          safety = Some(value.safety)
        ) { (name, lowerer) =>
          val lowered = lowerer.lowerDeclarationType(value.levelParams, value.tpe)
          val body = lowerer.lowerDeclarationBody(value.value, lowered, name)
          Decl.ConstDecl(
            value.hint == HintOpaque,
            name,
            lowered.term,
            ConstBody.TermBody(body),
            coreSpan(value.provenance)
          ) ->
            lowered.convention
        }
      case value: ExportTheorem =>
        publish(
          value.name,
          value.levelParams,
          value.provenance,
          "theorem",
          opaque = true,
          tables,
          safety = Some(Safe)
        ) { (name, lowerer) =>
          val lowered = lowerer.lowerDeclarationType(value.levelParams, value.tpe)
          val body = lowerer.lowerDeclarationBody(value.value, lowered, name)
          Decl.ConstDecl(isOpaque = true, name, lowered.term, ConstBody.TermBody(body), coreSpan(value.provenance)) ->
            lowered.convention
        }
      case value: ExportOpaque if !value.isUnsafe =>
        publish(value.name, value.levelParams, value.provenance, "opaque", opaque = true, tables, safety = Some(Safe)) {
          (name, lowerer) =>
            val lowered = lowerer.lowerDeclarationType(value.levelParams, value.tpe)
            val body = lowerer.lowerDeclarationBody(value.value, lowered, name)
            Decl.ConstDecl(isOpaque = true, name, lowered.term, ConstBody.TermBody(body), coreSpan(value.provenance)) ->
              lowered.convention
        }
      case value: ExportAxiom  => skip(value.name, value.levelParams, value.provenance, "axiom", tables, Unsafe)
      case value: ExportDef    => skip(value.name, value.levelParams, value.provenance, "def", tables, value.safety)
      case value: ExportOpaque => skip(value.name, value.levelParams, value.provenance, "opaque", tables, Unsafe)
      case value: ExportQuot => unsupported(value.name, value.provenance, tables, "quotient declarations require T1.5")
      case value: ExportInductive =>
        val flags = value.types.map(_.isUnsafe) ++ value.constructors.map(_.isUnsafe) ++ value.recursors.map(_.isUnsafe)
        if (flags.distinct.length > 1)
          throw MalformedExport(
            value.provenance,
            "inductive block mixes safe and unsafe member flags",
            value.provenance.declaration
          )
        if (flags.headOption.contains(true)) {
          value.types.foreach(v => skip(v.name, v.levelParams, value.provenance, "inductive", tables, Unsafe))
          value.constructors.foreach(v => skip(v.name, v.levelParams, value.provenance, "constructor", tables, Unsafe))
          value.recursors.foreach(v => skip(v.name, v.levelParams, value.provenance, "recursor", tables, Unsafe))
        } else
          throw UnsupportedFeature(
            value.provenance,
            "inductive blocks require T1.5/K6/T2",
            value.provenance.declaration
          )
    }

    private def publish(
        sourceName: NameId,
        levelParams: Vector[NameId],
        provenance: ExportProvenance,
        kind: String,
        opaque: Boolean,
        tables: ExportTables,
        hint: Option[ExportDefHint] = None,
        safety: Option[ExportSafety] = None
    )(build: (String, LeanTermLowerer) => (Decl, Option[ImportedCallingConvention])): Unit = {
      val name = LeanExportNames.encode(sourceName, tables)
      validateNameAvailability(name, provenance)
      val lowerer = new LeanTermLowerer(tables, currentEnv, registry, name)
      try {
        val (decl, convention) = build(name, lowerer)
        val next = Interpreter.evalDecl(decl, currentEnv)
        val global = ImportedGlobal(sourceName, name, provenance, Installed, levelParams, convention)
        val nextRegistry = registry.add(global, tables)
        val nextEntry = LeanManifestEntry(name, kind, opaque, provenance, convention, hint, safety)
        currentEnv = next
        registry = nextRegistry
        installed0 :+= nextEntry
      } catch {
        case diagnostic: LeanImportDiagnostic => throw diagnostic
        case error: TypeError => throw DeclarationTypeError(provenance, bounded(error.getMessage), Some(name))
      }
    }

    private def skip(
        sourceName: NameId,
        levelParams: Vector[NameId],
        provenance: ExportProvenance,
        kind: String,
        tables: ExportTables,
        safety: ExportSafety
    ): Unit = {
      val name = LeanExportNames.encode(sourceName, tables)
      validateNameAvailability(name, provenance)
      val global = ImportedGlobal(sourceName, name, provenance, SkippedUnsafe, levelParams)
      val nextRegistry = registry.add(global, tables)
      val entry = LeanManifestEntry(name, kind, opaque = true, provenance, None, None, Some(safety))
      registry = nextRegistry
      skipped0 :+= entry
    }

    private def validateNameAvailability(name: String, provenance: ExportProvenance): Unit = {
      if (name.isEmpty) throw TypeLowering(provenance, "anonymous declaration name", Some(name))
      if (ReservedNames.all(name))
        throw ReservedNameViolation(provenance, s"$name is reserved for authenticated kernel installation", Some(name))
      if (currentEnv.globals.contains(name))
        throw ReservedNameViolation(provenance, s"$name collides with an existing bootstrap global", Some(name))
    }

    private def unsupported(name: NameId, provenance: ExportProvenance, tables: ExportTables, reason: String): Nothing =
      throw UnsupportedFeature(provenance, reason, Some(LeanExportNames.encode(name, tables)))

    private def coreSpan(provenance: ExportProvenance): Span =
      Span(0, 1, Some(SourceId.fresh()))
  }

  private def bounded(message: String): String = {
    val rendered = Option(message).getOrElse("type checking failed")
    if (rendered.length <= 4096) rendered else rendered.take(4093) + "..."
  }

  private def importProvenance(source: String): ExportProvenance =
    ExportProvenance(java.nio.file.Paths.get(source), 0L, 0, 0L, "import", None, None)
}
