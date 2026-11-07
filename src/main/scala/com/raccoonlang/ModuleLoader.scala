package com.raccoonlang

import com.raccoonlang.{SurfaceAst => SA}

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, NoSuchFileException, Path}
import java.security.MessageDigest
import scala.collection.mutable
import scala.util.control.NonFatal

/**
 * Reads modules and links their imports (docs/namespaces.md, "Imports"). `Sources` keeps the files read, `Snapshot`
 * reads each at most once for one run, and a `Loader` links an entry's imports over its source roots into `Module`s.
 */
object ModuleLoader {
  final case class LoadedSource(sourceId: SourceId, path: Path, source: String)

  /**
   * One version of a module file: its source, under a `SourceId` of its own, the source's digest, and its parse, or the
   * parse error, located in it.
   */
  final class ModuleFile private[ModuleLoader] (
      val source: LoadedSource,
      val digest: String,
      val parsed: Either[ModuleParseError, SA.Program]
  ) {
    def path: Path = source.path
  }

  /**
   * The module files read so far, the latest version of each by canonical path. A file is parsed once per version: one
   * whose source is unchanged keeps its version, whose spans and `SourceId` results computed from it carry. Source ids
   * are distinct across the process.
   */
  final class Sources {
    private var nextSourceId = 0
    private val latest = mutable.HashMap.empty[Path, ModuleFile]

    /** A view of the files in which each is read at most once, so one run sees one version of each. */
    def snapshot(): Snapshot = new Snapshot(this)

    private[ModuleLoader] def version(path: Path, source: String): ModuleFile = {
      val digest = sha256(source)
      latest.get(path) match {
        case Some(file) if file.digest == digest => file
        case _ =>
          val sourceId = SourceId(nextSourceId)
          nextSourceId += 1
          val parsed = LanguageParser.parseProgram(source, sourceId) match {
            case Success(program, _, _) => Right(program)
            case Failure(_, curIdx, message) =>
              Left(ModuleParseError(path, message, curIdx, Some(Span(curIdx, curIdx, Some(sourceId)))))
          }
          val file = new ModuleFile(LoadedSource(sourceId, path, source), digest, parsed)
          latest(path) = file
          file
      }
    }
  }

  /** The files of one run, each read when first asked for: one that cannot be read stays unread for the run. */
  final class Snapshot private[ModuleLoader] (sources: Sources) {
    private val read = mutable.LinkedHashMap.empty[Path, Either[String, ModuleFile]]

    /** The file at `path`, a canonical path; one that cannot be read is `ModuleReadFailed` at `span`. */
    private[ModuleLoader] def file(path: Path, span: Option[Span]): ModuleFile =
      read
        .getOrElseUpdate(
          path,
          try Right(sources.version(path, Files.readString(path)))
          catch { case NonFatal(e) => Left(reason(e)) }
        )
        .fold(why => throw ModuleReadFailed(path, why, span), identity)

    /** Every file this run has read, in the order it first read them. */
    private[ModuleLoader] def files: Iterator[ModuleFile] = read.valuesIterator.flatMap(_.toOption)
  }

  /**
   * A loaded module: its file, its parse, and the modules it imports, each loaded, in its import order. An import the
   * prelude stands for is no module.
   */
  final class Module private[ModuleLoader] (val file: ModuleFile, val program: SA.Program, val imports: Vector[Module]) {
    def path: Path = file.path

    /**
     * The modules this one imports, directly or not, each once, in depth-first import order: for each import in turn,
     * the import's own closure, then the import, less the modules already listed. So for the first import `i`,
     * `i.closure :+ i` is a prefix of this closure, and a module's closure in this order is what a standalone check of it
     * assembles.
     */
    lazy val closure: Vector[Module] = {
      val listed = mutable.HashSet.empty[Module]
      val order = Vector.newBuilder[Module]
      imports.foreach(imported => (imported.closure :+ imported).foreach(module => if (listed.add(module)) order += module))
      order.result()
    }

    /**
     * What a check of this module depends on: its canonical path, its source, and its imports' keys, in order; the
     * caller's configuration is not in it. The source is its version, by digest and by `SourceId`, which the spans of
     * results computed from it carry: a source changed and changed back is a new version, whose results locate errors
     * in it.
     */
    lazy val key: String =
      sha256((path.toString +: file.digest +: file.source.sourceId.value.toString +: imports.map(_.key)).mkString("\u0000"))
  }

  /**
   * An entry that failed to load: the first error a depth-first load from it meets, with the sources it may be located
   * in, the entry's first, unless the entry itself could not be read.
   */
  final case class LoadFailure(error: TypeError, sources: Vector[LoadedSource])
    extends RuntimeException(error.getMessage)

  /**
   * Loads entries over `sourceRoots`, which are absolute and normalized, from the files of `snapshot`; the imports
   * `prelude` stands for are not loaded. A module loads once: one whose imports all loaded is linked once, and every
   * entry that reaches it shares it. Its imports cannot fail to load for a later entry: they read the same files, and an
   * import cycle through it would run through its own imports.
   */
  final class Loader(sourceRoots: Vector[Path], prelude: Prelude.Config, snapshot: Snapshot) {
    private val loaded = mutable.HashMap.empty[Path, Module]

    /**
     * The entry at `entry`, written `shown`, loaded depth first: its file, then for each import in order, the imported
     * module's, until a module fails, as `LoadFailure`. An imported module may not have a body; the entry may.
     */
    def load(entry: Path, shown: String): Module = {
      val absolute = entry.toAbsolutePath.normalize
      val canonical =
        try absolute.toRealPath()
        catch {
          case _: NoSuchFileException => throw LoadFailure(ModuleNotFound(shown, Vector(absolute), None), Vector.empty)
          case NonFatal(e) => throw LoadFailure(ModuleReadFailed(absolute, reason(e), None), Vector.empty)
        }
      try visit(canonical, None, isEntry = true, Vector.empty)
      catch {
        // Located in the entry's sources, its own first, as `ErrorReporter` falls back to it, if it was read.
        case error: TypeError =>
          val (own, others) = snapshot.files.toVector.partition(_.path == canonical)
          throw LoadFailure(error, if (own.isEmpty) Vector.empty else (own ++ others).map(_.source))
      }
    }

    /** The module at `path`, imported at `importSpan` along `visiting`, loaded; a failure is its `TypeError`. */
    private def visit(path: Path, importSpan: Option[Span], isEntry: Boolean, visiting: Vector[Path]): Module = {
      visiting.indexOf(path) match {
        case -1  =>
        case idx => throw CyclicImport(visiting.drop(idx) :+ path, importSpan)
      }
      def rejectBody(program: SA.Program): Unit =
        if (!isEntry) program.body.foreach(body => throw ImportedModuleHasBody(path, Some(body.span)))

      loaded.get(path) match {
        case Some(module) =>
          rejectBody(module.program)
          module
        case None =>
          val file = snapshot.file(path, importSpan)
          val program = file.parsed.fold(throw _, identity)
          rejectBody(program)
          val imports = program.imports.filterNot(imp => prelude.ignoresImport(imp.path)).map { imp =>
            visit(resolveImport(imp), Some(imp.span), isEntry = false, visiting :+ path)
          }
          val module = new Module(file, program, imports)
          loaded(path) = module
          module
      }
    }

    private def resolveImport(imp: SA.Import): Path = {
      val relative =
        imp.path.zipWithIndex.foldLeft(sourceRoots.head.getFileSystem.getPath("")) { case (cur, (part, idx)) =>
          val name = if (idx == imp.path.length - 1) s"$part.rac" else part
          cur.resolve(name)
        }
      val candidates = sourceRoots.map(root => root.resolve(relative).normalize)
      candidates
        .find(Files.isRegularFile(_))
        .map(_.toRealPath())
        .getOrElse(throw ModuleNotFound(imp.path.mkString("."), candidates, Some(imp.span)))
    }
  }

  private def reason(e: Throwable): String = Option(e.getMessage).getOrElse(e.toString)

  /** The SHA-256 digest of `text`'s UTF-8 encoding, in hexadecimal. */
  private[raccoonlang] def sha256(text: String): String =
    MessageDigest
      .getInstance("SHA-256")
      .digest(text.getBytes(StandardCharsets.UTF_8))
      .map(byte => f"${byte & 0xff}%02x")
      .mkString
}
