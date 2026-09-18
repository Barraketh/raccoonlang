package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.util.control.NonFatal

/** Bundled, checked source prelude and the explicit bootstrap selection boundary. */
object Prelude {
  private val DefaultResourcePath = "/Init/Prelude.rac"
  private val TestResourcePath = "/Init/TestPrelude.rac"
  val ImportPath: Vector[String] = Vector("Init", "Prelude")

  /** A selected prelude is trusted by construction; its declarations are checked exactly once. */
  final case class Config(
      surface: SurfaceAst.Program,
      core: CoreAst.Program,
      ignoredImports: Set[Vector[String]]
  ) {
    def ignoresImport(path: Vector[String]): Boolean = ignoredImports(path)

    /** Immutable checked environment shared by all programs using this configuration. */
    lazy val checkedEnv: Env =
      if (core.decls.isEmpty) Interpreter.buildEmptyPreludeEnv(core) else Interpreter.buildPreludeEnv(core)

    /** Resolved names from this selected prelude, shared by elaboration of all programs using it. */
    lazy val names: Elaborator.PreludeNames = Elaborator.preludeNames(this)
  }

  lazy val default: Config = fromResource(DefaultResourcePath, Set(ImportPath))
  lazy val test: Config = fromResource(TestResourcePath, Set(ImportPath))

  /** Empty source configuration: kernel primitives remain available, but no source prelude names are admitted. */
  val none: Config = Config(
    SurfaceAst.Program(Vector.empty, Vector.empty, None),
    CoreAst.Program(Vector.empty, None),
    Set.empty
  )

  def fromPath(path: Path): Config = {
    val canonical = path.toAbsolutePath.normalize
    val source =
      try Files.readString(canonical)
      catch {
        case NonFatal(e) =>
          throw new RuntimeException(
            s"Failed to read prelude ${canonical.toString}: ${Option(e.getMessage).getOrElse(e.toString)}",
            e
          )
      }
    fromSource(canonical.toString, source)
  }

  def fromSource(
      sourceName: String,
      source: String,
      ignoredImports: Set[Vector[String]] = Set(ImportPath)
  ): Config = {
    val surface = LanguageParser.parseProgram(source) match {
      case Success(program, _, _) => program
      case Failure(_, offset, message) =>
        throw new RuntimeException(s"Failed to parse $sourceName at offset $offset: $message")
    }
    Config(surface, Elaborator.elabWithoutPrelude(surface), ignoredImports)
  }

  private def fromResource(path: String, ignoredImports: Set[Vector[String]]): Config =
    fromSource(path, resourceSource(path), ignoredImports)

  private def resourceSource(path: String): String = {
    val stream = Option(getClass.getResourceAsStream(path))
      .getOrElse(throw new RuntimeException(s"Missing bundled resource $path"))
    try new String(stream.readAllBytes(), StandardCharsets.UTF_8)
    finally stream.close()
  }
}
