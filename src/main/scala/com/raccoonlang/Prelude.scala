package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Files, Path}
import scala.util.control.NonFatal

object Prelude {
  private val DefaultResourcePath = "/Init/Prelude.rac"
  private val TestResourcePath = "/Init/TestPrelude.rac"
  val ImportPath: Vector[String] = Vector("Init", "Prelude")

  final case class Config(
      surface: SurfaceAst.Program,
      core: CoreAst.Program,
      ignoredImports: Set[Vector[String]]
  ) {
    def ignoresImport(path: Vector[String]): Boolean =
      ignoredImports(path)
  }

  lazy val default: Config =
    fromResource(DefaultResourcePath, ignoredImports = Set(ImportPath))

  lazy val test: Config =
    fromResource(TestResourcePath, ignoredImports = Set(ImportPath))

  val none: Config =
    Config(
      surface = SurfaceAst.Program(Vector.empty, Vector.empty, None),
      core = CoreAst.Program(Vector.empty, None),
      ignoredImports = Set.empty
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
    fromSource(canonical.toString, source, ignoredImports = Set(ImportPath))
  }

  def fromSource(sourceName: String, source: String, ignoredImports: Set[Vector[String]] = Set(ImportPath)): Config = {
    val surface =
      LanguageParser.parseProgram(source) match {
        case Success(program, _, _) => program
        case Failure(_, _, message) => throw new RuntimeException(s"Failed to parse $sourceName: $message")
      }
    Config(surface, Elaborator.elabWithoutPrelude(surface), ignoredImports)
  }

  private def fromResource(resourcePath: String, ignoredImports: Set[Vector[String]]): Config =
    fromSource(resourcePath, resourceSource(resourcePath), ignoredImports)

  private def resourceSource(resourcePath: String): String = {
    val stream =
      Option(getClass.getResourceAsStream(resourcePath))
        .getOrElse(throw new RuntimeException(s"Missing bundled resource $resourcePath"))
    try new String(stream.readAllBytes(), StandardCharsets.UTF_8)
    finally stream.close()
  }
}
