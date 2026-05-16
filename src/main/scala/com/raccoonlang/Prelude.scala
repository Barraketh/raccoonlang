package com.raccoonlang

import java.nio.charset.StandardCharsets

object Prelude {
  private val ResourcePath = "/Init/Prelude.rac"
  private val ImportPath = Vector("Init", "Prelude")

  def isPreludeImport(path: Vector[String]): Boolean =
    path == ImportPath

  lazy val surface: SurfaceAst.Program =
    LanguageParser.parseProgram(source) match {
      case Success(program, _, _) => program
      case Failure(_, _, message) => throw new RuntimeException(s"Failed to parse $ResourcePath: $message")
    }

  lazy val core: CoreAst.Program =
    Elaborator.elabWithoutPrelude(surface)

  private lazy val source: String = {
    val stream =
      Option(getClass.getResourceAsStream(ResourcePath))
        .getOrElse(throw new RuntimeException(s"Missing bundled resource $ResourcePath"))
    try new String(stream.readAllBytes(), StandardCharsets.UTF_8)
    finally stream.close()
  }
}
