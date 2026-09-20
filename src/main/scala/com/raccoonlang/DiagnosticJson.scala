package com.raccoonlang

/**
 * Diagnostics as a JSON array for tools. Positions match the text report; `kind` is the error class name. Hand-written:
 * the shape is too small to justify a dependency.
 */
object DiagnosticJson {

  /** A clean run still prints `[]`, so a tool can tell "nothing wrong" from "no output". */
  def render(diagnostics: Vector[Diagnostic], sources: Vector[ModuleLoader.LoadedSource]): String =
    if (diagnostics.isEmpty) "[]"
    else diagnostics.map(one(_, sources)).mkString("[\n", ",\n", "\n]")

  private def one(diagnostic: Diagnostic, sources: Vector[ModuleLoader.LoadedSource]): String = {
    val span = diagnostic.span.getOrElse(Span(0, 0))
    val fields = Vector.newBuilder[String]
    ErrorReporter.sourceFor(span, sources).foreach { source =>
      val at = ErrorReporter.positionIn(ErrorReporter.Source(source.source), span)
      fields += field("path", string(source.path.toString))
      fields += field("startLine", at.line.toString)
      fields += field("startColumn", at.column.toString)
      fields += field("endLine", at.endLine.toString)
      fields += field("endColumn", at.endColumn.toString)
    }
    fields += field("severity", string("error"))
    fields += field("kind", string(diagnostic.error.getClass.getSimpleName))
    fields += field("message", string(diagnostic.getMessage))
    fields += field(
      "notes",
      diagnostic.frames.map(frame => string(s"in ${ErrorReporter.renderFrame(frame)}")).mkString("[", ", ", "]")
    )
    fields.result().mkString("  {", ", ", "}")
  }

  private def field(name: String, value: String): String = s"${string(name)}: $value"

  /** JSON string escaping: the two mandatory escapes, the named control characters, and \\u for the rest. */
  private def string(value: String): String = {
    val out = new StringBuilder(value.length + 2)
    out += '"'
    value.foreach {
      case '"'                   => out ++= "\\\""
      case '\\'                  => out ++= "\\\\"
      case '\n'                  => out ++= "\\n"
      case '\r'                  => out ++= "\\r"
      case '\t'                  => out ++= "\\t"
      case '\b'                  => out ++= "\\b"
      case '\f'                  => out ++= "\\f"
      case ch if ch.toInt < 0x20 => out ++= f"\\u${ch.toInt}%04x"
      case ch                    => out += ch
    }
    out += '"'
    out.result()
  }
}
