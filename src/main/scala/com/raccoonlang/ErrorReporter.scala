package com.raccoonlang

/**
 * Renders diagnostics as text. Positions are 1-based `file:line:column`; the underline covers the span, clamped to its
 * first line.
 */
object ErrorReporter {

  case class Line(start: Int, end: Int, lineNum: Int)

  /** A source text indexed by line; `lineNum` is a 0-based index. */
  case class Source(s: String) {
    private val lineStarts: IndexedSeq[Int] =
      0 +: s.zipWithIndex.collect { case ('\n', idx) => idx + 1 }.filter(_ <= s.length)

    val lines: IndexedSeq[Line] =
      lineStarts.zipWithIndex.map { case (start, lineNum) =>
        val nextStart = if (lineNum + 1 < lineStarts.length) lineStarts(lineNum + 1) else s.length + 1
        Line(start, math.min(nextStart - 1, s.length), lineNum)
      }

    def getLine(offset: Int): Line = {
      val clamped = math.max(0, math.min(offset, s.length))
      lines.findLast(_.start <= clamped).getOrElse(Line(0, s.length, 0))
    }
  }

  /** Where a diagnostic points, resolved against one source text: 1-based line and column, and the span's extent. */
  final case class Position(line: Int, column: Int, endLine: Int, endColumn: Int)

  private[raccoonlang] def positionIn(source: Source, span: Span): Position = {
    val start = math.max(0, math.min(span.start, source.s.length))
    val end = math.max(start, math.min(span.end, source.s.length))
    val startLine = source.getLine(start)
    val endLine = source.getLine(end)
    Position(
      line = startLine.lineNum + 1,
      column = start - startLine.start + 1,
      endLine = endLine.lineNum + 1,
      endColumn = end - endLine.start + 1
    )
  }

  /** The source a span names, or the first one loaded when it names none — a report still has to quote something. */
  private[raccoonlang] def sourceFor(
      span: Span,
      sources: Vector[ModuleLoader.LoadedSource]
  ): Option[ModuleLoader.LoadedSource] =
    span.source.flatMap(sourceId => sources.find(_.sourceId == sourceId)).orElse(sources.headOption)

  def pretty(diagnostic: Diagnostic, source: Source): String =
    render(diagnostic, path = None, source)

  def pretty(diagnostic: Diagnostic, loaded: ModuleLoader.LoadedProgram): String =
    pretty(diagnostic, loaded.sources)

  def pretty(diagnostic: Diagnostic, sources: Vector[ModuleLoader.LoadedSource]): String =
    sourceFor(diagnostic.span.getOrElse(Span(0, 0)), sources) match {
      case Some(loadedSource) =>
        render(diagnostic, Some(loadedSource.path.toString), Source(loadedSource.source))
      case None => diagnostic.getMessage
    }

  /** Every diagnostic of a run, in order. Each report already starts and ends with a blank line. */
  def pretty(diagnostics: Vector[Diagnostic], sources: Vector[ModuleLoader.LoadedSource]): String =
    diagnostics.map(pretty(_, sources)).mkString

  /** A kernel bug is not a diagnostic about the program: no excerpt, no "error:". */
  def pretty(internal: InternalError, sources: Vector[ModuleLoader.LoadedSource]): String = {
    val where =
      for {
        span <- internal.span
        loadedSource <- span.source.flatMap(sourceId => sources.find(_.sourceId == sourceId))
      } yield {
        val pos = positionIn(Source(loadedSource.source), span)
        s" while processing ${loadedSource.path.toString}:${pos.line}"
      }
    s"${internal.getMessage}${where.getOrElse("")}\nThis is a bug in the Raccoon kernel, not in the program."
  }

  /** Headline, source line, underline (at least one column; tabs preserved for alignment), detail, notes. */
  private def render(diagnostic: Diagnostic, path: Option[String], source: Source): String = {
    val span = diagnostic.span.getOrElse(Span(0, 0))
    val pos = positionIn(source, span)
    val line = source.getLine(math.max(0, math.min(span.start, source.s.length)))
    val text = source.s.slice(line.start, line.end)
    val startColumn = pos.column - 1
    val endColumn = if (pos.endLine == pos.line) pos.endColumn - 1 else text.length
    val width = math.max(1, endColumn - startColumn)
    val indent = text.take(startColumn).map(ch => if (ch == '\t') '\t' else ' ')
    val where = path.fold("")(p => s"$p:")
    // A message's first line is its headline; any detail follows the source excerpt it is about.
    val (headline, detail) = diagnostic.getMessage.span(_ != '\n')
    val notes = diagnostic.frames.map(frame => s"\nnote: in ${renderFrame(frame)}").mkString
    s"""
       |$where${pos.line}:${pos.column}: error: $headline
       |$text
       |$indent${"^" * width}$detail$notes
       |""".stripMargin
  }

  /** A context frame as the phrase that follows "in". */
  private[raccoonlang] def renderFrame(frame: Frame): String =
    frame match {
      case Frame.InDefinition(name)                   => s"definition $name"
      case Frame.InArgument(index, binder, callee)    => s"argument $index ($binder) of $callee"
      case Frame.InBranch(ctor, args) if args.isEmpty => s"branch $ctor"
      case Frame.InBranch(ctor, args)                 => s"branch $ctor ${args.mkString(" ")}"
    }
}
