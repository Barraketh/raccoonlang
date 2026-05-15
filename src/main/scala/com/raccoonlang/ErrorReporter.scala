package com.raccoonlang

object ErrorReporter {

  case class Line(start: Int, end: Int, lineNum: Int)
  case class Source(s: String) {
    val newLineLocations = s.zipWithIndex.filter { case (c, _) => c == '\n' }.map(_._2)
    val lines: IndexedSeq[Line] =
      if (newLineLocations.isEmpty) Vector(Line(0, s.length, 0))
      else {
        val linesMiddle = newLineLocations.zip(newLineLocations.tail)
        val allLines = ((0, newLineLocations.head) +: linesMiddle) :+ (newLineLocations.last, s.length)
        allLines.zipWithIndex.map { case ((lineStart, lineEnd), lineNum) =>
          val actualLineStart = if (lineStart == 0) 0 else lineStart + 1
          Line(actualLineStart, lineEnd, lineNum)
        }
      }

    def getLine(offset: Int): Line = lines.findLast(_.start <= offset).get
  }

  def pretty(err: TypeError, source: Source): String = {
    val sp = err.span.getOrElse(Span(0, 0))
    val line = source.getLine(sp.start)
    val lineOffset = sp.start - line.start
    val caretLine = " " * lineOffset + "^"
    s"""
       |${line.lineNum}:${lineOffset}: error: ${err.getMessage}
       |${source.s.slice(line.start, line.end)}
       |$caretLine
       |""".stripMargin
  }

  def pretty(err: TypeError, loaded: ModuleLoader.LoadedProgram): String =
    pretty(err, loaded.sources)

  def pretty(err: TypeError, sources: Vector[ModuleLoader.LoadedSource]): String = {
    if (sources.isEmpty)
      return err.getMessage

    val sp = err.span.getOrElse(Span(0, 0))
    val loadedSource =
      sp.source
        .flatMap(sourceId => sources.find(_.sourceId == sourceId))
        .getOrElse(sources.head)

    val localOffset = math.max(0, math.min(sp.start, loadedSource.source.length))
    val source = Source(loadedSource.source)
    val line = source.getLine(localOffset)
    val lineOffset = localOffset - line.start
    val caretLine = " " * lineOffset + "^"
    s"""
       |${loadedSource.path.toString}:${line.lineNum}:${lineOffset}: error: ${err.getMessage}
       |${loadedSource.source.slice(line.start, line.end)}
       |$caretLine
       |""".stripMargin
  }

}
