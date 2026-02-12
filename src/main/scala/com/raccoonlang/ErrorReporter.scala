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

  def pretty(err: TypeErrWithSpan, source: Source): String = {
    val line = source.getLine(err.span.start)
    val lineOffset = err.span.start - line.start
    val caretLine = " " * lineOffset + "^"
    s"""
       |${line.lineNum}:${lineOffset}: error: ${err.message}
       |${source.s.slice(line.start, line.end)}
       |$caretLine
       |""".stripMargin
  }

}
