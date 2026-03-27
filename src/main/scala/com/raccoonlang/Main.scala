package com.raccoonlang

import scala.util.control.NonFatal

object Main {
  def main(args: Array[String]): Unit = {
    if (args.length != 1) {
      System.err.println("Usage: raccoon-lang <file>")
      sys.exit(2)
    }

    val input = try {
      val src = scala.io.Source.fromFile(args(0))
      try src.mkString
      finally src.close()
    } catch {
      case NonFatal(e) =>
        System.err.println(s"Failed to read file: ${e.getMessage}")
        sys.exit(2)
        return
    }

    LanguageParser.parseProgram(input) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          val resOpt = Interpreter.run(core)
          resOpt.foreach { v => println(PrettyPrinter.print(v)) }
          sys.exit(0)
        } catch {
          case te: TypeError =>
            val src = ErrorReporter.Source(input)
            System.err.println(ErrorReporter.pretty(te, src))
            sys.exit(1)
          case NonFatal(e) =>
            System.err.println(Option(e.getMessage).getOrElse(e.toString))
            sys.exit(1)
        }

      case Failure(_, curIdx, message) =>
        // Simple parse error pretty print with caret
        val src = ErrorReporter.Source(input)
        val line = src.getLine(curIdx)
        val lineOffset = curIdx - line.start
        val caret = " " * Math.max(0, lineOffset) + "^"
        System.err.println(s"parse error: $message")
        System.err.println(input.slice(line.start, line.end))
        System.err.println(caret)
        sys.exit(1)
    }
  }
}
