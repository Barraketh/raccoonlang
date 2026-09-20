package com.raccoonlang

import java.nio.file.{Path, Paths}
import java.time.{Instant, ZoneId}
import java.time.format.DateTimeFormatter
import scala.util.control.NonFatal

object Main {
  private val LogTimestampFormat =
    DateTimeFormatter.ofPattern("HH:mm:ss.SSS").withZone(ZoneId.systemDefault())

  private final case class CliArgs(
      roots: Vector[Path] = Vector.empty,
      preludePath: Option[Path] = None,
      noPrelude: Boolean = false,
      waitForEnter: Boolean = false,
      json: Boolean = false,
      entry: Option[Path] = None
  )

  private val Usage =
    "Usage: raccoon-lang [--root <dir>] [--prelude <file> | --no-prelude] [--wait-for-enter] [--json] <file>"

  def main(args: Array[String]): Unit = {
    val parsedArgs = {
      @annotation.tailrec
      def loop(rest: List[String], cur: CliArgs): CliArgs =
        rest match {
          case Nil =>
            cur
          case "--root" :: root :: tail =>
            loop(tail, cur.copy(roots = cur.roots :+ Paths.get(root)))
          case "--root" :: Nil =>
            cur.copy(entry = None)
          case "--prelude" :: path :: tail =>
            loop(tail, cur.copy(preludePath = Some(Paths.get(path))))
          case "--prelude" :: Nil =>
            cur.copy(entry = None)
          case "--no-prelude" :: tail =>
            loop(tail, cur.copy(noPrelude = true))
          case "--wait-for-enter" :: tail =>
            loop(tail, cur.copy(waitForEnter = true))
          case "--json" :: tail =>
            loop(tail, cur.copy(json = true))
          case file :: tail if cur.entry.isEmpty =>
            loop(tail, cur.copy(entry = Some(Paths.get(file))))
          case _ =>
            cur.copy(entry = None)
        }

      loop(args.toList, CliArgs())
    }

    val entry = parsedArgs.entry.getOrElse {
      System.err.println(Usage)
      sys.exit(2)
      return
    }

    if (parsedArgs.noPrelude && parsedArgs.preludePath.nonEmpty) {
      System.err.println(Usage)
      sys.exit(2)
      return
    }

    // Under --json, stdout carries the diagnostics array and nothing else.
    def log(s: String): Unit =
      if (!parsedArgs.json) {
        val timestamp = LogTimestampFormat.format(Instant.ofEpochMilli(System.currentTimeMillis()))
        println(s"$timestamp: $s")
      }

    var loadedOpt = Option.empty[ModuleLoader.LoadedProgram]

    /** Report every diagnostic of the run, as the array a tool reads or as the text a reader reads. */
    def report(diagnostics: Vector[Diagnostic], sources: Vector[ModuleLoader.LoadedSource]): Nothing = {
      if (parsedArgs.json) println(DiagnosticJson.render(diagnostics, sources))
      else System.err.println(ErrorReporter.pretty(diagnostics, sources))
      sys.exit(1)
    }

    try {
      if (parsedArgs.waitForEnter) {
        System.err.println("JVM started. Press Enter to continue.")
        scala.io.StdIn.readLine()
      }
      log("Starting")
      val prelude =
        parsedArgs.preludePath match {
          case Some(path)                   => Prelude.fromPath(path)
          case None if parsedArgs.noPrelude => Prelude.none
          case None                         => Prelude.default
        }
      val loadConfig =
        if (parsedArgs.roots.isEmpty) ModuleLoader.LoadConfig.forEntry(entry, prelude)
        else ModuleLoader.LoadConfig(parsedArgs.roots, prelude)
      val loaded =
        ModuleLoader.load(entry, loadConfig)
      loadedOpt = Some(loaded)
      log("Loaded")
      val elaborated = Elaborator.elaborate(loaded.program, prelude)
      log("Elaborated")
      val checked = TypeChecker.check(elaborated)
      log("Checked")
      val resOpt = Interpreter.run(checked)
      if (parsedArgs.json) println(DiagnosticJson.render(Vector.empty, Vector.empty))
      else resOpt.foreach { v => println(PrettyPrinter.print(v)) }
      log("Done")
      sys.exit(0)
    } catch {
      case ModuleLoader.LoadFailure(diagnostic, sources) =>
        report(Vector(diagnostic), sources)
      case Execution.CheckFailure(diagnostics) =>
        report(diagnostics, loadedOpt.map(_.sources).getOrElse(Vector.empty))
      // Elaboration fails fast with a lone diagnostic.
      case diagnostic: Diagnostic =>
        report(Vector(diagnostic), loadedOpt.map(_.sources).getOrElse(Vector.empty))
      case internal: InternalError =>
        System.err.println(ErrorReporter.pretty(internal, loadedOpt.map(_.sources).getOrElse(Vector.empty)))
        internal.printStackTrace()
        sys.exit(70)
      case NonFatal(e) =>
        System.err.println(Option(e.getMessage).getOrElse(e.toString))
        sys.exit(1)
    }
  }
}
