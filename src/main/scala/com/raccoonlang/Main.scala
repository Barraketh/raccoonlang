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
      entry: Option[Path] = None
  )

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
          case file :: tail if cur.entry.isEmpty =>
            loop(tail, cur.copy(entry = Some(Paths.get(file))))
          case _ =>
            cur.copy(entry = None)
        }

      loop(args.toList, CliArgs())
    }

    val entry = parsedArgs.entry.getOrElse {
      System.err.println(
        "Usage: raccoon-lang [--root <dir>] [--prelude <file> | --no-prelude] [--wait-for-enter] <file>"
      )
      sys.exit(2)
      return
    }

    if (parsedArgs.noPrelude && parsedArgs.preludePath.nonEmpty) {
      System.err.println(
        "Usage: raccoon-lang [--root <dir>] [--prelude <file> | --no-prelude] [--wait-for-enter] <file>"
      )
      sys.exit(2)
      return
    }

    def log(s: String): Unit = {
      val timestamp = LogTimestampFormat.format(Instant.ofEpochMilli(System.currentTimeMillis()))
      println(s"$timestamp: $s")
    }

    var loadedOpt = Option.empty[ModuleLoader.LoadedProgram]
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
      val core = Elaborator.elab(loaded.program, prelude)
      log("Elaborated")
      val resOpt = Interpreter.run(core, prelude)
      resOpt.foreach { v => println(PrettyPrinter.print(v)) }
      log("Done")
      sys.exit(0)
    } catch {
      case ModuleLoader.LoadFailure(error, sources) =>
        System.err.println(ErrorReporter.pretty(error, sources))
        sys.exit(1)
      case te: TypeError =>
        loadedOpt match {
          case Some(loaded) => System.err.println(ErrorReporter.pretty(te, loaded))
          case None         => System.err.println(te.getMessage)
        }
        sys.exit(1)
      case NonFatal(e) =>
        System.err.println(Option(e.getMessage).getOrElse(e.toString))
        sys.exit(1)
    }
  }
}
