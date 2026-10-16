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
      stackBytes: Option[Long] = None,
      entry: Option[Path] = None
  )

  private val Usage =
    "Usage: raccoon-lang [--root <dir>] [--prelude <file> | --no-prelude] [--wait-for-enter] [--json] " +
      "[--stack <size>] <file>"

  private val StackSize = """(\d+)([kKmMgG]?)""".r

  /** Positive bytes, or KiB, MiB or GiB with the suffix `k`, `m` or `g`, in either case. */
  private def parseStackSize(size: String): Option[Long] =
    size match {
      case StackSize(count, unit) =>
        val scale = unit.toLowerCase match {
          case "k" => 1L << 10
          case "m" => 1L << 20
          case "g" => 1L << 30
          case _   => 1L
        }
        count.toLongOption.filter(n => n > 0 && n <= Long.MaxValue / scale).map(_ * scale)
      case _ => None
    }

  def main(args: Array[String]): Unit = {
    val parsedArgs = {
      @annotation.tailrec
      def loop(rest: List[String], cur: CliArgs): CliArgs =
        rest match {
          case Nil => cur
          case "--root" :: root :: tail =>
            loop(tail, cur.copy(roots = cur.roots :+ Paths.get(root)))
          case "--root" :: Nil => cur.copy(entry = None)
          case "--prelude" :: path :: tail =>
            loop(tail, cur.copy(preludePath = Some(Paths.get(path))))
          case "--prelude" :: Nil => cur.copy(entry = None)
          case "--no-prelude" :: tail =>
            loop(tail, cur.copy(noPrelude = true))
          case "--wait-for-enter" :: tail =>
            loop(tail, cur.copy(waitForEnter = true))
          case "--json" :: tail =>
            loop(tail, cur.copy(json = true))
          case "--stack" :: size :: tail =>
            parseStackSize(size) match {
              case Some(bytes) => loop(tail, cur.copy(stackBytes = Some(bytes)))
              case None        => cur.copy(entry = None)
            }
          case "--stack" :: Nil => cur.copy(entry = None)
          case file :: tail if cur.entry.isEmpty =>
            loop(tail, cur.copy(entry = Some(Paths.get(file))))
          case _ => cur.copy(entry = None)
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

    // Under --json, stdout carries only the diagnostics array.
    def log(s: String): Unit =
      if (!parsedArgs.json) {
        val timestamp = LogTimestampFormat.format(Instant.ofEpochMilli(System.currentTimeMillis()))
        println(s"$timestamp: $s")
      }

    if (parsedArgs.waitForEnter) {
      System.err.println("JVM started. Press Enter to continue.")
      scala.io.StdIn.readLine()
    }

    def runPipeline(): Int = {
      var loadedOpt = Option.empty[ModuleLoader.LoadedProgram]

      def report(diagnostics: Vector[Diagnostic], sources: Vector[ModuleLoader.LoadedSource]): Int = {
        if (parsedArgs.json) println(DiagnosticJson.render(diagnostics, sources))
        else System.err.println(ErrorReporter.pretty(diagnostics, sources))
        1
      }

      try {
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
        val loaded = ModuleLoader.load(entry, loadConfig)
        loadedOpt = Some(loaded)
        log("Loaded")
        val elaborated = Elaborator.elaborate(loaded.program, prelude)
        log("Elaborated")
        val checked = TypeChecker.check(elaborated)
        log("Checked")
        val result = Interpreter.run(checked)
        if (parsedArgs.json) println(DiagnosticJson.render(Vector.empty, Vector.empty))
        else result.foreach(value => println(PrettyPrinter.print(value)))
        log("Done")
        0
      } catch {
        case ModuleLoader.LoadFailure(diagnostic, sources) => report(Vector(diagnostic), sources)
        case Execution.CheckFailure(diagnostics) =>
          report(diagnostics, loadedOpt.map(_.sources).getOrElse(Vector.empty))
        // Elaboration fails fast with a lone diagnostic.
        case diagnostic: Diagnostic =>
          report(Vector(diagnostic), loadedOpt.map(_.sources).getOrElse(Vector.empty))
        case internal: InternalError =>
          System.err.println(ErrorReporter.pretty(internal, loadedOpt.map(_.sources).getOrElse(Vector.empty)))
          internal.printStackTrace()
          70
        case NonFatal(e) =>
          System.err.println(Option(e.getMessage).getOrElse(e.toString))
          1
      }
    }

    // The absent option keeps the JVM's current default thread stack. Only an explicit --stack creates a worker.
    val exitCode = parsedArgs.stackBytes.fold(runPipeline())(bytes => Execution.onStack(bytes)(runPipeline()))
    sys.exit(exitCode)
  }
}
