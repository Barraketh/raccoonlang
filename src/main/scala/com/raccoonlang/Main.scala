package com.raccoonlang

import java.nio.charset.StandardCharsets
import java.nio.file.{Path, Paths}
import java.time.{Instant, ZoneId}
import java.time.format.DateTimeFormatter
import scala.util.control.NonFatal

object Main {
  private val LogTimestampFormat =
    DateTimeFormatter.ofPattern("HH:mm:ss.SSS").withZone(ZoneId.systemDefault())

  private final case class CliArgs(
      roots: Vector[Path],
      preludePath: Option[Path],
      noPrelude: Boolean,
      waitForEnter: Boolean,
      json: Boolean,
      raw: Boolean,
      stackBytes: Long,
      entry: Option[Path]
  )

  private val Usage =
    "Usage: raccoon-lang [--root <dir>] [--prelude <file> | --no-prelude] [--wait-for-enter] [--json] [--raw] " +
      "[--stack <size>] <file>"

  /** The stack of the thread that checks and runs a program, unless `--stack` sets it (PROOF_BY_EVALUATION §5). */
  private val DefaultStackBytes = 256L << 20

  private val StackSize = """(\d+)([kKmMgG]?)""".r

  /**
   * A `--stack` size in bytes: a positive whole number of bytes, or of KiB, MiB or GiB with the suffix `k`, `m` or `g`
   * in either case, as `-Xss` reads it. Anything else, or a size beyond a `Long`, is not a size.
   */
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
          case "--raw" :: tail =>
            loop(tail, cur.copy(raw = true))
          case "--stack" :: size :: tail =>
            parseStackSize(size) match {
              case Some(bytes) => loop(tail, cur.copy(stackBytes = bytes))
              case None        => cur.copy(entry = None)
            }
          case "--stack" :: Nil =>
            cur.copy(entry = None)
          case file :: tail if cur.entry.isEmpty =>
            loop(tail, cur.copy(entry = Some(Paths.get(file))))
          case _ =>
            cur.copy(entry = None)
        }

      loop(
        args.toList,
        CliArgs(
          roots = Vector.empty,
          preludePath = None,
          noPrelude = false,
          waitForEnter = false,
          json = false,
          raw = false,
          stackBytes = DefaultStackBytes,
          entry = None
        )
      )
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

    // Under --json, stdout carries the diagnostics array and nothing else; under --raw, the result and nothing else.
    def log(s: String): Unit =
      if (!parsedArgs.json && !parsedArgs.raw) {
        val timestamp = LogTimestampFormat.format(Instant.ofEpochMilli(System.currentTimeMillis()))
        println(s"$timestamp: $s")
      }

    var loadedOpt = Option.empty[ModuleLoader.LoadedProgram]

    /** Report every diagnostic of the run, as the array a tool reads or as the text a reader reads; the exit code. */
    def report(diagnostics: Vector[Diagnostic], sources: Vector[ModuleLoader.LoadedSource]): Int = {
      if (parsedArgs.json) println(DiagnosticJson.render(diagnostics, sources))
      else System.err.println(ErrorReporter.pretty(diagnostics, sources))
      1
    }

    if (parsedArgs.waitForEnter) {
      System.err.println("JVM started. Press Enter to continue.")
      scala.io.StdIn.readLine()
    }

    // The whole pipeline runs on a thread of --stack bytes, which returns the exit code. What it does not catch, the
    // main thread rethrows, and the JVM reports.
    val exitCode = Execution.onStack(parsedArgs.stackBytes) {
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
        else
          resOpt.foreach { result =>
            val strings = prelude.checkedEnv.nativeLiterals.stringLayout
            val raw = if (parsedArgs.raw) PrettyPrinter.rawString(result, strings) else None
            raw match {
              // A String's characters exactly: in UTF-8, the encoding of source text, whatever the platform's, and with
              // no newline after them.
              case Some(text) =>
                val bytes = text.getBytes(StandardCharsets.UTF_8)
                System.out.write(bytes, 0, bytes.length)
                System.out.flush()
              case None => println(PrettyPrinter.print(result, strings))
            }
          }
        log("Done")
        0
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
          70
        case NonFatal(e) =>
          System.err.println(Option(e.getMessage).getOrElse(e.toString))
          1
      }
    }
    sys.exit(exitCode)
  }
}
