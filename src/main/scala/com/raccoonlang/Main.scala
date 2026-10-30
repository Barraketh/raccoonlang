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
      noUserAxioms: Boolean = false,
      stackBytes: Long = DefaultStackBytes,
      entry: Option[Path] = None
  )

  private val Usage =
    "Usage: raccoon-lang [--root <dir>] [--prelude <file> | --no-prelude] [--no-user-axioms] [--wait-for-enter] " +
      "[--stack <size>] <file>"

  /** The stack of the thread that checks and runs a program, unless `--stack` sets it. */
  private val DefaultStackBytes = 256L << 20

  private val StackSize = """(\d+)([kKmMgG]?)""".r

  /**
   * A `--stack` size in bytes: a positive whole number of bytes, or of KiB, MiB or GiB with the suffix `k`, `m` or `g`
   * in either case, as `-Xss` reads it. Anything else, or a size beyond a `Long`, is not a size.
   */
  private[raccoonlang] def parseStackSize(size: String): Option[Long] =
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
          case "--no-user-axioms" :: tail =>
            loop(tail, cur.copy(noUserAxioms = true))
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

    def log(s: String): Unit = {
      val timestamp = LogTimestampFormat.format(Instant.ofEpochMilli(System.currentTimeMillis()))
      println(s"$timestamp: $s")
    }

    if (parsedArgs.waitForEnter) {
      System.err.println("JVM started. Press Enter to continue.")
      scala.io.StdIn.readLine()
    }

    // The whole pipeline runs on a thread of --stack bytes, which returns the exit code. What it does not catch, the
    // main thread rethrows, and the JVM reports.
    val exitCode = Execution.onStack(parsedArgs.stackBytes) {
      var loadedOpt = Option.empty[ModuleLoader.LoadedProgram]
      try {
        log("Starting")
        val prelude =
          parsedArgs.preludePath match {
            case Some(path)                   => Prelude.fromPath(path)
            case None if parsedArgs.noPrelude => Prelude.none
            case None                         => Prelude.default
          }
        // A custom prelude's axioms are trusted as the bundled prelude's are, with or without `--no-user-axioms`, so
        // they are listed.
        val preludeAxioms = Interpreter.axioms(prelude.core)
        if (parsedArgs.preludePath.nonEmpty && preludeAxioms.nonEmpty)
          System.err.println(s"Prelude axioms (trusted): ${preludeAxioms.map(_.name).mkString(", ")}")
        val loadConfig =
          if (parsedArgs.roots.isEmpty) ModuleLoader.LoadConfig.forEntry(entry, prelude)
          else ModuleLoader.LoadConfig(parsedArgs.roots, prelude)
        val loaded =
          ModuleLoader.load(entry, loadConfig)
        loadedOpt = Some(loaded)
        log("Loaded")
        val core = Elaborator.elab(loaded.program, prelude)
        log("Elaborated")
        // Program axioms are unchecked assumptions; theorems that rely on the trusted bootstrap alone need none.
        val axioms = Interpreter.axioms(core)
        if (axioms.nonEmpty && !parsedArgs.noUserAxioms)
          System.err.println(s"User axioms (unchecked assumptions): ${axioms.map(_.name).mkString(", ")}")
        val resOpt = Interpreter.run(core, prelude, allowUserAxioms = !parsedArgs.noUserAxioms)
        // A program with a result has a body.
        resOpt.foreach(v => println(Interpreter.show(v, core.body.map(TypeChecker.sourceSpan).get)))
        log("Done")
        0
      } catch {
        case ModuleLoader.LoadFailure(error, sources) =>
          System.err.println(ErrorReporter.pretty(error, sources))
          1
        case te: TypeError =>
          loadedOpt match {
            case Some(loaded) => System.err.println(ErrorReporter.pretty(te, loaded))
            case None         => System.err.println(te.getMessage)
          }
          1
        case NonFatal(e) =>
          System.err.println(Option(e.getMessage).getOrElse(e.toString))
          1
      }
    }
    sys.exit(exitCode)
  }
}
