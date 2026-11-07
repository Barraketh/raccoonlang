package com.raccoonlang

import com.raccoonlang.ModuleChecker.{EntryResult, Listener, Options, PreludeSource}

import java.io.PrintStream
import java.nio.file.{Path, Paths}
import java.time.{Instant, ZoneId}
import java.time.format.DateTimeFormatter
import java.util.Locale
import scala.collection.mutable
import scala.util.control.NonFatal

object Main {
  private val LogTimestampFormat =
    DateTimeFormatter.ofPattern("HH:mm:ss.SSS").withZone(ZoneId.systemDefault())

  /**
   * The CLI's arguments. `files` are the entries, as written: one, unless `batch`; none with `serve`, which needs a
   * `socket`. `json` is batch output's form.
   */
  private[raccoonlang] final case class CliArgs(
      roots: Vector[Path] = Vector.empty,
      preludePath: Option[Path] = None,
      noPrelude: Boolean = false,
      waitForEnter: Boolean = false,
      noUserAxioms: Boolean = false,
      stackBytes: Long = DefaultStackBytes,
      batch: Boolean = false,
      json: Boolean = false,
      serve: Boolean = false,
      socket: Option[Path] = None,
      files: Vector[String] = Vector.empty
  )

  private[raccoonlang] val Usage =
    "Usage: raccoon-lang [--root <dir>] [--prelude <file> | --no-prelude] [--no-user-axioms] [--wait-for-enter] " +
      "[--stack <size>] <file>\n" +
      "       raccoon-lang [options] --batch [--json] <file>...\n" +
      "       raccoon-lang --serve --socket <path>"

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

  /** The arguments `args` give, or none when they are not a use of the CLI (`Usage`). */
  private[raccoonlang] def parseArgs(args: Seq[String]): Option[CliArgs] = {
    @annotation.tailrec
    def loop(rest: List[String], cur: CliArgs): Option[CliArgs] =
      rest match {
        case Nil                           => Some(cur)
        case "--root" :: root :: tail      => loop(tail, cur.copy(roots = cur.roots :+ Paths.get(root)))
        case "--prelude" :: path :: tail   => loop(tail, cur.copy(preludePath = Some(Paths.get(path))))
        case "--no-prelude" :: tail        => loop(tail, cur.copy(noPrelude = true))
        case "--wait-for-enter" :: tail    => loop(tail, cur.copy(waitForEnter = true))
        case "--no-user-axioms" :: tail    => loop(tail, cur.copy(noUserAxioms = true))
        case "--batch" :: tail             => loop(tail, cur.copy(batch = true))
        case "--json" :: tail              => loop(tail, cur.copy(json = true))
        case "--serve" :: tail             => loop(tail, cur.copy(serve = true))
        case "--socket" :: path :: tail    => loop(tail, cur.copy(socket = Some(Paths.get(path))))
        case "--stack" :: size :: tail     =>
          parseStackSize(size) match {
            case Some(bytes) => loop(tail, cur.copy(stackBytes = bytes))
            case None        => None
          }
        case ("--root" | "--prelude" | "--socket" | "--stack") :: Nil => None
        case file :: tail                                             => loop(tail, cur.copy(files = cur.files :+ file))
      }

    loop(args.toList, CliArgs()).filter { cli =>
      !(cli.noPrelude && cli.preludePath.nonEmpty) &&
      (!cli.json || cli.batch) &&
      (cli.socket.nonEmpty == cli.serve) &&
      (if (cli.serve) cli.files.isEmpty && !cli.batch else if (cli.batch) cli.files.nonEmpty else cli.files.length == 1)
    }
  }

  def main(args: Array[String]): Unit = {
    val cli = parseArgs(args.toSeq).getOrElse {
      System.err.println(Usage)
      sys.exit(2)
    }

    if (cli.waitForEnter) {
      System.err.println("JVM started. Press Enter to continue.")
      scala.io.StdIn.readLine()
    }

    val exitCode =
      if (cli.serve) Server.serve(cli.socket.get)
      // The whole pipeline runs on a thread of --stack bytes, which returns the exit code. What it does not catch, the
      // main thread rethrows, and the JVM reports.
      else Execution.onStack(cli.stackBytes)(run(cli, new ModuleChecker, Paths.get(""), System.out, System.err))
    sys.exit(exitCode)
  }

  /**
   * The CLI's check of `cli`'s entries with `checker`, its relative paths read from `cwd`, printing to `out` and `err`
   * as the CLI does; returns the exit code. `cli` is a single or batch check, run on a thread of `cli.stackBytes`.
   */
  private[raccoonlang] def run(cli: CliArgs, checker: ModuleChecker, cwd: Path, out: PrintStream, err: PrintStream): Int = {
    val options =
      Options(
        cli.roots.map(cwd.resolve),
        cli.preludePath match {
          case Some(path)            => PreludeSource.File(cwd.resolve(path))
          case None if cli.noPrelude => PreludeSource.Absent
          case None                  => PreludeSource.Bundled
        },
        allowUserAxioms = !cli.noUserAxioms,
        cli.stackBytes
      )
    if (cli.batch) runBatch(cli, checker.run(options), cwd, out, err)
    else runSingle(cli, cli.files.head, checker.run(options), cwd, out, err)
  }

  /** A custom prelude's axioms are trusted as the bundled prelude's are, with or without `--no-user-axioms`. */
  private def preludeAxiomsLine(cli: CliArgs, prelude: Prelude.Config): Option[String] = {
    val axioms = Interpreter.axioms(prelude.core)
    Option.when(cli.preludePath.nonEmpty && axioms.nonEmpty)(s"Prelude axioms (trusted): ${axioms.map(_.name).mkString(", ")}")
  }

  /** Program axioms are unchecked assumptions; theorems that rely on the trusted bootstrap alone need none. */
  private def userAxiomsLine(cli: CliArgs, axioms: Vector[String]): Option[String] =
    Option.when(axioms.nonEmpty && !cli.noUserAxioms)(s"User axioms (unchecked assumptions): ${axioms.mkString(", ")}")

  /** `error` as the CLI reports it: a `TypeError` located in `sources`, anything else by its message. */
  private def report(error: Throwable, sources: Vector[ModuleLoader.LoadedSource]): String =
    error match {
      case te: TypeError => ErrorReporter.pretty(te, sources)
      case other         => Option(other.getMessage).getOrElse(other.toString)
    }

  /** One entry, `shown`, checked and run, with its steps logged on `out` and its errors on `err`. */
  private def runSingle(
      cli: CliArgs,
      shown: String,
      run: ModuleChecker#Run,
      cwd: Path,
      out: PrintStream,
      err: PrintStream
  ): Int = {
    def log(s: String): Unit = {
      val timestamp = LogTimestampFormat.format(Instant.ofEpochMilli(System.currentTimeMillis()))
      out.println(s"$timestamp: $s")
    }

    try {
      log("Starting")
      preludeAxiomsLine(cli, run.prelude._1).foreach(err.println)
      val result = run.check(
        cwd.resolve(shown),
        shown,
        new Listener {
          override def loaded(): Unit = log("Loaded")
          override def elaborated(axioms: Vector[String]): Unit = {
            log("Elaborated")
            userAxiomsLine(cli, axioms).foreach(err.println)
          }
        }
      )
      result.outcome match {
        case Left(error) =>
          err.println(report(error, result.sources))
          1
        case Right(printed) =>
          printed.foreach(result => out.println(result.printed))
          log("Done")
          0
      }
    } catch {
      case NonFatal(e) =>
        err.println(Option(e.getMessage).getOrElse(e.toString))
        1
    }
  }

  /**
   * Every entry of `cli`, checked in turn with what the earlier ones checked, and reported on `out`: one JSON object a
   * line with `--json`, otherwise a verdict line and what the single-file CLI would print. An error is printed once:
   * an entry rejected with an error printed for an earlier one names that entry instead. Exits 0 when every entry is
   * accepted, 1 otherwise.
   */
  private def runBatch(cli: CliArgs, run: ModuleChecker#Run, cwd: Path, out: PrintStream, err: PrintStream): Int = {
    val prelude = try Right(run.prelude._1)
    catch { case NonFatal(e) => Left(e) }
    prelude.foreach(preludeAxiomsLine(cli, _).foreach(err.println))
    val printed = mutable.HashMap.empty[String, String]
    var accepted = 0
    val started = System.nanoTime()
    cli.files.foreach { shown =>
      val start = System.nanoTime()
      val result =
        try prelude.map(_ => run.check(cwd.resolve(shown), shown)).fold(e => EntryResult(Vector.empty, Vector.empty, Left(e)), identity)
        catch { case NonFatal(e) => EntryResult(Vector.empty, Vector.empty, Left(e)) }
      val seconds = (System.nanoTime() - start) / 1e9
      val error = result.outcome.left.toOption.map(report(_, result.sources))
      val stdout = result.outcome.toOption.flatten.fold("")(_.printed + "\n")
      val stderr = (userAxiomsLine(cli, result.axioms).toVector ++ error).map(_ + "\n").mkString
      if (result.outcome.isRight) accepted += 1
      val verdict = if (result.outcome.isRight) "accepted" else "rejected"
      if (cli.json) {
        val failedModule = result.outcome.left.toOption.collect { case te: TypeError => te }.flatMap(_.span).flatMap {
          span => span.source.flatMap(id => result.sources.find(_.sourceId == id)).map(_.path.toString)
        }
        out.println(
          Json.obj(
            "entry"         -> Json.quote(shown),
            "verdict"       -> Json.quote(verdict),
            "exit_code"     -> (if (result.outcome.isRight) "0" else "1"),
            "seconds"       -> "%.3f".formatLocal(Locale.ROOT, seconds),
            "stdout"        -> Json.quote(stdout),
            "stderr"        -> Json.quote(stderr),
            "error_module" -> failedModule.fold("null")(Json.quote)
          )
        )
      } else {
        error.flatMap(printed.get) match {
          case Some(earlier) =>
            out.println(f"$shown: $verdict ($seconds%.2f s), with the error reported above for $earlier")
          case None =>
            out.println(f"$shown: $verdict ($seconds%.2f s)")
            out.print(stdout)
            out.print(stderr)
            error.foreach(printed(_) = shown)
        }
      }
    }
    if (!cli.json)
      out.println(
        f"${cli.files.length} entries: $accepted accepted, ${cli.files.length - accepted} rejected " +
          f"(${(System.nanoTime() - started) / 1e9}%.2f s)"
      )
    if (accepted == cli.files.length) 0 else 1
  }
}
