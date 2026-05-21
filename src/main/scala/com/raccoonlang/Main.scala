package com.raccoonlang

import java.nio.file.{Path, Paths}
import scala.util.control.NonFatal

object Main {
  private final case class CliArgs(
      roots: Vector[Path] = Vector.empty,
      preludePath: Option[Path] = None,
      noPrelude: Boolean = false,
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
          case file :: tail if cur.entry.isEmpty =>
            loop(tail, cur.copy(entry = Some(Paths.get(file))))
          case _ =>
            cur.copy(entry = None)
        }

      loop(args.toList, CliArgs())
    }

    val entry = parsedArgs.entry.getOrElse {
      System.err.println("Usage: raccoon-lang [--root <dir>] [--prelude <file> | --no-prelude] <file>")
      sys.exit(2)
      return
    }

    if (parsedArgs.noPrelude && parsedArgs.preludePath.nonEmpty) {
      System.err.println("Usage: raccoon-lang [--root <dir>] [--prelude <file> | --no-prelude] <file>")
      sys.exit(2)
      return
    }

    var loadedOpt = Option.empty[ModuleLoader.LoadedProgram]
    try {
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
      val core = Elaborator.elab(loaded.program, prelude)
      val resOpt = Interpreter.run(core, prelude)
      resOpt.foreach { v => println(PrettyPrinter.print(v)) }
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
