package com.raccoonlang

import java.nio.file.{Path, Paths}
import scala.util.control.NonFatal

object Main {
  def main(args: Array[String]): Unit = {
    val (rootArgs, entryArg) = {
      @annotation.tailrec
      def loop(rest: List[String], roots: Vector[Path], entry: Option[Path]): (Vector[Path], Option[Path]) =
        rest match {
          case Nil =>
            (roots, entry)
          case "--root" :: root :: tail =>
            loop(tail, roots :+ Paths.get(root), entry)
          case "--root" :: Nil =>
            (roots, None)
          case file :: tail if entry.isEmpty =>
            loop(tail, roots, Some(Paths.get(file)))
          case _ =>
            (roots, None)
        }

      loop(args.toList, Vector.empty, None)
    }

    val entry = entryArg.getOrElse {
      System.err.println("Usage: raccoon-lang [--root <dir>] <file>")
      sys.exit(2)
      return
    }

    var loadedOpt = Option.empty[ModuleLoader.LoadedProgram]
    try {
      val loaded =
        if (rootArgs.isEmpty) ModuleLoader.load(entry)
        else ModuleLoader.load(entry, ModuleLoader.LoadConfig(rootArgs))
      loadedOpt = Some(loaded)
      val core = Elaborator.elab(loaded.program)
      val resOpt = Interpreter.run(core)
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
