package com.raccoonlang

import com.raccoonlang.{SurfaceAst => SA}

import java.nio.file.{Files, NoSuchFileException, Path}
import scala.collection.mutable
import scala.util.control.NonFatal

object ModuleLoader {
  final case class LoadConfig(sourceRoots: Vector[Path])
  object LoadConfig {
    def forEntry(entry: Path): LoadConfig =
      LoadConfig(Vector(entry.toAbsolutePath.normalize.getParent))
  }

  final case class LoadedSource(sourceId: SourceId, path: Path, source: String)
  final case class LoadedProgram(program: SA.Program, sources: Vector[LoadedSource])

  final case class LoadFailure(error: TypeError, sources: Vector[LoadedSource])
    extends RuntimeException(error.getMessage)

  private final case class ParsedModule(path: Path, sourceId: SourceId, program: SA.Program)

  def load(entry: Path): LoadedProgram =
    load(entry, LoadConfig.forEntry(entry))

  def load(entry: Path, config: LoadConfig): LoadedProgram = {
    val effectiveConfig =
      if (config.sourceRoots.isEmpty) LoadConfig.forEntry(entry)
      else config
    new Loader(effectiveConfig).load(entry)
  }

  private final class Loader(config: LoadConfig) {
    private val sourceRoots = config.sourceRoots.map(_.toAbsolutePath.normalize)
    private val parsed = mutable.Map.empty[Path, ParsedModule]
    private val emitted = mutable.Set.empty[Path]
    private val orderedImports = Vector.newBuilder[SA.Command]
    private var sources = Vector.empty[LoadedSource]
    private var visiting = Vector.empty[Path]

    def load(entry: Path): LoadedProgram = {
      val entryModule = visitEntry(entry)
      LoadedProgram(
        SA.Program(
          imports = Vector.empty,
          decls = orderedImports.result() ++ entryModule.program.decls,
          body = entryModule.program.body
        ),
        sources
      )
    }

    private def visitEntry(path: Path): ParsedModule = {
      val canonical = existingPath(path.toAbsolutePath.normalize, path.toString, None)
      visit(canonical, path.toString, None, isEntry = true)
    }

    private def visit(path: Path, importName: String, importSpan: Option[Span], isEntry: Boolean): ParsedModule = {
      val canonical = existingPath(path, importName, importSpan)
      visiting.indexOf(canonical) match {
        case -1 =>
        case idx =>
          val cycle = visiting.drop(idx) :+ canonical
          fail(CyclicImport(cycle, importSpan))
      }

      parsed.get(canonical) match {
        case Some(module) if isEntry || emitted(canonical) =>
          module
        case _ =>
          val module = parseModule(canonical, importSpan)
          visiting :+= canonical
          try {
            if (!isEntry)
              module.program.body.foreach(body => fail(ImportedModuleHasBody(module.path, Some(body.span))))

            module.program.imports.foreach { imp =>
              if (!Prelude.isPreludeImport(imp.path)) {
                val depPath = resolveImport(imp)
                visit(depPath, imp.path.mkString("."), Some(imp.span), isEntry = false)
              }
            }

            if (!isEntry && !emitted(canonical)) {
              orderedImports += SA.Command.Block(module.program.decls, moduleSpan(module))
              emitted += canonical
            }
          } finally {
            visiting = visiting.dropRight(1)
          }
          module
      }
    }

    private def existingPath(path: Path, importName: String, span: Option[Span]): Path =
      try path.toRealPath()
      catch {
        case _: NoSuchFileException =>
          fail(ModuleNotFound(importName, Vector(path), span))
        case NonFatal(e) =>
          fail(ModuleReadFailed(path, Option(e.getMessage).getOrElse(e.toString), span))
      }

    private def parseModule(path: Path, readSpan: Option[Span]): ParsedModule =
      parsed.getOrElseUpdate(
        path, {
          val source =
            try Files.readString(path)
            catch {
              case NonFatal(e) =>
                fail(ModuleReadFailed(path, Option(e.getMessage).getOrElse(e.toString), readSpan))
            }

          val sourceId = SourceId(sources.length)
          sources :+= LoadedSource(sourceId, path, source)

          LanguageParser.parseProgram(source, sourceId) match {
            case Success(program, _, _) =>
              ParsedModule(path, sourceId, program)
            case Failure(_, curIdx, message) =>
              fail(ModuleParseError(path, message, curIdx, Some(Span(curIdx, curIdx, Some(sourceId)))))
          }
        }
      )

    private def resolveImport(imp: SA.Import): Path = {
      val relative =
        imp.path.zipWithIndex.foldLeft(sourceRoots.head.getFileSystem.getPath("")) { case (cur, (part, idx)) =>
          val name = if (idx == imp.path.length - 1) s"$part.rac" else part
          cur.resolve(name)
        }
      val candidates = sourceRoots.map(root => root.resolve(relative).normalize)
      candidates
        .find(Files.isRegularFile(_))
        .map(_.toRealPath())
        .getOrElse(fail(ModuleNotFound(imp.path.mkString("."), candidates, Some(imp.span))))
    }

    private def fail(error: TypeError): Nothing =
      throw LoadFailure(error, sources)
  }

  private def moduleSpan(module: ParsedModule): Span =
    module.program.decls match {
      case first +: rest =>
        val firstSpan = commandSpan(first)
        Span(firstSpan.start, commandSpan(rest.lastOption.getOrElse(first)).end, firstSpan.source)
      case _ =>
        Span(0, 0, Some(module.sourceId))
    }

  private def commandSpan(command: SA.Command): Span =
    command match {
      case decl: SA.Command.Decl            => declSpan(decl)
      case SA.Command.Namespace(_, _, span) => span
      case SA.Command.Open(_, _, _, span)   => span
      case SA.Command.Block(_, span)        => span
    }

  private def declSpan(decl: SA.Command.Decl): Span =
    decl match {
      case SA.Command.Decl.ConstDecl(_, _, _, _, span, _) => span
      case SA.Command.Decl.AxiomDecl(_, span, _)          => span
      case SA.Command.Decl.InductiveDecl(_, _, _, span)   => span
    }

}
