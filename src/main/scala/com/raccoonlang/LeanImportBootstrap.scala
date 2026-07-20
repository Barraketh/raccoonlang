package com.raccoonlang

import com.raccoonlang.CoreAst.{Binder, ConstBody, Decl, LocalRef}
import com.raccoonlang.CoreAst.Term
import com.raccoonlang.LeanExportIr.ExportProvenance

import java.nio.file.Paths

object LeanImportBootstrap {
  private val source = SourceId.fresh()
  private var nextOffset = 0
  private def span(): Span = { val value = Span(nextOffset, nextOffset + 1, Some(source)); nextOffset += 1; value }

  private def builtin(name: String, binders: Vector[(String, Term)], result: Term): Decl.ConstDecl = {
    val coreBinders = binders.map { case (binderName, tpe) => Binder(LocalRef(nextOffset, binderName), tpe, span()) }
    val tpe = Term.Pi(coreBinders, result, span())
    Decl.ConstDecl(isOpaque = false, name, tpe, ConstBody.Builtin(span()), span())
  }

  private def declarations: Vector[Decl] = {
    val level = Term.GlobalRef("Level", span())
    val tpe = Term.GlobalRef("Type", span())
    Vector(
      builtin("Sort", Vector("u" -> level), tpe),
      builtin("Level.succ", Vector("u" -> level), level),
      builtin("Level.max", Vector("u" -> level, "v" -> level), level),
      builtin("Level.imax", Vector("u" -> level, "v" -> level), level)
    )
  }

  def build(): Either[Vector[LeanImportDiagnostic], Env] = {
    val provenance = ExportProvenance(Paths.get("<lean-import-bootstrap>"), 1L, 1, 0L, "bootstrap", None, None)
    try {
      val base = Interpreter.trustedBootstrap(BootstrapAuthority.Unprivileged).initialEnv
      Right(declarations.foldLeft(base)((env, decl) => Interpreter.evalDecl(decl, env, ReservedNamePermit.leanImportBootstrap)))
    } catch {
      case error: TypeError => Left(Vector(DeclarationTypeError(provenance, error.getMessage)))
      case error: RuntimeException => Left(Vector(DeclarationTypeError(provenance, error.getMessage)))
    }
  }
}
