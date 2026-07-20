package com.raccoonlang

import com.raccoonlang.LeanExportIr.ExportProvenance

sealed trait LeanImportDiagnostic extends RuntimeException {
  def provenance: ExportProvenance
  def declaration: Option[String]
  def path: Vector[String]
  def message: String
  final override def getMessage: String =
    s"${provenance.source}:${provenance.line}:${provenance.column}: $message"
}

final case class MalformedExport(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class UnsupportedProducer(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class InternOrder(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class MissingIntern(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class IndexOverflow(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class UnknownLevelParameter(
    provenance: ExportProvenance, message: String, declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class BadBVar(
    provenance: ExportProvenance, message: String, declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class InvalidBinderMetadata(
    provenance: ExportProvenance, message: String, declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class UnknownGlobal(
    provenance: ExportProvenance, message: String, declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class TypeLowering(
    provenance: ExportProvenance, message: String, declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class BodyLowering(
    provenance: ExportProvenance, message: String, declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class DeclarationTypeError(
    provenance: ExportProvenance, message: String, declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class UnsupportedFeature(
    provenance: ExportProvenance, message: String, declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic
