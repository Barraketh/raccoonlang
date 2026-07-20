package com.raccoonlang

import com.raccoonlang.LeanExportIr.ExportProvenance

sealed trait LeanImportDiagnostic extends RuntimeException {
  def provenance: ExportProvenance
  def declaration: Option[String]
  def path: Vector[String]
  def message: String
  final override def getMessage: String = {
    val rendered = s"${provenance.source}:${provenance.line}:${provenance.column}: $message"
    if (rendered.length <= 4096) rendered else rendered.take(4093) + "..."
  }
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
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class BadBVar(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class InvalidBinderMetadata(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class UnknownGlobal(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class ForwardGlobal(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class UnsafeDependency(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class TypeLowering(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class BodyLowering(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class DeclarationTypeError(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class UnsupportedFeature(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class ApplicationConventionMismatch(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class SuppliedImplicitMismatch(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class UnsaturatedCoreApplication(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class MissingKernelGate(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic

final case class ReservedNameViolation(
    provenance: ExportProvenance,
    message: String,
    declaration: Option[String] = None,
    path: Vector[String] = Vector.empty
) extends LeanImportDiagnostic
