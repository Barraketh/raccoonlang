package com.raccoonlang

import com.raccoonlang.CoreAst.LocalRef
import com.raccoonlang.LeanExportIr.BinderInfo

sealed trait ImportedSourceBinder
final case class SourceTermBinder(info: BinderInfo) extends ImportedSourceBinder
case object SourceUniverseParameter extends ImportedSourceBinder

final case class ImportedBinder(
    sourceOrdinal: Int,
    sourceInfo: ImportedSourceBinder,
    coreBinderId: LocalRef,
    requestedImplicit: Boolean,
    checkedImplicit: Boolean
)

final case class ImportedTelescope(binders: Vector[ImportedBinder], corePi: CoreAst.Term.Pi)
final case class ImportedCallingConvention(universeCount: Int, telescopes: Vector[ImportedTelescope])
