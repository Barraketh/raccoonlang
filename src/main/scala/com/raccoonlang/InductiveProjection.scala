package com.raccoonlang

import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import java.util.concurrent.atomic.AtomicInteger

/** Primitive positional projection for one-constructor inductive families. */
object InductiveProjection {
  private val NoSpan = Span(0, 0)

  // Projection-head Pis are internal checked syntax. Parser-assigned refs are non-negative.
  private val syntheticRefId = new AtomicInteger(-1)
  private def syntheticRef(name: String): CoreAst.LocalRef = {
    CoreAst.LocalRef(syntheticRefId.getAndDecrement(), name)
  }

  private def projectionInstance(
      base: Value,
      familyName: String,
      expectedInfo: ProjectionInfo
  ): InductiveFamilyInstance =
    base.tpe match {
      case InductiveFamilyValue(inst)
          if inst.head.name == familyName && inst.meta.projectionInfo.exists(_ eq expectedInfo) =>
        inst
      case _ => throw WTF(s"Projection for $familyName has major type ${base.tpe}")
    }

  private def constructorPi(info: ProjectionInfo): VPi =
    info.ctorHead.tpe match {
      case pi: VPi => pi
      case other   => throw WTF(s"Constructor ${info.ctorHead.name} has fields but non-Pi type $other")
    }

  private def parameterEnv(inst: InductiveFamilyInstance, info: ProjectionInfo, pi: VPi): Env = {
    val numParams = info.ctorHead.numErasedFamilyArgs
    val params = pi.binders.take(numParams)
    if (inst.args.length < params.length)
      throw WTF(
        s"Family ${inst.head.name} has ${inst.args.length} arguments, but ${info.ctorHead.name} expects ${params.length} parameters"
      )
    BinderOps.instantiateFull(params, pi.env, inst.args.take(params.length))
  }

  private def validateIndex(familyName: String, info: ProjectionInfo, idx: Int, span: Option[Span]): Unit =
    if (idx < 0 || idx >= info.fieldCount)
      throw InvalidProjection(
        familyName,
        idx,
        s"field index is out of range (${info.fieldCount} fields)",
        span
      )

  private def projectedField(
      base: Value,
      inst: InductiveFamilyInstance,
      info: ProjectionInfo,
      idx: Int,
      fieldTy: Value
  ): Value = {
    val raw =
      base match {
        case VCtor(head, fields, _) =>
          if (head.name != info.ctorHead.name)
            throw WTF(s"Projection for ${info.ctorHead.name} received constructor ${head.name}")
          fields(idx)
        case packed: VPacked =>
          val (ctorName, fields) = packed.codec.decodeHead(packed)
          if (ctorName != info.ctorHead.name)
            throw WTF(s"Projection for ${info.ctorHead.name} received packed constructor $ctorName")
          if (fields.length != info.fieldCount)
            throw WTF(
              s"Packed constructor $ctorName decoded to ${fields.length} fields, expected ${info.fieldCount}"
            )
          fields(idx)
        case _ => stuckProjection(base, inst, info, idx, fieldTy)
      }
    Value.ascribe(raw, fieldTy)
  }

  /** Typecheck and evaluate one positional projection. */
  def check(
      base: Value,
      inst: InductiveFamilyInstance,
      info: ProjectionInfo,
      idx: Int,
      span: Span
  ): Value = {
    validateIndex(inst.head.name, info, idx, Some(span))
    if (Value.isPropositionType(base.tpe))
      ProofReconstruction.recoverField(base.tpe, idx).getOrElse {
        throw InvalidProjection(
          inst.head.name,
          idx,
          "field value or type is not recoverable from the exact proposition",
          Some(span)
        )
      }
    else projectOne(base, inst, info, idx)
  }

  /** Evaluate a previously checked positional projection. */
  def project(base: Value, familyName: String, info: ProjectionInfo, idx: Int): Value = {
    val inst = projectionInstance(base, familyName, info)
    validateIndex(familyName, info, idx, None)
    if (Value.isPropositionType(base.tpe))
      ProofReconstruction.recoverField(base.tpe, idx).getOrElse {
        throw WTF(s"Checked projection $familyName.$idx is not recoverable at runtime from ${base.tpe}")
      }
    else projectOne(base, inst, info, idx)
  }

  private def projectOne(
      base: Value,
      inst: InductiveFamilyInstance,
      info: ProjectionInfo,
      idx: Int
  ): Value = {
    val pi = constructorPi(info)
    val fields = pi.binders.drop(info.ctorHead.numErasedFamilyArgs)
    var env = parameterEnv(inst, info, pi)
    val dependencies = info.fieldDependencies(idx)

    var fieldIdx = 0
    while (fieldIdx < idx) {
      if (dependencies.contains(fieldIdx)) {
        val binder = fields(fieldIdx)
        val fieldTy = Interpreter.evalTerm(binder.ty, env)
        env = BinderOps.bindValue(env, binder, projectedField(base, inst, info, fieldIdx, fieldTy))
      }
      fieldIdx += 1
    }

    val fieldTy = Interpreter.evalTerm(fields(idx).ty, env)
    projectedField(base, inst, info, idx, fieldTy)
  }

  /** Build all of a neutral base's projections once, left-to-right, for structure eta expansion. */
  private[raccoonlang] def projections(
      base: Value,
      inst: InductiveFamilyInstance,
      info: ProjectionInfo
  ): Vector[Value] = {
    if (info.fieldCount == 0) return Vector.empty

    val pi = constructorPi(info)
    val fields = pi.binders.drop(info.ctorHead.numErasedFamilyArgs)
    var env = parameterEnv(inst, info, pi)
    val result = Vector.newBuilder[Value]
    var idx = 0
    while (idx < info.fieldCount) {
      val binder = fields(idx)
      val fieldTy = Interpreter.evalTerm(binder.ty, env)
      val projection = projectedField(base, inst, info, idx, fieldTy)
      env = BinderOps.bindValue(env, binder, projection)
      result += projection
      idx += 1
    }
    result.result()
  }

  private def projectionHeadName(familyName: String, idx: Int): String =
    s"@proj[$familyName,$idx]"

  private def stuckProjection(
      base: Value,
      inst: InductiveFamilyInstance,
      info: ProjectionInfo,
      idx: Int,
      fieldTy: Value
  ): Value = {
    val head = VConst(
      projectionHeadName(inst.head.name, idx),
      StructField(inst.head.name, idx, info),
      projectionPi(inst, info, idx, base.tpe)
    )
    val app = base match {
      case Blocker(blockedOn) => VBlockedApp(head, Vector(base), fieldTy, blockedOn)
      case _                  => VApp(head, Vector(base), fieldTy)
    }
    StructEta.expandIfStruct(Value.canonicalizeProof(app))
  }

  /** Honest type carried by the internal projection head for keys, dependencies, and diagnostics. */
  private def projectionPi(
      inst: InductiveFamilyInstance,
      info: ProjectionInfo,
      idx: Int,
      instTpe: Value
  ): VPi = {
    val selfRef = syntheticRef("self")
    val tyRef = syntheticRef("self.ty")
    val piEnv = Env.empty.putLocal(tyRef, instTpe)
    val binders = Vector(ElabAst.Binder(selfRef, ETerm.LocalRef(tyRef, NoSpan), NoSpan))
    lazy val codomain: Env => Value = env => project(env(selfRef), inst.head.name, info, idx).tpe
    VPi(
      piEnv,
      binders,
      codomain,
      synDeps = instTpe.synDeps,
      id = ValueId.LocalId(AstNodeId.synthetic(), Vector(instTpe)),
      classifier0 = () => {
        val outTy = codomain(BinderOps.freshen(binders, piEnv))
        VSort(Level.imax(TypeChecker.getUniverse(instTpe).level, TypeChecker.getUniverse(outTy).level))
      }
    )
  }
}
