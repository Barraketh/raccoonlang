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

  /**
   * Typecheck and evaluate one projection in a single left-to-right constructor-telescope pass. A preceding field is
   * projected only when the remaining telescope actually mentions it; this is both Lean's typing rule for Prop majors
   * and what keeps forbidden data projections from being fabricated internally.
   */
  def check(
      base: Value,
      inst: InductiveFamilyInstance,
      info: ProjectionInfo,
      idx: Int,
      span: Span
  ): Value =
    projectOne(base, inst, info, idx, enforcePropRules = true, span = Some(span))

  /** Evaluate a previously checked positional projection. */
  def project(base: Value, familyName: String, info: ProjectionInfo, idx: Int): Value = {
    val inst = projectionInstance(base, familyName, info)
    projectOne(base, inst, info, idx, enforcePropRules = false, span = None)
  }

  private def projectOne(
      base: Value,
      inst: InductiveFamilyInstance,
      info: ProjectionInfo,
      idx: Int,
      enforcePropRules: Boolean,
      span: Option[Span]
  ): Value = {
    val familyName = inst.head.name
    validateIndex(familyName, info, idx, span)
    val pi = constructorPi(info)
    val fields = pi.binders.drop(info.ctorHead.numErasedFamilyArgs)
    var env = parameterEnv(inst, info, pi)
    val propMajor = enforcePropRules && Value.isPropositionType(base.tpe)

    var fieldIdx = 0
    while (fieldIdx < idx) {
      if (info.fieldNeededInSuffix(fieldIdx)) {
        val binder = fields(fieldIdx)
        val fieldTy = Interpreter.evalTerm(binder.ty, env)
        if (propMajor && !Value.isPropositionType(fieldTy))
          throw InvalidProjection(
            familyName,
            idx,
            s"preceding dependent field $fieldIdx is not a proposition",
            span
          )
        env = BinderOps.bindValue(env, binder, projectedField(base, inst, info, fieldIdx, fieldTy))
      }
      fieldIdx += 1
    }

    val fieldTy = Interpreter.evalTerm(fields(idx).ty, env)
    if (propMajor && !Value.isPropositionType(fieldTy))
      throw InvalidProjection(familyName, idx, "selected field is not a proposition", span)
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
      case Blocker(blockerId) => VBlockedApp(head, Vector(base), fieldTy, blockerId)
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
