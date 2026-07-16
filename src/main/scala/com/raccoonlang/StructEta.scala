package com.raccoonlang

import com.raccoonlang.ElabAst.{Term => ETerm}
import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

/**
 * Structure eta as representation (K4, docs/mathlib-export-port.md §4): every value of an eta-eligible struct type is
 * constructor-headed *from creation*. Proof representation instead exposes a declaration-certified constructor for
 * every inhabitant whose exact proposition reconstructs it, and erases other non-Pi inhabitants. Struct values always
 * expose their fields. Expansion is enforced at binder freshening and at every neutral-creation seam (stuck
 * applications and matches, published opaque/axiom globals, recursive-call residuals, stuck builtins).
 *
 * Canonical-at-birth is deliberate: ascription and materialization do NOT expand. They retype values that already
 * circulate, and wrapping one copy while the bare original lives on (in envs, inside other values) would split the
 * representation — and unlike proof forms, which `ProofEquation` reunites, expansion has no mixed defEq rule.
 *
 * With the invariant in force, eta needs no conversion rule: `c ≡ mk(c.a, c.b)` is VCtor-vs-VCtor for the existing
 * fieldwise defEq, and a match on a struct scrutinee always fires (binding the branch to the scrutinee's projections —
 * "assume the single constructor" as a consequence, not a reduction rule).
 *
 * Eligibility (`InductiveMeta.etaInfo`, computed in InductiveChecks): a declared struct with one constructor, no
 * indices, no recursive field, not declared in Prop. The gate is load-bearing for decidability, not a heuristic:
 * "single constructor" alone would admit `Acc` (destructuring neutral accessibility proofs is the undecidability
 * channel K2 seals) and `Quot.mk` (expansion would invent a representative for a quotient). Both are also excluded by
 * other layers (Prop collapse, recursion, not being declared structs), but eligibility must never rest on that
 * coincidence. Prop *instantiations* never eta-expand; every inhabitant follows the family's independent `ProofStorage`
 * policy, reconstructing the certified constructor when possible and otherwise using proof eta or `VProof`.
 *
 * Known gap (completeness only, never soundness): a value created before its type is a *known* struct instance stays
 * bare — a rigid binder frozen at a then-blocked type, or a neutral whose type reveals only under a later store. Rigid
 * vars additionally cannot be expanded in place: rigid and refinable are store-relative, and expanding a meta would
 * break unification's Var-linking (the same reason `canonicalizeProof` exempts Vars).
 */
object StructEta {

  private val NoSpan = Span(0, 0)

  // Synthetic LocalRefs for projection-head types. Parser-assigned ref ids are non-negative, so
  // negative ids can never collide with source refs inside a shared env.
  private var syntheticRefId = -1
  private def syntheticRef(name: String): CoreAst.LocalRef = {
    val ref = CoreAst.LocalRef(syntheticRefId, name)
    syntheticRefId -= 1
    ref
  }

  /**
   * The instance behind `tpe` when it is an application of a struct family with eta capability, regardless of sort.
   * Callers that create values must use `eligibleInstance`.
   */
  private def anyInstance(tpe: Value): Option[(InductiveFamilyInstance, StructEtaInfo)] =
    tpe match {
      case InductiveFamilyValue(inst) => inst.meta.etaInfo.map(info => (inst, info))
      case _                          => None
    }

  /**
   * The instance behind `tpe` when it is an eta-eligible struct instance at a non-propositional sort. Prop
   * instantiations are proof territory: they follow `ProofStorage` and never eta-expand.
   */
  def eligibleInstance(tpe: Value): Option[(InductiveFamilyInstance, StructEtaInfo)] =
    anyInstance(tpe).filter(_ => !Value.isPropositionType(tpe))

  /**
   * A fresh rigid witness at `tpe`: for an eligible struct instance, the constructor applied to fresh field witnesses —
   * recursively, via ordinary binder freshening, so nested struct fields expand and proof fields collapse. None for
   * non-struct types (callers fall back to a bare Var).
   */
  def freshStructWitness(tpe: Value): Option[Value] =
    eligibleInstance(tpe).map { case (inst, info) =>
      val head = info.ctorHead
      head.tpe match {
        case pi: VPi =>
          val paramBinders = pi.binders.take(head.numErasedFamilyArgs)
          val fieldBinders = pi.binders.drop(head.numErasedFamilyArgs)
          val paramEnv = BinderOps.instantiateFull(paramBinders, pi.env, inst.args)
          val fieldEnv = BinderOps.freshen(fieldBinders, paramEnv)
          VCtor(head, fieldBinders.map(binder => fieldEnv(binder.localRef)), tpe)
        case _ => VCtor(head, Vector.empty, tpe)
      }
    }

  /**
   * Enforce the representation invariant on a just-created value: a neutral at an eligible struct type wraps into
   * constructor form, its fields the stuck projections of the base. Idempotent. Exemptions mirror `canonicalizeProof`:
   * VCtor/VProof are already canonical, and Vars stay bare so refinable metas remain linkable.
   */
  def expandIfStruct(value: Value): Value =
    value match {
      case VCtor(_, _, _)     => value
      case _: Var | _: VProof => value
      case _: VConst | _: VApp | _: NeutralThunk =>
        eligibleInstance(value.tpe) match {
          case Some((inst, info)) =>
            VCtor(info.ctorHead, projections(value, inst, info, info.fieldNames.length), value.tpe)
          case None => value
        }
      case _ => value
    }

  /**
   * Reduce `field idx of base` (the `StructField` application rule, called from `Interpreter.evalApply`): a
   * constructor-headed base gives the stored field; a base that is still neutral after resolution re-sticks at its
   * (possibly refined) type; a base that *collapsed* under a solved store — its sort resolved to Prop — projects to a
   * proof of the instantiated field type. That last arm is sound because every field of a struct fits in the struct's
   * own sort (InductiveUniverseTooSmall), so at a Prop instance every field is a proof.
   */
  def project(base: Value, idx: Int): Value =
    base match {
      case VCtor(_, fields, _) => fields(idx)
      case _ =>
        anyInstance(base.tpe) match {
          case Some((inst, info)) => projections(base, inst, info, idx + 1).last
          case None =>
            throw WTF(s"Projection of field $idx from non-struct value $base of type ${base.tpe}")
        }
    }

  /**
   * The first `count` projections of `base`, built left-to-right so each dependent field type is instantiated with the
   * earlier projections.
   */
  private def projections(
      base: Value,
      inst: InductiveFamilyInstance,
      info: StructEtaInfo,
      count: Int
  ): Vector[Value] = {
    if (count == 0) return Vector.empty
    val head = info.ctorHead
    val pi = head.tpe match {
      case pi: VPi => pi
      case other   => throw WTF(s"Struct constructor ${head.name} has fields but non-Pi type $other")
    }
    val fieldBinders = pi.binders.drop(head.numErasedFamilyArgs)
    var env = BinderOps.instantiateFull(pi.binders.take(head.numErasedFamilyArgs), pi.env, inst.args)
    val result = Vector.newBuilder[Value]
    (0 until count).foreach { idx =>
      val binder = fieldBinders(idx)
      val fieldTy = Interpreter.evalTerm(binder.ty, env)
      val proj = stuckProjection(base, inst, info, idx, fieldTy)
      env = BinderOps.bindValue(env, binder, proj)
      result += proj
    }
    result.result()
  }

  private def stuckProjection(
      base: Value,
      inst: InductiveFamilyInstance,
      info: StructEtaInfo,
      idx: Int,
      fieldTy: Value
  ): Value = {
    val name = s"${inst.head.name}.${info.fieldNames(idx)}"
    val head = VConst(name, StructField(idx), projectionPi(inst, info, idx, base.tpe))
    val app = base match {
      case Blocker(blockerId) => VBlockedApp(head, Vector(base), fieldTy, blockerId)
      case _                  => VApp(head, Vector(base), fieldTy)
    }
    // Proof fields erase at formation; struct fields
    // expand recursively — bounded by the nesting depth, since eligible structs are non-recursive.
    expandIfStruct(Value.canonicalizeProof(app))
  }

  /**
   * The projection head's own type: `(self: <instance>) -> <field type at self>`. Nothing on the kernel path evaluates
   * it — StructField applications are built and reduced directly, and `runLam` is never involved — but the head must
   * carry an honest type for keys/synDeps and diagnostics. The binder's type syntax is a LocalRef bound in the Pi's
   * closure env, so the Pi is freshenable and its codomain evaluable without any global environment. Named heads quote
   * as `GlobalRef("S.field")`, deliberately aliasing the generated selector of the same name.
   */
  private def projectionPi(
      inst: InductiveFamilyInstance,
      info: StructEtaInfo,
      idx: Int,
      instTpe: Value
  ): VPi = {
    val selfRef = syntheticRef("self")
    val tyRef = syntheticRef("self.ty")
    val piEnv = Env.empty.putLocal(tyRef, instTpe)
    val binders = Vector(ElabAst.Binder(selfRef, ETerm.LocalRef(tyRef, NoSpan), NoSpan))
    lazy val codomain: Env => Value = env => fieldTypeOf(env(selfRef), inst, info, idx)
    VPi(
      piEnv,
      binders,
      codomain,
      synDeps = instTpe.synDeps,
      // A fresh synthetic id per Pi: a shared name-based id would give the projection Pis of
      // *different* instances identical trusted ValueKeys (kernel-theory §2/§6 — never extend
      // key-trusted surfaces). Distinct ids only forfeit the key fast path; the head VConsts
      // these types hang off compare by name, so nothing depends on Pi key equality.
      id = ValueId.LocalId(AstNodeId.synthetic(), Vector(instTpe)),
      classifier0 = () => {
        val outTy = codomain(BinderOps.freshen(binders, piEnv))
        VSort(Level.imax(TypeChecker.getUniverse(instTpe).level, TypeChecker.getUniverse(outTy).level))
      }
    )
  }

  /**
   * The type of field `idx` at a concrete `self` (constructor-headed by the invariant, so the dependent prefix reads
   * stored fields directly).
   */
  private def fieldTypeOf(self: Value, inst: InductiveFamilyInstance, info: StructEtaInfo, idx: Int): Value = {
    val head = info.ctorHead
    val pi = head.tpe match {
      case pi: VPi => pi
      case other   => throw WTF(s"Struct constructor ${head.name} has fields but non-Pi type $other")
    }
    val fieldBinders = pi.binders.drop(head.numErasedFamilyArgs)
    var env = BinderOps.instantiateFull(pi.binders.take(head.numErasedFamilyArgs), pi.env, inst.args)
    fieldBinders.take(idx).zipWithIndex.foreach { case (binder, j) =>
      env = BinderOps.bindValue(env, binder, project(self, j))
    }
    Interpreter.evalTerm(fieldBinders(idx).ty, env)
  }
}
