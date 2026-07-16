package com.raccoonlang

import com.raccoonlang.Value._

import scala.util.DynamicVariable

/** K3 native literals: constructor folding, accelerated Nat operations, and bundled-Nat validation. */
object Packed {

  /**
   * Re-pack a constructor application over packed fields. The local guards protect the packed value invariant even
   * while the bundled Prelude is being constructed.
   */
  private[raccoonlang] def foldCtor(
      head: ConstructorHead,
      storedArgs: Vector[Value],
      tpe: Value
  ): Option[VPacked] =
    head.name match {
      case NatCodec.zeroName
          if head.totalArity == 0 && storedArgs.isEmpty && head.noConfusion &&
            !isPropositionType(tpe) =>
        Some(VPacked(NatCodec, 0, tpe))
      case NatCodec.succName
          if head.totalArity == 1 && head.numErasedFamilyArgs == 0 && head.noConfusion &&
            !isPropositionType(tpe) =>
        storedArgs match {
          case Vector(p: VPacked) if p.codec == NatCodec && ValueEquivalence.defEq(p.tpe, tpe) =>
            Some(VPacked(NatCodec, p.payload + 1, tpe))
          case _ => None
        }
      case _ => None
    }

  private sealed trait NatOp
  private final case class ArithOp(run: (BigInt, BigInt) => Option[BigInt]) extends NatOp
  private final case class CmpOp(run: (BigInt, BigInt) => Boolean) extends NatOp

  private[raccoonlang] val MaxPowExponent: BigInt = BigInt(1) << 24

  private val ops: Map[String, NatOp] = Map(
    "Nat.add" -> ArithOp((a, b) => Some(a + b)),
    "Nat.sub" -> ArithOp((a, b) => Some((a - b).max(0))),
    "Nat.mul" -> ArithOp((a, b) => Some(a * b)),
    "Nat.pow" -> ArithOp { (a, b) =>
      if (b > MaxPowExponent) throw NativeOperationLimitExceeded("Nat.pow", b, MaxPowExponent)
      Some(a.pow(b.toInt))
    },
    "Nat.beq" -> CmpOp(_ == _),
    "Nat.ble" -> CmpOp(_ <= _),
    "Nat.blt" -> CmpOp(_ < _)
  )

  /** Names whose meaning is trusted by the packed representation or native-operation table. */
  private[raccoonlang] val reservedNames: Set[String] =
    ops.keySet ++ Set(NatCodec.familyName, NatCodec.zeroName, NatCodec.succName)

  private val opsEnabled = new DynamicVariable[Boolean](true)

  private[raccoonlang] def withOpsDisabled[A](body: => A): A = opsEnabled.withValue(false)(body)

  /** Apply a sound bounded native fast path. Dispatch mismatches fall through to the structural body. */
  private[raccoonlang] def runOp(
      lam: VLam,
      args: Vector[Value],
      resultTy0: () => Value
  ): Option[Value] = {
    if (!opsEnabled.value) return None
    val op = lam.id match {
      case ValueId.Const(name) => ops.getOrElse(name, return None)
      case _                   => return None
    }
    val (a, b) = args match {
      case Vector(x: VPacked, y: VPacked) if x.codec == NatCodec && y.codec == NatCodec =>
        (x.payload, y.payload)
      case _ => return None
    }
    op match {
      case ArithOp(run) =>
        run(a, b).flatMap { result =>
          val resultTy = resultTy0()
          if (ValueEquivalence.defEq(resultTy, args.head.tpe)) Some(VPacked(NatCodec, result, resultTy))
          else None
        }
      case CmpOp(run) =>
        val resultTy = resultTy0()
        boolCtor(lam, if (run(a, b)) "Bool.true" else "Bool.false", resultTy)
    }
  }

  private def boolCtor(lam: VLam, name: String, resultTy: Value): Option[Value] = {
    val env = lam.body match {
      case LamBody.Core(_, env)      => env
      case LamBody.Native(_, env, _) => env
      case LamBody.ProofEta          => Env.empty
    }
    env.globals.get(name).map(_.value(env)) match {
      case Some(h: ConstructorHead) if h.totalArity == 0 && h.noConfusion && ValueEquivalence.defEq(h.tpe, resultTy) =>
        Some(VCtor(h, Vector.empty, resultTy))
      case _ => None
    }
  }

  /** Resolve the authenticated Nat family after the bundled Prelude has passed validateNatFamily. */
  private[raccoonlang] def natFamily(env: Env, span: Span): Value =
    env.globals
      .get(NatCodec.familyName)
      .map(_.value(env))
      .getOrElse(throw NatLiteralUnavailable("no `Nat` in scope", Some(span)))

  /** Validate once that the bundled Prelude's reserved Nat family has exactly the codec's shape. */
  private[raccoonlang] def validateNatFamily(env: Env): Unit = {
    def fail(reason: String): Nothing = throw NatLiteralUnavailable(reason)
    def global(name: String): Option[Value] = env.globals.get(name).map(_.value(env))

    val family = global(NatCodec.familyName).getOrElse(fail("no `Nat` in scope"))
    family match {
      case VConst(_, Inductive(meta), _)
          if meta.familyArity == 0 &&
            meta.constructorNames == Vector(NatCodec.zeroName, NatCodec.succName) =>
      case _ => fail("`Nat` in scope is not the two-constructor unary inductive")
    }
    if (!ValueEquivalence.defEq(family.tpe, TypeTpe)) fail("`Nat` in scope is not Type-valued")

    global(NatCodec.zeroName) match {
      case Some(h: ConstructorHead) if h.totalArity == 0 && h.noConfusion && ValueEquivalence.defEq(h.tpe, family) =>
      case _ => fail(s"`${NatCodec.zeroName}` is not a nullary `Nat` constructor")
    }

    global(NatCodec.succName) match {
      case Some(h: ConstructorHead) if h.totalArity == 1 && h.numErasedFamilyArgs == 0 && h.noConfusion =>
        h.tpe match {
          case pi: VPi if pi.binders.length == 1 =>
            val fieldTy = Interpreter.evalTerm(pi.binders.head.ty, pi.env)
            val outTy = pi.codomain(telescope.BinderOps.freshen(pi))
            if (!ValueEquivalence.defEq(fieldTy, family) || !ValueEquivalence.defEq(outTy, family))
              fail(s"`${NatCodec.succName}` is not `Nat -> Nat`")
          case _ => fail(s"`${NatCodec.succName}` is not `Nat -> Nat`")
        }
      case _ => fail(s"`${NatCodec.succName}` is not a unary `Nat` constructor")
    }

    ()
  }

  /** Evaluation of checked literal syntax after the bundled family has been authenticated. */
  private[raccoonlang] def evalNatLit(value: BigInt, env: Env): Value =
    VPacked(NatCodec, value, env(NatCodec.familyName))
}
