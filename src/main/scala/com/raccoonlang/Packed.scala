package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.util.DynamicVariable
import scala.util.control.NonFatal

/** K3 native literals: constructor folding, native Nat operations, and trusted-bootstrap validation. */
object Packed {

  /** Issued only after this object validates the complete native Nat family. */
  final class ValidatedNatLayout private[Packed] (val natTpe: Value)

  sealed trait NativeOpOrigin
  case object LeanKernel extends NativeOpOrigin
  case object RaccoonExtension extends NativeOpOrigin

  sealed trait NativeBootstrapProfile
  case object BundledSourcePrelude extends NativeBootstrapProfile
  case object PinnedTranslatedInit extends NativeBootstrapProfile
  case object SyntheticFullK3 extends NativeBootstrapProfile

  sealed abstract class NativeNatOpSpec private[Packed] (
      val name: String,
      val origin: NativeOpOrigin,
      val requiredBy: Set[NativeBootstrapProfile]
  ) {
    private[raccoonlang] def returnsBool: Boolean
  }

  private final class NatOpSpec(
      name: String,
      origin: NativeOpOrigin,
      requiredBy: Set[NativeBootstrapProfile],
      val run: (BigInt, BigInt) => BigInt
  ) extends NativeNatOpSpec(name, origin, requiredBy) {
    override val returnsBool: Boolean = false
  }

  private final class BoolOpSpec(
      name: String,
      origin: NativeOpOrigin,
      requiredBy: Set[NativeBootstrapProfile],
      val run: (BigInt, BigInt) => Boolean
  ) extends NativeNatOpSpec(name, origin, requiredBy) {
    override val returnsBool: Boolean = true
  }

  private[raccoonlang] val MaxPowExponent: BigInt = BigInt(1) << 24
  private[raccoonlang] val MaxShiftLeft: BigInt = BigInt(1) << 24

  private val fullProfiles: Set[NativeBootstrapProfile] = Set(PinnedTranslatedInit, SyntheticFullK3)
  private val allProfiles: Set[NativeBootstrapProfile] = fullProfiles + BundledSourcePrelude

  private def natSpec(
      name: String,
      origin: NativeOpOrigin,
      profiles: Set[NativeBootstrapProfile]
  )(run: (BigInt, BigInt) => BigInt): NativeNatOpSpec =
    new NatOpSpec(name, origin, profiles, run)

  private def boolSpec(
      name: String,
      origin: NativeOpOrigin,
      profiles: Set[NativeBootstrapProfile]
  )(run: (BigInt, BigInt) => Boolean): NativeNatOpSpec =
    new BoolOpSpec(name, origin, profiles, run)

  /** The sole source of native Nat identities, equations, result types, origins, and profile membership. */
  private[raccoonlang] val nativeNatOpSpecs: Vector[NativeNatOpSpec] = Vector(
    natSpec("Nat.add", LeanKernel, allProfiles)(_ + _),
    natSpec("Nat.sub", LeanKernel, allProfiles)((a, b) => (a - b).max(0)),
    natSpec("Nat.mul", LeanKernel, allProfiles)(_ * _),
    natSpec("Nat.pow", LeanKernel, allProfiles) { (a, b) =>
      if (b > MaxPowExponent) throw NativeOperationLimitExceeded("Nat.pow", b, MaxPowExponent)
      a.pow(b.toInt)
    },
    boolSpec("Nat.beq", LeanKernel, allProfiles)(_ == _),
    boolSpec("Nat.ble", LeanKernel, allProfiles)(_ <= _),
    boolSpec("Nat.blt", RaccoonExtension, allProfiles)(_ < _),
    natSpec("Nat.div", LeanKernel, fullProfiles)((a, b) => if (b == 0) BigInt(0) else a / b),
    natSpec("Nat.mod", LeanKernel, fullProfiles)((a, b) => if (b == 0) a else a % b),
    natSpec("Nat.gcd", LeanKernel, fullProfiles)(_.gcd(_)),
    natSpec("Nat.land", LeanKernel, fullProfiles)(_ & _),
    natSpec("Nat.lor", LeanKernel, fullProfiles)(_ | _),
    natSpec("Nat.xor", LeanKernel, fullProfiles)(_ ^ _),
    natSpec("Nat.shiftLeft", LeanKernel, fullProfiles) { (a, count) =>
      if (a == 0) BigInt(0)
      else {
        if (count > MaxShiftLeft)
          throw NativeOperationLimitExceeded("Nat.shiftLeft", count, MaxShiftLeft)
        a << count.toInt
      }
    },
    natSpec("Nat.shiftRight", LeanKernel, fullProfiles) { (a, count) =>
      if (count >= a.bitLength) BigInt(0) else a >> count.toInt
    }
  )

  private val opsByName: Map[String, NativeNatOpSpec] = nativeNatOpSpecs.map(spec => spec.name -> spec).toMap
  require(opsByName.size == nativeNatOpSpecs.size, "Native Nat operation names must be unique")
  private[raccoonlang] val opNames: Set[String] = opsByName.keySet
  private[raccoonlang] val reservedNames: Set[String] =
    opNames ++ Set(NatCodec.familyName, NatCodec.zeroName, NatCodec.succName)

  private val opsEnabled = new DynamicVariable[Boolean](true)
  private[raccoonlang] def withOpsDisabled[A](body: => A): A = opsEnabled.withValue(false)(body)

  private[raccoonlang] def foldCtor(
      head: ConstructorHead,
      storedArgs: Vector[Value],
      tpe: Value
  ): Option[VPacked] =
    head.name match {
      case NatCodec.zeroName
          if head.totalArity == 0 && storedArgs.isEmpty && head.noConfusion &&
            !isPropositionType(tpe) && tpe.synDeps.isEmpty =>
        Some(VPacked.nat(0, tpe))
      case NatCodec.succName
          if head.totalArity == 1 && head.numErasedFamilyArgs == 0 && head.noConfusion &&
            !isPropositionType(tpe) && tpe.synDeps.isEmpty =>
        storedArgs match {
          case Vector(p: VPacked) if p.codec == NatCodec && ValueEquivalence.defEq(p.tpe, tpe) =>
            p.natValue.map(value => VPacked.nat(value + 1, tpe))
          case _ => None
        }
      case _ => None
    }

  /** Apply a native equation only for an exact admitted bootstrap identity and two packed Nats. */
  private[raccoonlang] def runOp(
      lam: VLam,
      args: Vector[Value],
      resultTy0: () => Value
  ): Option[Value] = {
    if (!opsEnabled.value) return None
    val spec = lam.id match {
      case ValueId.Const(name) => opsByName.getOrElse(name, return None)
      case _                   => return None
    }
    val operands = args match {
      case Vector(left: VPacked, right: VPacked) =>
        for {
          a <- left.natValue
          b <- right.natValue
        } yield (a, b)
      case _ => None
    }
    operands.flatMap { case (left, right) =>
      spec match {
        case natOp: NatOpSpec =>
          val result = natOp.run(left, right)
          val resultTy = resultTy0()
          if (ValueEquivalence.defEq(resultTy, args.head.tpe)) Some(VPacked.nat(result, resultTy)) else None
        case boolOp: BoolOpSpec =>
          val result = boolOp.run(left, right)
          val resultTy = resultTy0()
          boolCtor(lam, if (result) "Bool.true" else "Bool.false", resultTy)
      }
    }
  }

  private def boolCtor(lam: VLam, name: String, resultTy: Value): Option[Value] = {
    val env = lam.body match {
      case LamBody.Core(_, env)      => env
      case LamBody.Native(_, env, _) => env
      case LamBody.ProofEta          => Env.empty
    }
    env.globals.get(name).map(_.value(env)) match {
      case Some(h: ConstructorHead)
          if h.name == name && h.totalArity == 0 && h.noConfusion && ValueEquivalence.defEq(h.tpe, resultTy) =>
        Some(VCtor(h, Vector.empty, resultTy))
      case _ => None
    }
  }

  private[raccoonlang] def validateNatFamily(env: Env): ValidatedNatLayout = {
    def fail(reason: String): Nothing = throw NatLiteralUnavailable(reason)
    def global(name: String): Option[Value] = env.globals.get(name).map(_.value(env))

    val family = global(NatCodec.familyName).getOrElse(fail("no `Nat` in scope"))
    family match {
      case VConst(NatCodec.familyName, Inductive(meta), _)
          if meta.familyArity == 0 && meta.constructorNames == Vector(NatCodec.zeroName, NatCodec.succName) =>
      case _ => fail("`Nat` in scope is not the two-constructor unary inductive")
    }
    if (!ValueEquivalence.defEq(family.tpe, TypeTpe)) fail("`Nat` in scope is not Type-valued")
    val zero = global(NatCodec.zeroName) match {
      case Some(h: ConstructorHead)
          if h.name == NatCodec.zeroName && h.totalArity == 0 && h.noConfusion &&
            ValueEquivalence.defEq(h.tpe, family) =>
        h
      case _ => fail(s"`${NatCodec.zeroName}` is not a nullary `Nat` constructor")
    }
    val succ = global(NatCodec.succName) match {
      case Some(h: ConstructorHead)
          if h.name == NatCodec.succName && h.totalArity == 1 && h.numErasedFamilyArgs == 0 && h.noConfusion =>
        h.tpe match {
          case pi: VPi if pi.binders.length == 1 =>
            val fresh = BinderOps.freshen(pi)
            val fieldTy = Interpreter.evalTerm(pi.binders.head.ty, pi.env)
            val outTy = pi.codomain(fresh)
            if (!ValueEquivalence.defEq(fieldTy, family) || !ValueEquivalence.defEq(outTy, family))
              fail(s"`${NatCodec.succName}` is not `Nat -> Nat`")
          case _ => fail(s"`${NatCodec.succName}` is not `Nat -> Nat`")
        }
        h
      case _ => fail(s"`${NatCodec.succName}` is not a unary `Nat` constructor")
    }
    // Force both constructor validations before issuing the otherwise opaque capability.
    val _ = (zero, succ)
    new ValidatedNatLayout(family)
  }

  private[raccoonlang] def validateNativeOpDeclaration(name: String, value: Value, env: Env): Unit =
    try validateNativeOpDeclaration0(name, value, env)
    catch {
      case mismatch: NativeOperationDeclarationMismatch => throw mismatch
      case error: TypeError =>
        throw NativeOperationDeclarationMismatch(name, error.msg, error.span)
      case NonFatal(error) =>
        throw NativeOperationDeclarationMismatch(name, Option(error.getMessage).getOrElse(error.toString))
    }

  private def validateNativeOpDeclaration0(name: String, value: Value, env: Env): Unit = {
    val spec = opsByName.getOrElse(name, return)
    def fail(reason: String): Nothing = throw NativeOperationDeclarationMismatch(name, reason)
    val lam = value match {
      case actual: VLam => actual
      case _            => fail("declaration is not a transparent applicable lambda")
    }
    lam.id match {
      case ValueId.Const(actual) if actual == name =>
      case _                                       => fail("lambda identity is not the exact reserved name")
    }
    val nat = env.globals.get(NatCodec.familyName).map(_.value(env)).getOrElse(fail("Nat is unavailable"))
    val (expectedResult, resultName) =
      if (spec.returnsBool)
        (env.globals.get("Bool").map(_.value(env)).getOrElse(fail("Bool is unavailable")), "Bool")
      else (nat, "Nat")
    lam.tpe match {
      case pi: VPi if pi.binders.length == 2 =>
        var telescopeEnv = pi.env
        pi.binders.foreach { binder =>
          if (binder.isImplicit) fail("expected two explicit telescope binders")
          val binderTy = Interpreter.evalTerm(binder.ty, telescopeEnv)
          if (!ValueEquivalence.defEq(binderTy, nat)) fail("expected telescope domain Nat -> Nat")
          val (_, fresh) = FreshVar.freshValue(binder.name, binderTy)
          telescopeEnv = telescopeEnv.putLocal(binder.localRef, fresh)
        }
        if (!ValueEquivalence.defEq(pi.codomain(telescopeEnv), expectedResult))
          fail(s"expected $resultName codomain")
      case _ => fail("expected a two-argument telescope")
    }
  }

  private[raccoonlang] def validateRequiredNativeOps(env: Env, profile: NativeBootstrapProfile): Unit =
    nativeNatOpSpecs.find(spec => spec.requiredBy(profile) && !env.globals.contains(spec.name)).foreach { spec =>
      throw MissingNativeOperation(spec.name, profile)
    }

  private def exactGlobal(env: Env, name: String, fail: String => Nothing): Value =
    env.globals.get(name).map(_.value(env)).getOrElse(fail(s"missing `$name`"))

  private final case class ConstructorShape(fieldTypes: Vector[Value], resultTy: Value)

  private def constructorShape(
      head: ConstructorHead,
      familyArgs: Vector[Value],
      fail: String => Nothing
  ): ConstructorShape =
    head.tpe match {
      case pi: VPi if pi.binders.length == head.totalArity && familyArgs.length == head.numErasedFamilyArgs =>
        var env = pi.env
        pi.binders.take(head.numErasedFamilyArgs).zip(familyArgs).foreach { case (binder, arg) =>
          env = BinderOps.bindValueAndCheck(env, binder, arg)
        }
        val fields = Vector.newBuilder[Value]
        pi.binders.drop(head.numErasedFamilyArgs).foreach { binder =>
          val fieldTy = Interpreter.evalTerm(binder.ty, env)
          fields += fieldTy
          val (_, fresh) = FreshVar.freshValue(binder.name, fieldTy)
          env = env.putLocal(binder.localRef, fresh)
        }
        ConstructorShape(fields.result(), pi.codomain(env))
      case _ => fail(s"`${head.name}` has an invalid constructor telescope")
    }

  /** Validate and issue the environment-independent descriptor for String literal peeling. */
  private[raccoonlang] def validateStringLayout(env: Env): ValidatedStringLayout =
    try validateStringLayout0(env)
    catch {
      case unavailable: StringLiteralUnavailable => throw unavailable
      case error: TypeError                      => throw StringLiteralUnavailable(error.msg, error.span)
      case NonFatal(error) =>
        throw StringLiteralUnavailable(Option(error.getMessage).getOrElse(error.toString))
    }

  private def validateStringLayout0(env: Env): ValidatedStringLayout = {
    def fail(reason: String): Nothing = throw StringLiteralUnavailable(reason)
    def requireClosed(name: String, value: Value): Unit =
      if (value.synDeps.nonEmpty) fail(s"`$name` is not closed")
    def inductive(label: String, expectedName: String, value: Value): InductiveMeta =
      TypeChecker.inductiveFamilyOf(value) match {
        case Some(instance)
            if instance.head.name == expectedName && !isPropositionType(value) &&
              ValueEquivalence.defEq(value.tpe, TypeTpe) =>
          instance.meta
        case _ => fail(s"`$label` is not the expected non-propositional Type-valued inductive instance")
      }
    def head(name: String): ConstructorHead =
      exactGlobal(env, name, fail) match {
        case actual: ConstructorHead if actual.name == name && actual.noConfusion => actual
        case _ => fail(s"`$name` is not the expected no-confusion constructor")
      }

    val nat = exactGlobal(env, NatCodec.familyName, fail)
    val char = exactGlobal(env, "Char", fail)
    val list = exactGlobal(env, "List", fail)
    val string = exactGlobal(env, "String", fail)
    inductive("Char", "Char", char)
    val syntheticSpan = Span(0, 0)
    val listChar = TypeChecker
      .checkTerm(
        CoreAst.Term.App(
          CoreAst.Term.GlobalRef("List", syntheticSpan),
          Vector(CoreAst.Term.GlobalRef("Char", syntheticSpan)),
          syntheticSpan
        ),
        env
      )
      .value
    val listMeta = inductive("List Char", "List", listChar)
    val stringMeta = inductive("String", "String", string)

    if (stringMeta.familyArity != 0 || stringMeta.constructorNames != Vector("String.mk"))
      fail("`String` does not have exactly the nullary family and `String.mk` constructor")
    val projection = stringMeta.projectionInfo.getOrElse(fail("`String` has no projection metadata"))
    if (!projection.etaEligible || projection.fieldCount != 1)
      fail("`String` is not an eta-eligible one-field structure")
    val stringMk = head("String.mk")
    if (!(projection.ctorHead eq stringMk) || stringMk.numErasedFamilyArgs != 0 || stringMk.totalArity != 1)
      fail("`String.mk` is not the installed sole one-field constructor")
    val stringShape = constructorShape(stringMk, Vector.empty, fail)
    if (stringShape.fieldTypes.length != 1 || !ValueEquivalence.defEq(stringShape.fieldTypes.head, listChar))
      fail("`String.mk` field is not `List Char`")
    if (!ValueEquivalence.defEq(stringShape.resultTy, string)) fail("`String.mk` result is not `String`")

    if (listMeta.constructorNames != Vector("List.nil", "List.cons"))
      fail("`List Char` does not have exactly `List.nil` and `List.cons`")
    if (listMeta.projectionInfo.exists(_.etaEligible)) fail("`List Char` is eta-eligible")
    val familyArgs = listChar match {
      case ConstSpine(head, args) if (head eq list) && args.length == listMeta.familyArity => args
      case _ => fail("`List Char` is not an exact family instance")
    }
    val nil = head("List.nil")
    val cons = head("List.cons")
    if (nil.numErasedFamilyArgs != familyArgs.length || cons.numErasedFamilyArgs != familyArgs.length)
      fail("List constructors do not erase exactly the family arguments")
    val nilShape = constructorShape(nil, familyArgs, fail)
    if (nilShape.fieldTypes.nonEmpty || !ValueEquivalence.defEq(nilShape.resultTy, listChar))
      fail("`List.nil` does not instantiate to `List Char`")
    val consShape = constructorShape(cons, familyArgs, fail)
    if (
      consShape.fieldTypes.length != 2 || !ValueEquivalence.defEq(consShape.fieldTypes(0), char) ||
      !ValueEquivalence
        .defEq(consShape.fieldTypes(1), listChar) || !ValueEquivalence.defEq(consShape.resultTy, listChar)
    ) fail("`List.cons` does not instantiate to `Char -> List Char -> List Char`")

    val charOfNat = exactGlobal(env, "Char.ofNat", fail)
    charOfNat match {
      case lam: VLam =>
        lam.id match {
          case ValueId.Const("Char.ofNat") =>
          case _                           => fail("`Char.ofNat` has the wrong identity")
        }
        lam.tpe match {
          case pi: VPi if pi.binders.length == 1 =>
            val domain = Interpreter.evalTerm(pi.binders.head.ty, pi.env)
            val fresh = BinderOps.freshen(pi)
            if (!ValueEquivalence.defEq(domain, nat) || !ValueEquivalence.defEq(pi.codomain(fresh), char))
              fail("`Char.ofNat` is not `Nat -> Char`")
          case _ => fail("`Char.ofNat` is not `Nat -> Char`")
        }
      case _ => fail("`Char.ofNat` is not a transparent applicable lambda")
    }

    Vector(
      "Nat" -> nat,
      "Char" -> char,
      "List Char" -> listChar,
      "Char.ofNat" -> charOfNat,
      "String" -> string,
      "String.mk" -> stringMk
    ).foreach { case (name, value) => requireClosed(name, value) }

    val codec = new CharListCodec(nat, char, listChar, charOfNat)
    new ValidatedStringLayout(string, stringMk, codec)
  }

  private[raccoonlang] def evalNatLit(value: BigInt, env: Env): Value =
    VPacked.nat(
      value,
      env.nativeLiterals.natLayout.getOrElse(throw NatLiteralUnavailable("no validated Nat layout")).natTpe
    )

  private[raccoonlang] def evalStrLit(scalars: Vector[Int], env: Env): Value = {
    val layout = env.nativeLiterals.stringLayout.getOrElse(throw StringLiteralUnavailable("no validated String layout"))
    val chars = VPacked.charList(layout.charListCodec, scalars)
    Interpreter.evalApply(layout.stringMk, Vector(chars))
  }
}
