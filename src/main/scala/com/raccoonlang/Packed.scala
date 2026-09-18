package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.util.DynamicVariable
import scala.util.control.NonFatal

/** Native literals: constructor folding, native Nat operations, and trusted-bootstrap validation. */
object Packed {

  /** Issued only after this object validates the complete native Nat family. */
  final class ValidatedNatLayout private[Packed] (val natTpe: Value)

  /** The kernel-owned identity, result kind, and equation of one native Nat operation. */
  sealed abstract class NativeNatOpSpec private[Packed] (val name: String) {
    private[raccoonlang] def returnsBool: Boolean
  }

  private final class NatOpSpec(name: String, val run: (BigInt, BigInt) => BigInt) extends NativeNatOpSpec(name) {
    override val returnsBool: Boolean = false
  }

  private final class BoolOpSpec(name: String, val run: (BigInt, BigInt) => Boolean) extends NativeNatOpSpec(name) {
    override val returnsBool: Boolean = true
  }

  private[raccoonlang] val MaxPowExponent: BigInt = BigInt(1) << 24
  private[raccoonlang] val MaxShiftLeft: BigInt = BigInt(1) << 24

  private def natSpec(name: String)(run: (BigInt, BigInt) => BigInt): NativeNatOpSpec = new NatOpSpec(name, run)

  private def boolSpec(name: String)(run: (BigInt, BigInt) => Boolean): NativeNatOpSpec = new BoolOpSpec(name, run)

  /** The sole source of native Nat identities, equations, and result types. */
  private[raccoonlang] val nativeNatOpSpecs: Vector[NativeNatOpSpec] = Vector(
    natSpec("Nat.add")(_ + _),
    natSpec("Nat.sub")((a, b) => (a - b).max(0)),
    natSpec("Nat.mul")(_ * _),
    natSpec("Nat.pow") { (a, b) =>
      if (b > MaxPowExponent) throw NativeOperationLimitExceeded("Nat.pow", b, MaxPowExponent)
      a.pow(b.toInt)
    },
    boolSpec("Nat.beq")(_ == _),
    boolSpec("Nat.ble")(_ <= _),
    boolSpec("Nat.blt")(_ < _),
    natSpec("Nat.div")((a, b) => if (b == 0) BigInt(0) else a / b),
    natSpec("Nat.mod")((a, b) => if (b == 0) a else a % b),
    natSpec("Nat.gcd")(_.gcd(_)),
    natSpec("Nat.land")(_ & _),
    natSpec("Nat.lor")(_ | _),
    natSpec("Nat.xor")(_ ^ _),
    natSpec("Nat.shiftLeft") { (a, count) =>
      if (a == 0) BigInt(0)
      else {
        if (count > MaxShiftLeft)
          throw NativeOperationLimitExceeded("Nat.shiftLeft", count, MaxShiftLeft)
        a << count.toInt
      }
    },
    natSpec("Nat.shiftRight") { (a, count) =>
      if (count >= a.bitLength) BigInt(0) else a >> count.toInt
    }
  )

  private val opsByName: Map[String, NativeNatOpSpec] = nativeNatOpSpecs.map(spec => spec.name -> spec).toMap
  require(opsByName.size == nativeNatOpSpecs.size, "Native Nat operation names must be unique")
  private[raccoonlang] val opNames: Set[String] = opsByName.keySet

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

  /**
   * Validate a trusted prelude's declaration of a native Nat operation and attach the native equation to that exact
   * lambda. Interception lives on the published value itself, so no name registry is consulted at application time: a
   * program can never obtain native semantics for a function it wrote.
   */
  private[raccoonlang] def nativeOp(name: String, value: Value, env: Env): Value = {
    validateNativeOpDeclaration(name, value, env)
    val spec = opsByName(name)
    val source = value.asInstanceOf[VLam]
    val nat = env(NatCodec.familyName)
    def fail(reason: String): Nothing = throw NativeOperationDeclarationMismatch(name, reason)
    def boolCtor(ctorName: String): Value =
      env.globals.get(ctorName).map(_.value(env)) match {
        case Some(h: ConstructorHead) if h.totalArity == 0 && h.noConfusion => VCtor(h, Vector.empty, h.tpe)
        case _ => fail(s"`$ctorName` is not a nullary constructor")
      }
    val compute: (BigInt, BigInt) => Value = spec match {
      case natOp: NatOpSpec => (a, b) => VPacked.nat(natOp.run(a, b), nat)
      case boolOp: BoolOpSpec =>
        val (yes, no) = (boolCtor("Bool.true"), boolCtor("Bool.false"))
        (a, b) => if (boolOp.run(a, b)) yes else no
    }
    val run: (Vector[Value], Env) => Value = (args, _) =>
      args match {
        case Vector(left: VPacked, right: VPacked)
            if opsEnabled.value && left.natValue.nonEmpty && right.natValue.nonEmpty =>
          compute(left.natValue.get, right.natValue.get)
        case _ => Interpreter.runLam(source, args)
      }
    VLam(source.tpe, source.id, LamBody.Native(run, Env.empty, isRawRecursive = false))
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
        // Each binder is validated to be exactly `Nat` before it is bound, so the freshening is
        // the ordinary one: `Nat` is neither eta-eligible nor propositional, and BinderOps.freshen
        // produces the same bare fresh Var this validation used to build by hand.
        var telescopeEnv = pi.env
        pi.binders.foreach { binder =>
          if (binder.isImplicit) fail("expected two explicit telescope binders")
          val binderTy = Interpreter.evalTerm(binder.ty, telescopeEnv)
          if (!ValueEquivalence.defEq(binderTy, nat)) fail("expected telescope domain Nat -> Nat")
          telescopeEnv = BinderOps.freshen(Vector(binder), telescopeEnv)
        }
        if (!ValueEquivalence.defEq(pi.codomain(telescopeEnv), expectedResult))
          fail(s"expected $resultName codomain")
      case _ => fail("expected a two-argument telescope")
    }
  }

  private def exactGlobal(env: Env, name: String, fail: String => Nothing): Value =
    env.globals.get(name).map(_.value(env)).getOrElse(fail(s"missing `$name`"))

  private final case class ConstructorShape(fieldTypes: Vector[Value], resultTy: Value)

  private final case class CharListInputs(
      listChar: Value,
      charListCodec: CharListCodec
  )

  private def constructorShape(
      head: ConstructorHead,
      familyArgs: Vector[Value],
      fail: String => Nothing
  ): ConstructorShape =
    head.tpe match {
      case pi: VPi if pi.binders.length == head.totalArity && familyArgs.length == head.numErasedFamilyArgs =>
        // Not head.fieldEnv: this validates a candidate prelude declaration, so each family
        // parameter is bound checked (bindValueAndCheck) rather than trusted.
        var env = head.paramBinders.zip(familyArgs).foldLeft(pi.env) { case (curEnv, (binder, arg)) =>
          BinderOps.bindValueAndCheck(curEnv, binder, arg)
        }
        val fields = Vector.newBuilder[Value]
        // Bare fresh Vars, deliberately: this is a purely structural shape check comparing field
        // types against expected ones, so struct-eta witnesses and canonical proofs would only
        // obscure what is being compared.
        head.fieldBinders.foreach { binder =>
          val fieldTy = Interpreter.evalTerm(binder.ty, env)
          fields += fieldTy
          val (_, fresh) = FreshVar.freshValue(binder.name, fieldTy)
          env = env.putLocal(binder.localRef, fresh)
        }
        ConstructorShape(fields.result(), pi.codomain(env))
      case _ => fail(s"`${head.name}` has an invalid constructor telescope")
    }

  private def inductive(
      label: String,
      expectedName: String,
      value: Value,
      fail: String => Nothing
  ): InductiveMeta =
    value match {
      case InductiveFamilyValue(instance)
          if instance.head.name == expectedName && !isPropositionType(value) &&
            ValueEquivalence.defEq(value.tpe, TypeTpe) =>
        instance.meta
      case _ => fail(s"`$label` is not the expected non-propositional Type-valued inductive instance")
    }

  private def constructorHead(env: Env, name: String, fail: String => Nothing): ConstructorHead =
    exactGlobal(env, name, fail) match {
      case actual: ConstructorHead if actual.name == name && actual.noConfusion => actual
      case _ => fail(s"`$name` is not the expected no-confusion constructor")
    }

  private def validateCharListInputs(env: Env, fail: String => Nothing): CharListInputs = {
    def requireClosed(name: String, value: Value): Unit =
      if (value.synDeps.nonEmpty) fail(s"`$name` is not closed")

    val nat = exactGlobal(env, NatCodec.familyName, fail)
    val char = exactGlobal(env, "Char", fail)
    val list = exactGlobal(env, "List", fail)
    inductive("Char", "Char", char, fail)
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
    val listMeta = inductive("List Char", "List", listChar, fail)
    if (listMeta.constructorNames != Vector("List.nil", "List.cons"))
      fail("`List Char` does not have exactly `List.nil` and `List.cons`")
    if (listMeta.projectionInfo.exists(_.etaEligible)) fail("`List Char` is eta-eligible")
    val familyArgs = listChar match {
      case ConstSpine(head, args) if (head eq list) && args.length == listMeta.familyArity => args
      case _ => fail("`List Char` is not an exact family instance")
    }
    val nil = constructorHead(env, "List.nil", fail)
    val cons = constructorHead(env, "List.cons", fail)
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

    Vector("Nat" -> nat, "Char" -> char, "List Char" -> listChar, "Char.ofNat" -> charOfNat).foreach {
      case (name, value) => requireClosed(name, value)
    }
    CharListInputs(listChar, new CharListCodec(nat, char, listChar, charOfNat))
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
    val inputs = validateCharListInputs(env, fail)
    val string = exactGlobal(env, "String", fail)
    val stringMeta = inductive("String", "String", string, fail)

    if (stringMeta.familyArity != 0 || stringMeta.constructorNames != Vector("String.mk"))
      fail("`String` does not have exactly the nullary family and `String.mk` constructor")
    val projection = stringMeta.projectionInfo.getOrElse(fail("`String` has no projection metadata"))
    if (!projection.etaEligible || projection.fieldCount != 1)
      fail("`String` is not an eta-eligible one-field structure")
    val stringMk = constructorHead(env, "String.mk", fail)
    if (!(projection.ctorHead eq stringMk) || stringMk.numErasedFamilyArgs != 0 || stringMk.totalArity != 1)
      fail("`String.mk` is not the installed sole one-field constructor")
    val stringShape = constructorShape(stringMk, Vector.empty, fail)
    if (stringShape.fieldTypes.length != 1 || !ValueEquivalence.defEq(stringShape.fieldTypes.head, inputs.listChar))
      fail("`String.mk` field is not `List Char`")
    if (!ValueEquivalence.defEq(stringShape.resultTy, string)) fail("`String.mk` result is not `String`")

    Vector(
      "String" -> string,
      "String.mk" -> stringMk
    ).foreach { case (name, value) => requireClosed(name, value) }

    new SourceStringLayout(string, stringMk, inputs.charListCodec)
  }

  private[raccoonlang] def evalNatLit(value: BigInt, env: Env): Value =
    VPacked.nat(
      value,
      env.nativeLiterals.natLayout.getOrElse(throw NatLiteralUnavailable("no validated Nat layout")).natTpe
    )

  private[raccoonlang] def evalStrLit(scalars: Vector[Int], env: Env): Value = {
    val layout = env.nativeLiterals.stringLayout.getOrElse(throw StringLiteralUnavailable("no validated String layout"))
    layout.eval(scalars)
  }
}
