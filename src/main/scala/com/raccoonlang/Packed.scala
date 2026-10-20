package com.raccoonlang

import com.raccoonlang.Value._
import com.raccoonlang.telescope.BinderOps

import scala.util.DynamicVariable
import scala.util.control.NonFatal

/** Native literals: constructor folding, native Nat operations, and trusted-bootstrap validation. */
object Packed {

  /** Issued only after this object validates the complete native Nat family. */
  final class ValidatedNatLayout private[Packed] (val natTpe: Value)

  /** Opaque operation identity issued only for a validated, published native Nat lambda. */
  private[raccoonlang] sealed trait ScalarNatKind
  private[raccoonlang] object ScalarNatKind {
    case object Add extends ScalarNatKind
    case object Sub extends ScalarNatKind
    case object Mul extends ScalarNatKind
    case object Div extends ScalarNatKind
    case object Mod extends ScalarNatKind
    case object Beq extends ScalarNatKind
    case object Ble extends ScalarNatKind
    case object Blt extends ScalarNatKind
  }

  final class ScalarNatCapability private[Packed] (
      private[raccoonlang] val kind: ScalarNatKind,
      private[raccoonlang] val natTpe: Value,
      private[raccoonlang] val yes: Value,
      private[raccoonlang] val no: Value,
      private val owner: () => VLam
  ) {
    private[Packed] def belongsTo(lam: VLam): Boolean =
      owner().asInstanceOf[AnyRef] eq lam.asInstanceOf[AnyRef]

  }

  /** Exact checked source body retained for constructor equations of one published native operation. */
  private[raccoonlang] final class NativeEquation private[Packed] (
      val source: VLam,
      private val owner: () => VLam
  ) {
    private[Packed] def belongsTo(lam: VLam): Boolean =
      owner().asInstanceOf[AnyRef] eq lam.asInstanceOf[AnyRef]

    private[raccoonlang] def inspect(nativeHead: VLam, args: Vector[Value]): Option[Value] =
      if (!belongsTo(nativeHead)) None
      else
        source.body match {
          case LamBody.Core(term, env) =>
            val selfName = source.id match {
              case ValueId.Const(name) => Some(name)
              case _                   => None
            }
            val peers = term.recursivePeers.map { case (_, name) =>
              if (selfName.contains(name)) nativeHead
              else env.globals.get(name).map(_.value(env)).getOrElse(wtf(s"Missing checked recursive peer $name"))
            }
            val nativePeers = peers.collect { case lam: VLam => lam }
            Some(withResidualNativeHeads(nativePeers) {
              Interpreter.runLamWithRecursivePeers(source, args, peers)
            })
          case _ => None
        }
  }

  /** Owner-checked native identity, independent of literal-layout finalization and runtime optimization flags. */
  private def nativeScalarCapability(lam: VLam): Option[ScalarNatCapability] =
    lam.body match {
      case native: LamBody.Native => native.scalarCapability.filter(_.belongsTo(lam))
      case _                      => None
    }

  /** Scalar execution also requires the current environment's literal layout and enabled optimization path. */
  private[raccoonlang] def scalarNatCapability(lam: VLam, env: Env): Option[ScalarNatCapability] =
    if (!opsEnabled.value || isResidualNativeHead(lam)) None
    else
      nativeScalarCapability(lam).filter(capability =>
        env.nativeLiterals.natLayout
          .exists(layout => layout.natTpe.asInstanceOf[AnyRef] eq capability.natTpe.asInstanceOf[AnyRef])
      )

  /** The kernel-owned identity, result kind, and equation of one native Nat operation. */
  sealed abstract class NativeNatOpSpec private[Packed] (val name: String) {
    private[raccoonlang] def returnsBool: Boolean
  }

  private final class NatOpSpec(
      name: String,
      val run: (BigInt, BigInt) => BigInt,
      val scalarKind: Option[ScalarNatKind]
  ) extends NativeNatOpSpec(name) {
    override val returnsBool: Boolean = false
  }

  private final class BoolOpSpec(
      name: String,
      val run: (BigInt, BigInt) => Boolean,
      val scalarKind: Option[ScalarNatKind]
  ) extends NativeNatOpSpec(name) {
    override val returnsBool: Boolean = true
  }

  private[raccoonlang] val MaxPowExponent: BigInt = BigInt(1) << 24
  private[raccoonlang] val MaxShiftLeft: BigInt = BigInt(1) << 24

  private def natSpec(name: String, scalarKind: Option[ScalarNatKind] = None)(
      run: (BigInt, BigInt) => BigInt
  ): NativeNatOpSpec = new NatOpSpec(name, run, scalarKind)

  private def boolSpec(name: String, scalarKind: Option[ScalarNatKind])(
      run: (BigInt, BigInt) => Boolean
  ): NativeNatOpSpec = new BoolOpSpec(name, run, scalarKind)

  /** The sole source of native Nat identities, equations, and result types. */
  private[raccoonlang] val nativeNatOpSpecs: Vector[NativeNatOpSpec] = Vector(
    natSpec("Nat.add", Some(ScalarNatKind.Add))(_ + _),
    natSpec("Nat.sub", Some(ScalarNatKind.Sub))((a, b) => (a - b).max(0)),
    natSpec("Nat.mul", Some(ScalarNatKind.Mul))(_ * _),
    natSpec("Nat.pow") { (a, b) =>
      if (b > MaxPowExponent) fail(NativeOperationLimitExceeded("Nat.pow", b, MaxPowExponent))
      a.pow(b.toInt)
    },
    boolSpec("Nat.beq", Some(ScalarNatKind.Beq))(_ == _),
    boolSpec("Nat.ble", Some(ScalarNatKind.Ble))(_ <= _),
    boolSpec("Nat.blt", Some(ScalarNatKind.Blt))(_ < _),
    natSpec("Nat.div", Some(ScalarNatKind.Div))((a, b) => if (b == 0) BigInt(0) else a / b),
    natSpec("Nat.mod", Some(ScalarNatKind.Mod))((a, b) => if (b == 0) a else a % b),
    natSpec("Nat.gcd")(_.gcd(_)),
    natSpec("Nat.land")(_ & _),
    natSpec("Nat.lor")(_ | _),
    natSpec("Nat.xor")(_ ^ _),
    natSpec("Nat.shiftLeft") { (a, count) =>
      if (a == 0) BigInt(0)
      else {
        if (count > MaxShiftLeft)
          fail(NativeOperationLimitExceeded("Nat.shiftLeft", count, MaxShiftLeft))
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
  private val residualNativeHeads = new DynamicVariable[Vector[VLam]](Vector.empty)
  private[raccoonlang] def withOpsDisabled[A](body: => A): A = opsEnabled.withValue(false)(body)

  private def withResidualNativeHeads[A](heads: Vector[VLam])(body: => A): A = {
    val combined = residualNativeHeads.value ++ heads.filterNot(head => residualNativeHeads.value.exists(_ eq head))
    residualNativeHeads.withValue(combined)(body)
  }

  private[raccoonlang] def isResidualNativeHead(lam: VLam): Boolean = residualNativeHeads.value.exists(_ eq lam)

  private[raccoonlang] def nativeEquation(lam: VLam): Option[NativeEquation] =
    lam.body match {
      case LamBody.Native(_, _, false, _, Some(equation)) if equation.belongsTo(lam) => Some(equation)
      case _                                                                         => None
    }

  private val StringAppendName = "String.append"
  private val StringDataName = "String.data"
  private val StringMkName = "String.mk"
  private val ListAppendName = "List.append"

  /** Opaque proof that every scalar was validated while extracting a String through its trusted layout. */
  private[raccoonlang] final class ValidatedCharScalars private[Packed] (
      private[raccoonlang] val codec: CharListCodec,
      private[raccoonlang] val values: Vector[Int]
  )

  /** A constructor applied to its stored fields at `tpe`: packed where it is literal data, and canonical as a proof. */
  private[raccoonlang] def construct(head: ConstructorHead, storedArgs: Vector[Value], tpe: Value): Value =
    Value.canonicalizeProof(foldCtor(head, storedArgs, tpe).getOrElse(VCtor(head, storedArgs, tpe)))

  /** Canonical Nat successor-prefix construction shared by evaluation and materialization. */
  private[raccoonlang] def natPrefix(base: Value, offset: BigInt, tpe: Value): Value = {
    require(offset >= 0, s"Nat successor-prefix offset must be non-negative: $offset")
    if (offset == 0) base
    else {
      require(tpe.synDeps.isEmpty, s"Nat successor-prefix type must be closed, got ${tpe.synDeps}")
      require(!Sorts.isProposition(tpe), s"Nat successor-prefix type must be data, got $tpe")
      require(ValueEquivalence.defEq(base.tpe, tpe), s"Nat successor-prefix base has type ${base.tpe}, expected $tpe")
      base match {
        case packed: VPacked if (packed.codec eq NatCodec) && ValueEquivalence.defEq(packed.tpe, tpe) =>
          VPacked.nat(packed.natValue.get + offset, tpe)
        case prefix: VNatPrefix if ValueEquivalence.defEq(prefix.tpe, tpe) =>
          natPrefix(prefix.base, prefix.offset + offset, tpe)
        case _ => Value.VNatPrefix.node(base, offset, tpe)
      }
    }
  }

  /** One successor layer of a compact prefix, with its predecessor kept compact. */
  private[raccoonlang] def natPrefixHead(prefix: VNatPrefix): (String, Vector[Value]) =
    (NatCodec.succName, Vector(natPrefix(prefix.base, prefix.offset - 1, prefix.tpe)))

  /** A shared compact count/base view of packed and ordinary Nat constructors. */
  private[raccoonlang] def natConstructorParts(value: Value): Option[(BigInt, Value)] =
    value match {
      case packed: VPacked if packed.codec eq NatCodec =>
        Some(packed.natValue.get -> VPacked.nat(0, packed.tpe))
      case prefix: VNatPrefix => Some(prefix.offset -> prefix.base)
      case _ =>
        ConstructorForm.Stored.unapply(value).flatMap {
          case (NatCodec.zeroName, Vector())            => Some(BigInt(0) -> VPacked.nat(0, value.tpe))
          case (NatCodec.succName, Vector(predecessor)) => Some(BigInt(1) -> predecessor)
          case _                                        => None
        }
    }

  private[raccoonlang] def foldCtor(
      head: ConstructorHead,
      storedArgs: Vector[Value],
      tpe: Value
  ): Option[Value] =
    head.name match {
      case NatCodec.zeroName
          if head.totalArity == 0 && storedArgs.isEmpty && head.noConfusion &&
            !Sorts.isProposition(tpe) && tpe.synDeps.isEmpty =>
        Some(VPacked.nat(0, tpe))
      case NatCodec.succName
          if head.totalArity == 1 && head.numErasedFamilyArgs == 0 && head.noConfusion &&
            !Sorts.isProposition(tpe) && tpe.synDeps.isEmpty =>
        storedArgs match {
          case Vector(base) if ValueEquivalence.defEq(base.tpe, tpe) => Some(natPrefix(base, 1, tpe))
          case _                                                     => None
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
    def reject(reason: String): Nothing = fail(NativeOperationDeclarationMismatch(name, reason))
    def boolCtor(ctorName: String): Value =
      env.globals.get(ctorName).map(_.value(env)) match {
        case Some(h: ConstructorHead) if h.totalArity == 0 && h.noConfusion => VCtor(h, Vector.empty, h.tpe)
        case _ => reject(s"`$ctorName` is not a nullary constructor")
      }
    var boolYes: Value = null
    var boolNo: Value = null
    val (compute, resultTy): ((BigInt, BigInt) => Value, Value) = spec match {
      case natOp: NatOpSpec => ((a, b) => VPacked.nat(natOp.run(a, b), nat), nat)
      case boolOp: BoolOpSpec =>
        val (yes, no) = (boolCtor("Bool.true"), boolCtor("Bool.false"))
        boolYes = yes
        boolNo = no
        ((a, b) => if (boolOp.run(a, b)) yes else no, yes.tpe)
    }
    lazy val scalarCapability = spec match {
      case natOp: NatOpSpec =>
        natOp.scalarKind.map(kind => new ScalarNatCapability(kind, nat, null, null, () => self))
      case boolOp: BoolOpSpec =>
        boolOp.scalarKind.map(kind => new ScalarNatCapability(kind, nat, boolYes, boolNo, () => self))
    }
    lazy val equation = new NativeEquation(source, () => self)
    def residual(args: Vector[Value]): Value = {
      val blockedOn = args.foldLeft(DepSet.empty) {
        case (deps, Blocker(argDeps)) => deps ++ argDeps
        case (deps, _)                => deps
      }
      Value.canonicalizeProof(VApp(self, args, resultTy, blockedOn))
    }

    def exactZero(value: Value): Boolean =
      ValueEquivalence.defEq(value.tpe, nat) && natConstructorParts(value).exists(_._1 == 0)

    /** A known successor prefix, represented as its numeric offset and the value below it. */
    def prefixParts(value: Value): Option[(BigInt, Value)] =
      Option.when(ValueEquivalence.defEq(value.tpe, nat))(natConstructorParts(value)).flatten

    lazy val validatedBle: Option[VLam] =
      env.globals.get("Nat.ble").map(_.value(env)).collect {
        case lam: VLam
            if nativeScalarCapability(lam).exists(capability =>
              capability.kind == ScalarNatKind.Ble &&
                (capability.natTpe.asInstanceOf[AnyRef] eq nat.asInstanceOf[AnyRef])
            ) =>
          lam
      }

    def compare(beq: Boolean, left: Value, right: Value): Option[Value] = {
      if (!beq && exactZero(left)) Some(boolYes)
      else if (beq && exactZero(left) && exactZero(right)) Some(boolYes)
      else if (exactZero(left) && prefixParts(right).exists(_._1 > 0)) Some(boolNo)
      else if (exactZero(right) && prefixParts(left).exists(_._1 > 0)) Some(boolNo)
      else
        (prefixParts(left), prefixParts(right)) match {
          case (Some((leftCount, leftBase)), Some((rightCount, rightBase))) =>
            val common = leftCount.min(rightCount)
            if (common > 0) {
              val leftRest = natPrefix(leftBase, leftCount - common, nat)
              val rightRest = natPrefix(rightBase, rightCount - common, nat)
              compact(Vector(leftRest, rightRest))
            } else None
          case _ => None
        }
    }

    def compact(args: Vector[Value]): Option[Value] =
      args match {
        case Vector(left, right) =>
          (left, right) match {
            case (packedLeft: VPacked, packedRight: VPacked)
                if opsEnabled.value && (packedLeft.codec eq NatCodec) && (packedRight.codec eq NatCodec) &&
                  ValueEquivalence.defEq(packedLeft.tpe, nat) && ValueEquivalence.defEq(packedRight.tpe, nat) =>
              Some(compute(packedLeft.natValue.get, packedRight.natValue.get))
            case _ =>
              spec.name match {
                case "Nat.add" =>
                  prefixParts(right).map { case (count, suffix) =>
                    if (count == 0) left
                    else if (exactZero(suffix)) natPrefix(left, count, nat)
                    else residual(Vector(natPrefix(left, count, nat), suffix))
                  }

                case "Nat.sub" => Option.when(exactZero(right))(left)
                case "Nat.mul" => Option.when(exactZero(right))(VPacked.nat(0, nat))
                case "Nat.pow" => Option.when(exactZero(right))(VPacked.nat(1, nat))
                case "Nat.beq" => compare(beq = true, left, right)
                case "Nat.ble" => compare(beq = false, left, right)
                case "Nat.blt" =>
                  validatedBle.map(le => Interpreter.evalApply(le, Vector(natPrefix(left, 1, nat), right)))
                case _ => None
              }
          }
        case _ => wtf(s"Validated native Nat operation $name was applied to ${args.length} arguments")
      }

    lazy val self: VLam =
      VLam(
        source.tpe,
        source.id,
        LamBody.Native(
          (args, _) =>
            if (isResidualNativeHead(self)) compact(args).getOrElse(residual(args))
            else if (!opsEnabled.value) Interpreter.runLam(source, args)
            else compact(args).getOrElse(residual(args)),
          Env.empty,
          isRawRecursive = false,
          scalarCapability = scalarCapability,
          equation = Some(equation)
        )
      )
    self
  }

  private[raccoonlang] def validateNatFamily(env: Env): ValidatedNatLayout = {
    def reject(reason: String): Nothing = fail(NatLiteralUnavailable(reason))
    def global(name: String): Option[Value] = env.globals.get(name).map(_.value(env))

    val family = global(NatCodec.familyName).getOrElse(reject("no `Nat` in scope"))
    family match {
      case VConst(NatCodec.familyName, Inductive(meta), _)
          if meta.familyArity == 0 && meta.constructorNames == Vector(NatCodec.zeroName, NatCodec.succName) =>
        // A literal builds its value from `zero` and `succ` wherever it is written, which a seal forbids (spec §7.1).
        if (meta.seal.nonEmpty) reject("`Nat` is sealed")
      case _ => reject("`Nat` in scope is not the two-constructor unary inductive")
    }
    if (!ValueEquivalence.defEq(family.tpe, Sorts.Type)) reject("`Nat` in scope is not Type-valued")
    val zero = global(NatCodec.zeroName) match {
      case Some(h: ConstructorHead)
          if h.name == NatCodec.zeroName && h.totalArity == 0 && h.noConfusion &&
            ValueEquivalence.defEq(h.tpe, family) =>
        h
      case _ => reject(s"`${NatCodec.zeroName}` is not a nullary `Nat` constructor")
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
              reject(s"`${NatCodec.succName}` is not `Nat -> Nat`")
          case _ => reject(s"`${NatCodec.succName}` is not `Nat -> Nat`")
        }
        h
      case _ => reject(s"`${NatCodec.succName}` is not a unary `Nat` constructor")
    }
    // Force both constructor validations before issuing the otherwise unchecked capability.
    val _ = (zero, succ)
    new ValidatedNatLayout(family)
  }

  private[raccoonlang] def validateNativeOpDeclaration(name: String, value: Value, env: Env): Unit =
    try validateNativeOpDeclaration0(name, value, env)
    catch {
      // Anything that goes wrong while validating this declaration is a fact about the declaration, so it is reported
      // as one mismatch. A mismatch raised inside is already that, and keeps its own location.
      case diagnostic: Diagnostic =>
        diagnostic.error match {
          case _: NativeOperationDeclarationMismatch => throw diagnostic
          case error =>
            throw diagnostic.copy(error =
              NativeOperationDeclarationMismatch(name, ErrorRendering.render(error, env.nativeLiterals.stringLayout))
            )
        }
      // A broken kernel invariant is not a fact about this declaration; let it through untouched.
      case internal: InternalError => throw internal
      case NonFatal(error) =>
        fail(NativeOperationDeclarationMismatch(name, Option(error.getMessage).getOrElse(error.toString)))
    }

  private def validateNativeOpDeclaration0(name: String, value: Value, env: Env): Unit = {
    val spec = opsByName.getOrElse(name, return)
    def reject(reason: String): Nothing = fail(NativeOperationDeclarationMismatch(name, reason))
    val lam = value match {
      case actual: VLam => actual
      case _            => reject("declaration is not an applicable lambda")
    }
    lam.id match {
      case ValueId.Const(actual) if actual == name =>
      case _                                       => reject("lambda identity is not the exact reserved name")
    }
    val nat = env.globals.get(NatCodec.familyName).map(_.value(env)).getOrElse(reject("Nat is unavailable"))
    val (expectedResult, resultName) =
      if (spec.returnsBool)
        (env.globals.get("Bool").map(_.value(env)).getOrElse(reject("Bool is unavailable")), "Bool")
      else (nat, "Nat")
    lam.tpe match {
      case pi: VPi if pi.binders.length == 2 =>
        // Each binder is validated to be exactly `Nat` before it is bound, so the freshening is
        // the ordinary one: `Nat` is neither eta-eligible nor propositional, and BinderOps.freshen
        // produces the same bare fresh Var this validation used to build by hand.
        var telescopeEnv = pi.env
        pi.binders.foreach { binder =>
          if (binder.mode != BinderMode.Explicit) reject("expected two explicit telescope binders")
          val binderTy = Interpreter.evalTerm(binder.ty, telescopeEnv)
          if (!ValueEquivalence.defEq(binderTy, nat)) reject("expected telescope domain Nat -> Nat")
          telescopeEnv = BinderOps.freshen(Vector(binder), telescopeEnv)
        }
        if (!ValueEquivalence.defEq(pi.codomain(telescopeEnv), expectedResult))
          reject(s"expected $resultName codomain")
      case _ => reject("expected a two-argument telescope")
    }
  }

  private def exactGlobal(env: Env, name: String, reject: String => Nothing): Value =
    env.globals.get(name).map(_.value(env)).getOrElse(reject(s"missing `$name`"))

  private final case class ConstructorShape(fieldTypes: Vector[Value], resultTy: Value)

  private final case class CharListInputs(
      listChar: Value,
      charListCodec: CharListCodec
  )

  private def constructorShape(
      head: ConstructorHead,
      familyArgs: Vector[Value],
      reject: String => Nothing
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
      case _ => reject(s"`${head.name}` has an invalid constructor telescope")
    }

  private def inductive(
      label: String,
      expectedName: String,
      value: Value,
      reject: String => Nothing
  ): InductiveMeta =
    value match {
      case InductiveFamilyValue(instance)
          if instance.head.name == expectedName && !Sorts.isProposition(value) &&
            ValueEquivalence.defEq(value.tpe, Sorts.Type) =>
        // A literal makes values of the layout's families wherever it is written, and a sealed family's are its
        // module's to make (spec §7.1).
        if (instance.meta.seal.nonEmpty) reject(s"`$label` is sealed")
        instance.meta
      case _ => reject(s"`$label` is not the expected non-propositional Type-valued inductive instance")
    }

  private def constructorHead(env: Env, name: String, reject: String => Nothing): ConstructorHead =
    exactGlobal(env, name, reject) match {
      case actual: ConstructorHead if actual.name == name && actual.noConfusion => actual
      case _ => reject(s"`$name` is not the expected no-confusion constructor")
    }

  private def validateCharListInputs(env: Env, reject: String => Nothing): CharListInputs = {
    def requireClosed(name: String, value: Value): Unit =
      if (value.synDeps.nonEmpty) reject(s"`$name` is not closed")

    val nat = exactGlobal(env, NatCodec.familyName, reject)
    val char = exactGlobal(env, "Char", reject)
    val list = exactGlobal(env, "List", reject)
    inductive("Char", "Char", char, reject)
    val syntheticSpan = Span(0, 0)
    val listChar = TypeChecker
      .checkTerm(
        CoreAst.Term.App(
          CoreAst.Term.GlobalRef("List", syntheticSpan),
          Vector(CoreAst.Term.GlobalRef("Char", syntheticSpan)),
          Vector.empty,
          syntheticSpan
        ),
        env
      )
      .value
    val listMeta = inductive("List Char", "List", listChar, reject)
    if (listMeta.constructorNames != Vector("List.nil", "List.cons"))
      reject("`List Char` does not have exactly `List.nil` and `List.cons`")
    if (listMeta.projectionInfo.exists(_.etaEligible)) reject("`List Char` is eta-eligible")
    val familyArgs = listChar match {
      case ConstSpine(head, args) if (head eq list) && args.length == listMeta.familyArity => args
      case _ => reject("`List Char` is not an exact family instance")
    }
    val nil = constructorHead(env, "List.nil", reject)
    val cons = constructorHead(env, "List.cons", reject)
    if (nil.numErasedFamilyArgs != familyArgs.length || cons.numErasedFamilyArgs != familyArgs.length)
      reject("List constructors do not erase exactly the family arguments")
    val nilShape = constructorShape(nil, familyArgs, reject)
    if (nilShape.fieldTypes.nonEmpty || !ValueEquivalence.defEq(nilShape.resultTy, listChar))
      reject("`List.nil` does not instantiate to `List Char`")
    val consShape = constructorShape(cons, familyArgs, reject)
    if (
      consShape.fieldTypes.length != 2 || !ValueEquivalence.defEq(consShape.fieldTypes(0), char) ||
      !ValueEquivalence
        .defEq(consShape.fieldTypes(1), listChar) || !ValueEquivalence.defEq(consShape.resultTy, listChar)
    ) reject("`List.cons` does not instantiate to `Char -> List Char -> List Char`")

    val charOfNat = exactGlobal(env, "Char.ofNat", reject)
    charOfNat match {
      case lam: VLam =>
        lam.id match {
          case ValueId.Const("Char.ofNat") =>
          case _                           => reject("`Char.ofNat` has the wrong identity")
        }
        lam.tpe match {
          case pi: VPi if pi.binders.length == 1 =>
            val domain = Interpreter.evalTerm(pi.binders.head.ty, pi.env)
            val fresh = BinderOps.freshen(pi)
            if (!ValueEquivalence.defEq(domain, nat) || !ValueEquivalence.defEq(pi.codomain(fresh), char))
              reject("`Char.ofNat` is not `Nat -> Char`")
          case _ => reject("`Char.ofNat` is not `Nat -> Char`")
        }
      case _ => reject("`Char.ofNat` is not an applicable lambda")
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
      // Any failure here means the same thing to a program: this environment has no usable String layout.
      case diagnostic: Diagnostic =>
        diagnostic.error match {
          case _: StringLiteralUnavailable => throw diagnostic
          case error =>
            throw diagnostic.copy(error =
              StringLiteralUnavailable(ErrorRendering.render(error, env.nativeLiterals.stringLayout))
            )
        }
      // A broken kernel invariant is not a fact about the layout; let it through untouched.
      case internal: InternalError => throw internal
      case NonFatal(error) =>
        fail(StringLiteralUnavailable(Option(error.getMessage).getOrElse(error.toString)))
    }

  private def validateStringLayout0(env: Env): ValidatedStringLayout = {
    def reject(reason: String): Nothing = fail(StringLiteralUnavailable(reason))
    def requireClosed(name: String, value: Value): Unit =
      if (value.synDeps.nonEmpty) reject(s"`$name` is not closed")
    val inputs = validateCharListInputs(env, reject)
    val string = exactGlobal(env, "String", reject)
    val stringMeta = inductive("String", "String", string, reject)

    if (stringMeta.familyArity != 0 || stringMeta.constructorNames != Vector("String.mk"))
      reject("`String` does not have exactly the nullary family and `String.mk` constructor")
    val projection = stringMeta.projectionInfo.getOrElse(reject("`String` has no projection metadata"))
    if (!projection.etaEligible || projection.fieldCount != 1)
      reject("`String` is not an eta-eligible one-field structure")
    val stringMk = constructorHead(env, "String.mk", reject)
    if (!(projection.ctorHead eq stringMk) || stringMk.numErasedFamilyArgs != 0 || stringMk.totalArity != 1)
      reject("`String.mk` is not the installed sole one-field constructor")
    val stringShape = constructorShape(stringMk, Vector.empty, reject)
    if (stringShape.fieldTypes.length != 1 || !ValueEquivalence.defEq(stringShape.fieldTypes.head, inputs.listChar))
      reject("`String.mk` field is not `List Char`")
    if (!ValueEquivalence.defEq(stringShape.resultTy, string)) reject("`String.mk` result is not `String`")

    Vector(
      "String" -> string,
      "String.mk" -> stringMk
    ).foreach { case (name, value) => requireClosed(name, value) }

    // Found once, by applying `Char.ofNat` to a fresh variable, so that printing never evaluates.
    val scalar = FreshVar.freshVar("value", inputs.charListCodec.natTpe)
    val charConstructor = Interpreter.evalApply(inputs.charListCodec.charOfNat, Vector(scalar)) match {
      case VCtor(head, Vector(Var(_, id, _)), _) if id == scalar.id => Some(head.name)
      case _                                                        => None
    }
    new SourceStringLayout(string, stringMk, inputs.charListCodec, charConstructor)
  }

  private[raccoonlang] def evalNatLit(value: BigInt, env: Env): Value =
    VPacked.nat(
      value,
      env.nativeLiterals.natLayout.getOrElse(fail(NatLiteralUnavailable("no validated Nat layout"))).natTpe
    )

  private[raccoonlang] def evalStrLit(scalars: Vector[Int], env: Env): Value = {
    val layout = env.nativeLiterals.stringLayout.getOrElse(fail(StringLiteralUnavailable("no validated String layout")))
    layout.eval(scalars)
  }

  /**
   * Attach the packed String.append equation only to the exact checked declarations that implement it. This runs once
   * at trusted-prelude completion, after the final String layout has been validated and installed. An unrecognized
   * trusted prelude remains usable: its original source declaration stays in place and keeps its source semantics.
   */
  private[raccoonlang] def attachStringAppend(env: Env): Env =
    (
      env.nativeLiterals.stringLayout,
      env.globals.get(StringAppendName),
      env.globals.get(ListAppendName),
      env.globals.get(StringDataName),
      env.globals.get(StringMkName)
    ) match {
      case (
            Some(layout: SourceStringLayout),
            Some(stringBinding),
            Some(listBinding),
            Some(dataBinding),
            Some(mkBinding)
          ) if layout.charConstructor.nonEmpty =>
        val stringAppend = stringBinding.value(env)
        val listAppend = listBinding.value(env)
        val stringData = dataBinding.value(env)
        val stringMk = mkBinding.value(env)
        (stringAppend, listAppend, stringData, stringMk) match {
          case (source: VLam, listLam: VLam, dataLam: VLam, mk: ConstructorHead)
              if (mk eq layout.stringMk) && validatesStringAppend(source) && validatesListAppend(listLam) &&
                validatesStringData(dataLam, layout) &&
                capturesGlobalBinding(source, StringDataName, dataBinding) &&
                capturesGlobalBinding(source, ListAppendName, listBinding) &&
                capturesGlobalBinding(source, StringMkName, mkBinding) &&
                capturesGlobalBinding(dataLam, StringMkName, mkBinding) =>
            val native = nativeStringAppend(source, layout, layout.charConstructor.get)
            Env.assertClosedGlobal(native)
            Env.assertCanonicalProof(native)
            env.copy(globals = env.globals.updated(StringAppendName, GlobalBinding.Strict(native)))
          case _ => env
        }
      case _ => env
    }

  private def nativeStringAppend(source: VLam, layout: SourceStringLayout, charConstructor: String): VLam =
    VLam(
      source.tpe,
      source.id,
      LamBody.Native(
        (args, _) =>
          args match {
            case Vector(left, right) if opsEnabled.value =>
              (stringScalars(left, layout), stringScalars(right, layout)) match {
                case (Some(leftData), Some(_)) if leftData.scalars.isEmpty => right
                case (Some(leftData), Some(rightData)) =>
                  val display = CharListAppendDisplay(
                    leftData.scalars.length + rightData.constructorPrefixLength,
                    rightData.hasPackedSuffix,
                    charConstructor
                  )
                  val chars = VPacked.charList(
                    layout.charListCodec,
                    concatValidatedCharScalars(leftData, rightData),
                    Some(display)
                  )
                  layout.evalAppended(chars)
                case _ => Interpreter.runLam(source, args)
              }
            case _ => Interpreter.runLam(source, args)
          },
        Env.empty,
        isRawRecursive = false,
        scalarCapability = None,
        equation = None
      )
    )

  /** The ground String shapes the native equation may decode under this exact validated source layout. */
  private final case class StringScalars(
      scalars: Vector[Int],
      codec: CharListCodec,
      constructorPrefixLength: Int,
      hasPackedSuffix: Boolean
  )

  /** The only minting path: both private shape records come from extraction that checked every ordinary Char. */
  private def concatValidatedCharScalars(
      left: StringScalars,
      right: StringScalars
  ): ValidatedCharScalars = {
    require(left.codec eq right.codec, "Cannot concatenate CharLists from different validated layouts")
    new ValidatedCharScalars(left.codec, left.scalars ++ right.scalars)
  }

  private def stringScalars(value: Value, layout: SourceStringLayout): Option[StringScalars] =
    value match {
      case VCtor(head, Vector(data), tpe)
          if (head eq layout.stringMk) && ValueEquivalence.defEq(tpe, layout.stringTpe) =>
        charListScalars(data, layout.charListCodec, layout.charConstructor)
      case _ => None
    }

  /**
   * Read a literal scalar list, or a source List.cons spine whose characters are exactly the validated Char.ofNat
   * constructor over packed Unicode scalars. The latter covers small formatted strings such as Text.nat while leaving
   * arbitrary Char values, neutral suffixes and unusual Char.ofNat definitions to the source evaluator.
   */
  private def charListScalars(
      value: Value,
      codec: CharListCodec,
      charConstructor: Option[String]
  ): Option[StringScalars] =
    value match {
      // The all-packed case is common after the first append. Reuse its immutable vector and display metadata directly;
      // do not allocate a builder merely to copy the same scalars back into another Vector.
      case packed: VPacked if packed.codec eq codec =>
        packed.charScalars.map { scalars =>
          packed.charListAppendDisplay match {
            case Some(display) =>
              StringScalars(scalars, codec, display.prefixLength, display.hasPackedSuffix)
            case None =>
              StringScalars(scalars, codec, 0, hasPackedSuffix = true)
          }
        }
      case _ =>
        val scalars = Vector.newBuilder[Int]
        var constructorPrefixLength = 0
        var rest = value
        while (true) {
          rest match {
            case packed: VPacked if packed.codec eq codec =>
              return packed.charScalars.map { tail =>
                scalars ++= tail
                val allScalars = scalars.result()
                packed.charListAppendDisplay match {
                  case Some(display) =>
                    StringScalars(
                      allScalars,
                      codec,
                      constructorPrefixLength + display.prefixLength,
                      display.hasPackedSuffix
                    )
                  case None =>
                    StringScalars(
                      allScalars,
                      codec,
                      constructorPrefixLength,
                      hasPackedSuffix = true
                    )
                }
              }
            case VCtor(head, Vector(), tpe)
                if head.name == "List.nil" && head.noConfusion &&
                  head.totalArity == head.numErasedFamilyArgs &&
                  ValueEquivalence.defEq(tpe, codec.listCharTpe) =>
              return Some(
                StringScalars(
                  scalars.result(),
                  codec,
                  constructorPrefixLength,
                  hasPackedSuffix = false
                )
              )
            case VCtor(head, Vector(char, tail), tpe)
                if head.name == "List.cons" && head.noConfusion &&
                  head.totalArity - head.numErasedFamilyArgs == 2 &&
                  ValueEquivalence.defEq(tpe, codec.listCharTpe) =>
              scalarOfKnownChar(char, codec, charConstructor) match {
                case Some(scalar) =>
                  scalars += scalar
                  constructorPrefixLength += 1
                  rest = tail
                case None => return None
              }
            case _ => return None
          }
        }
        None
    }

  private def scalarOfKnownChar(value: Value, codec: CharListCodec, charConstructor: Option[String]): Option[Int] =
    charConstructor.flatMap { constructorName =>
      value match {
        case VCtor(head, Vector(code: VPacked), tpe)
            if head.name == constructorName && head.noConfusion &&
              head.totalArity - head.numErasedFamilyArgs == 1 &&
              ValueEquivalence.defEq(tpe, codec.charTpe) && (code.codec eq NatCodec) &&
              ValueEquivalence.defEq(code.tpe, codec.natTpe) =>
          code.natValue
            .filter(_.isValidInt)
            .map(_.toInt)
            .filter(UnicodeScalarString.isScalar)
        case _ => None
      }
    }

  private def validatesStringAppend(source: VLam): Boolean = {
    val exactIdentity = source.id match {
      case ValueId.Const(StringAppendName) => true
      case _                               => false
    }
    val exactTelescope =
      source.tpe.binders.length == 2 && source.tpe.binders.forall(_.mode == BinderMode.Explicit)
    (exactIdentity, exactTelescope, source.body) match {
      case (true, true, LamBody.Core(term, _))
          if term.recursion.isEmpty && term.recursivePeers.isEmpty &&
            term.ty.binders.length == 2 && term.ty.binders.forall(_.mode == BinderMode.Explicit) =>
        val a = term.ty.binders(0).localRef
        val b = term.ty.binders(1).localRef
        stripEmptyBodies(term.body) match {
          case CoreAst.Term.App(CoreAst.Term.GlobalRef("String.mk", _), Vector(data), evidence, _)
              if evidence.isEmpty =>
            stripEmptyBodies(data) match {
              case CoreAst.Term.App(CoreAst.Term.GlobalRef("List.append", _), Vector(left, right), evidence0, _)
                  if evidence0.isEmpty =>
                isSelectorOf(left, StringDataName, a) && isSelectorOf(right, StringDataName, b)
              case _ => false
            }
          case _ => false
        }
      case _ => false
    }
  }

  /** Validate the exact generated projection equation used by `String.append`, not its global name alone. */
  private def validatesStringData(source: VLam, layout: SourceStringLayout): Boolean = {
    val exactIdentity = source.id match {
      case ValueId.Const(StringDataName) => true
      case _                             => false
    }
    val exactTelescope =
      source.tpe.binders.length == 1 && source.tpe.binders.head.mode == BinderMode.Explicit
    (exactIdentity, exactTelescope, source.body) match {
      case (true, true, LamBody.Core(term, _))
          if term.recursion.isEmpty && term.recursivePeers.isEmpty &&
            term.ty.binders.length == 1 && term.ty.binders.head.mode == BinderMode.Explicit =>
        val self = term.ty.binders.head.localRef
        stripEmptyBodies(term.body) match {
          case CoreAst.Term.Match(
                CoreAst.Term.LocalRef(scrutinee, _),
                _,
                Vector(singleCase),
                None,
                None,
                _,
                _
              ) if scrutinee == self =>
            singleCase.ctorName == layout.stringMk.name && singleCase.patternVars.length == 1 &&
            isLocalRef(stripEmptyBodies(singleCase.body), singleCase.patternVars.head.ref)
          case _ => false
        }
      case _ => false
    }
  }

  /**
   * A checked source lambda resolves globals through its captured persistent environment, not the final environment
   * passed to evaluation. `Env.putGlobal` rejects duplicate names, and env copies preserve each `GlobalBinding` object,
   * so identity here proves that the equation uses the exact selector/constructor/append bindings validated for this
   * native layout.
   */
  private def capturesGlobalBinding(source: VLam, name: String, expected: GlobalBinding): Boolean =
    source.body match {
      case LamBody.Core(_, capturedEnv) => capturedEnv.globals.get(name).exists(_ eq expected)
      case _                            => false
    }

  private def validatesListAppend(source: VLam): Boolean = {
    val exactIdentity = source.id match {
      case ValueId.Const(ListAppendName) => true
      case _                             => false
    }
    val exactTelescope =
      source.tpe.binders.length == 5 &&
        source.tpe.binders.map(_.mode) ==
        Vector(BinderMode.Implicit, BinderMode.Implicit, BinderMode.Implicit, BinderMode.Explicit, BinderMode.Explicit)
    (exactIdentity, exactTelescope, source.body) match {
      case (true, true, LamBody.Core(term, _))
          if term.ty.binders.length == 5 && term.recursivePeers.length == 1 && term.recursion.exists { recursion =>
            term.recursivePeers == Vector(recursion.selfRef -> ListAppendName) &&
            (recursion.decreases match {
              case CoreAst.DecreaseSpec.Lexicographic(Vector(ref), _) => ref == term.ty.binders(3).localRef
              case _                                                  => false
            })
          } =>
        val xs = term.ty.binders(3).localRef
        val ys = term.ty.binders(4).localRef
        val self = term.recursion.get.selfRef
        stripEmptyBodies(term.body) match {
          case CoreAst.Term.Match(
                CoreAst.Term.LocalRef(scrutinee, _),
                _,
                cases,
                None,
                None,
                _,
                _
              ) if scrutinee == xs && cases.length == 2 =>
            val nilCase = cases.find(_.ctorName == "List.nil")
            val consCase = cases.find(_.ctorName == "List.cons")
            (nilCase, consCase) match {
              case (Some(nil), Some(cons))
                  if nil.patternVars.isEmpty && cons.patternVars.length == 2 &&
                    isLocalRef(stripEmptyBodies(nil.body), ys) =>
                val head = cons.patternVars(0).ref
                val tail = cons.patternVars(1).ref
                stripEmptyBodies(cons.body) match {
                  case CoreAst.Term.App(
                        CoreAst.Term.GlobalRef("List.cons", _),
                        Vector(CoreAst.Term.LocalRef(consHead, _), rest),
                        evidence,
                        _
                      ) if evidence.isEmpty && consHead == head =>
                    stripEmptyBodies(rest) match {
                      case CoreAst.Term.App(
                            CoreAst.Term.LocalRef(recursive, _),
                            Vector(CoreAst.Term.LocalRef(recursiveTail, _), CoreAst.Term.LocalRef(recursiveYs, _)),
                            evidence0,
                            _
                          ) =>
                        recursive == self && recursiveTail == tail && recursiveYs == ys && evidence0.isEmpty
                      case _ => false
                    }
                  case _ => false
                }
              case _ => false
            }
          case _ => false
        }
      case _ => false
    }
  }

  private def stripEmptyBodies(term: CoreAst.Term): CoreAst.Term =
    term match {
      case CoreAst.Term.Body(lets, result, _) if lets.isEmpty => stripEmptyBodies(result)
      case other                                              => other
    }

  private def isLocalRef(term: CoreAst.Term, expected: CoreAst.LocalRef): Boolean =
    term match {
      case CoreAst.Term.LocalRef(ref, _) => ref == expected
      case _                             => false
    }

  private def isSelectorOf(term: CoreAst.Term, selector: String, base: CoreAst.LocalRef): Boolean =
    term match {
      case CoreAst.Term.App(
            CoreAst.Term.GlobalRef(name, _),
            Vector(CoreAst.Term.LocalRef(ref, _)),
            evidence,
            _
          ) =>
        name == selector && ref == base && evidence.isEmpty
      case _ => false
    }
}
