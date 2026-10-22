package com.raccoonlang

import com.raccoonlang.Value._

import java.util.concurrent.atomic.AtomicInteger

class NativeBufferBuiltinsTests extends munit.FunSuite with TestSupport {
  private val env = Prelude.default.checkedEnv
  private val natType = env("Nat")
  private val span = Span(0, 0)
  private val nilHead = env("List.nil").asInstanceOf[ConstructorHead]
  private val consHead = env("List.cons").asInstanceOf[ConstructorHead]
  private val zeroHead = env("Nat.zero").asInstanceOf[ConstructorHead]
  private val succHead = env("Nat.succ").asInstanceOf[ConstructorHead]
  private val pairHead = env("Pair.mk").asInstanceOf[ConstructorHead]
  private val bridge = env(NativeBufferBuiltins.Name)

  private def global(name: String): CoreAst.Term = CoreAst.Term.GlobalRef(name, span)
  private def applyType(name: String, argument: CoreAst.Term): Value =
    TypeChecker
      .checkTerm(
        CoreAst.Term.App(global(name), Vector(argument), Vector.empty, span),
        env
      )
      .value

  private val listNatType = applyType("List", global("Nat"))
  private val listListNatType =
    applyType("List", CoreAst.Term.App(global("List"), Vector(global("Nat")), Vector.empty, span))

  private def nil(tpe: Value): Value = VCtor(nilHead, Vector.empty, tpe)
  private def listOf(values: Vector[Value], tpe: Value): Value =
    values.foldRight(nil(tpe))((value, rest) => VCtor(consHead, Vector(value, rest), tpe))
  private def packedNat(value: BigInt): Value = VPacked.nat(value, natType)

  // load one byte, add one, and store it in a fresh output buffer
  private val incrementProgram: Value = listOf(
    Vector[BigInt](
      NativeBufferProgram.Magic,
      NativeBufferProgram.Version,
      3,
      1,
      2,
      6,
      NativeBufferProgram.BufferRole.Input,
      1,
      NativeBufferProgram.BufferRole.Output,
      1,
      NativeBufferProgram.Op.Const32,
      0,
      1,
      NativeBufferProgram.Op.Const64,
      0,
      0,
      NativeBufferProgram.Op.Load8,
      1,
      0,
      0,
      NativeBufferProgram.Op.Alu32,
      2,
      1,
      0,
      NativeBufferProgram.Alu.Add,
      NativeBufferProgram.Op.Store8,
      1,
      0,
      2,
      NativeBufferProgram.Op.Halt
    ).map(packedNat),
    listNatType
  )

  private def inputRows(row: Value): Value = listOf(Vector(row), listListNatType)
  private def inputRow(byte: Value): Value = listOf(Vector(byte), listNatType)

  private def invoke(program: Value, rows: Value): Value = Interpreter.evalApply(bridge, Vector(program, rows))

  private def nat(value: Value): BigInt = value match {
    case packed: VPacked if packed.codec eq NatCodec          => packed.natValue.get
    case VCtor(head, Vector(), _) if head eq zeroHead         => BigInt(0)
    case VCtor(head, Vector(previous), _) if head eq succHead => BigInt(1) + nat(previous)
    case other                                                => fail(s"Expected Nat result, got $other")
  }

  private def list(value: Value, expectedType: Value): Vector[Value] = {
    val result = Vector.newBuilder[Value]
    var rest = value
    var done = false
    while (!done) {
      rest match {
        case VCtor(head, Vector(), tpe) if (head eq nilHead) && ValueEquivalence.defEq(tpe, expectedType) => done = true
        case VCtor(head, Vector(item, tail), tpe) if (head eq consHead) && ValueEquivalence.defEq(tpe, expectedType) =>
          result += item
          rest = tail
        case other => fail(s"Expected closed List result, got $other")
      }
    }
    result.result()
  }

  private def statusAndBytes(value: Value): (BigInt, Vector[Vector[BigInt]]) = value match {
    case VCtor(head, Vector(status, outputs), _) if head eq pairHead =>
      val rows = list(outputs, listListNatType).map(row => list(row, listNatType).map(nat))
      (nat(status), rows)
    case other => fail(s"Expected native bridge status/result pair, got $other")
  }

  test("unary and packed small Nats agree, and unary prefixes cannot overflow a packed U64 suffix") {
    var unary65: Value = VCtor(zeroHead, Vector.empty, natType)
    var index = 0
    while (index < 65) {
      unary65 = VCtor(succHead, Vector(unary65), natType)
      index += 1
    }
    val packed65 = packedNat(65)
    assertEquals(
      statusAndBytes(invoke(incrementProgram, inputRows(inputRow(unary65)))),
      (BigInt(0), Vector(Vector(BigInt(66))))
    )
    assertEquals(
      statusAndBytes(invoke(incrementProgram, inputRows(inputRow(packed65)))),
      (BigInt(0), Vector(Vector(BigInt(66))))
    )

    val maxU64 = packedNat((BigInt(1) << 64) - 1)
    val overflowing = VCtor(succHead, Vector(maxU64), natType)
    assertEquals(statusAndBytes(invoke(incrementProgram, inputRows(inputRow(overflowing)))), (BigInt(6), Vector.empty))
  }

  test("nested symbolic list values block with all dependencies and retry to the direct ground result") {
    val byte = FreshVar.freshVar("buffer-byte", natType)
    val remainingRows = FreshVar.freshVar("remaining-rows", listListNatType)
    val symbolicRows = VCtor(consHead, Vector(inputRow(byte), remainingRows), listListNatType)
    val stuck = invoke(incrementProgram, symbolicRows)
    val expectedBlockers = DepSet(byte.id) ++ DepSet(remainingRows.id)
    stuck match {
      case VBlockedApp(head, Vector(program, rows), _, blockers) =>
        assert(head eq bridge)
        assertEquals(rows, symbolicRows)
        assertEquals(program, incrementProgram)
        assertEquals(blockers, expectedBlockers)
      case other => fail(s"Expected blocked Buffer.run application, got $other")
    }
    val store = EqStore.empty
      .allow(expectedBlockers)
      .addLink(byte.id, packedNat(41))
      .addLink(remainingRows.id, nil(listListNatType))
    assertEquals(
      statusAndBytes(ValueOps.materialize(stuck, store)),
      (BigInt(0), Vector(Vector(BigInt(42))))
    )
  }

  test("closed stuck list data stays neutral and bridge dependency traversal never inspects deferred evidence") {
    val closedAxiom = VConst("closedBufferByte", Symbol, natType)
    invoke(incrementProgram, inputRows(inputRow(closedAxiom))) match {
      case app: VApp if app.blockedOn.isEmpty => assertEquals(app.args(1), inputRows(inputRow(closedAxiom)))
      case other                              => fail(s"Expected an unblocked neutral application, got $other")
    }

    val function = runProgram("def proofIndexed (n: Nat)[h: Eq(Nat, n, 1)]: Nat := n\n{ proofIndexed }")
    val forces = new AtomicInteger
    val deferred = new DeferredEvidence(() => {
      forces.incrementAndGet()
      fail("Buffer.run inspected erased evidence in a stuck list element")
    })
    val evidenceApplication = VApp(function, Vector(packedNat(41), deferred), natType)
    val before = DeferredEvidence.forcings.get()
    val neutral = invoke(incrementProgram, inputRows(inputRow(evidenceApplication)))
    assertEquals(DeferredEvidence.forcings.get() - before, 0L)
    assertEquals(forces.get(), 0)
    neutral match {
      case app: VApp if app.blockedOn.isEmpty => ()
      case other                              => fail(s"Expected a neutral result without forcing evidence, got $other")
    }
  }

  test("source result marshalling rejects outputs above its separate cap before allocating lists") {
    val oversizedProgram = listOf(
      Vector[BigInt](
        NativeBufferProgram.Magic,
        NativeBufferProgram.Version,
        0,
        0,
        1,
        1,
        NativeBufferProgram.BufferRole.Output,
        NativeBufferProgram.MaxSourceOutputBytes + 1,
        NativeBufferProgram.Op.Halt
      ).map(packedNat),
      listNatType
    )
    assertEquals(statusAndBytes(invoke(oversizedProgram, nil(listListNatType))), (BigInt(5), Vector.empty))
  }

  test("a List family with a changed value kind is rejected at the native bridge declaration boundary") {
    val original = env("List").asInstanceOf[VConst]
    val pi = original.tpe.asInstanceOf[VPi]
    val changedClassifier = Sorts.sort(Value.Level.zero, Kind.lin)
    val changedPi = pi.copy(codomain = _ => changedClassifier)
    val changedList = VConst("List", original.constType, changedPi)
    val alteredEnv = env.copy(globals = env.globals.updated("List", GlobalBinding.Strict(changedList)))
    val bridgeType = bridge.tpe
    val rejected = intercept[Diagnostic] {
      NativeBufferBuiltins.instantiate(NativeBufferBuiltins.Name, bridgeType, alteredEnv)
    }
    assert(rejected.error.isInstanceOf[TypeMismatch], rejected.error.toString)
  }
}
