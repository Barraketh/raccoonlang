package com.raccoonlang

import com.raccoonlang.Value.{NatCodec, VPacked}

class FrameEvaluationTests extends munit.FunSuite with TestSupport {
  private val peano =
    """
      |inductive Peano : Type
      | | zero : Peano
      | | succ (_: Peano) : Peano
      |""".stripMargin

  private def constructor(fn: Value.VLam, suffix: String): Value.ConstructorHead = {
    val name = fn.tpe.env.globals.keys.find(_.endsWith(suffix)).getOrElse(fail(s"No $suffix constructor"))
    fn.tpe.env(name) match {
      case head: Value.ConstructorHead => head
      case other                       => fail(s"Expected $suffix constructor, got $other")
    }
  }

  private def peanoZero(fn: Value.VLam): Value =
    Packed.construct(constructor(fn, "Peano.zero"), Vector.empty, constructor(fn, "Peano.zero").tpe)

  private def peanoSucc(fn: Value.VLam, value: Value): Value =
    Packed.construct(constructor(fn, "Peano.succ"), Vector(value), constructor(fn, "Peano.zero").tpe)

  private def peanoType(fn: Value.VLam): Value = constructor(fn, "Peano.zero").tpe

  private def peanoFrom(n: Int, fn: Value.VLam): Value =
    (0 until n).foldLeft(peanoZero(fn))((value, _) => peanoSucc(fn, value))

  private def natPayload(value: Value): BigInt =
    value match {
      case packed: VPacked if packed.codec == NatCodec => packed.natValue.getOrElse(fail("Missing Nat payload"))
      case other                                       => fail(s"Expected packed Nat, got $other")
    }

  private def bool(env: Env, expected: Boolean): Value = {
    val suffix = if (expected) "Bool.true" else "Bool.false"
    val name = env.globals.keys.find(_.endsWith(suffix)).getOrElse(fail(s"No $suffix constructor"))
    val head = env(name).asInstanceOf[Value.ConstructorHead]
    Packed.construct(head, Vector.empty, env("Bool"))
  }

  private def captures(value: Value): Vector[Value] =
    value match {
      case lam: Value.VLam =>
        lam.id match {
          case Value.ValueId.LocalId(_, captured) => captured
          case other                              => fail(s"Expected local closure identity, got $other")
        }
      case other => fail(s"Expected a closure, got $other")
    }

  test("nested closures retain captured values and identity across later invocations") {
    val source = peano +
      """
        |def capture (x: Peano): Peano -> Peano := {
        |  let captured := Peano.succ(x)
        |  fun (ignored: Peano): Peano => captured
        |}
        |{ capture }
        |""".stripMargin
    val fn = runProgram(source).asInstanceOf[Value.VLam]
    val z = peanoZero(fn)
    val one = peanoSucc(fn, z)
    val two = peanoSucc(fn, one)
    val first = Interpreter.evalApply(fn, Vector(z))
    val second = Interpreter.evalApply(fn, Vector(one))
    val firstAgain = Interpreter.evalApply(fn, Vector(z))

    assert(ValueEquivalence.defEq(Interpreter.evalApply(first, Vector(z)), one))
    assert(ValueEquivalence.defEq(Interpreter.evalApply(second, Vector(z)), two))
    assertEquals(first.key, firstAgain.key)
    assertNotEquals(first.key, second.key)
    assertEquals(captures(first).length, 1)
    assert(ValueEquivalence.defEq(captures(first).head, one))
    assert(ValueEquivalence.defEq(captures(second).head, two))
  }

  test("recursive matches and non-tail arguments compute the specified Peano formula") {
    val fn = runProgram(
      peano +
        """
          |def add (a: Peano)(b: Peano): Peano decreases structural(b) := {
          |  match b returning Peano with
          |  | Peano.zero => a
          |  | Peano.succ rest => add(Peano.succ(a), rest)
          |}
          |def twice (x: Peano): Peano := {
          |  let y := Peano.succ(x)
          |  add(y, y)
          |}
          |{ twice }
          |""".stripMargin
    ).asInstanceOf[Value.VLam]
    Vector(0, 1, 2, 5).foreach { n =>
      val result = Interpreter.evalApply(fn, Vector(peanoFrom(n, fn)))
      assert(ValueEquivalence.defEq(result, peanoFrom(2 * (n + 1), fn)))
      assert(ValueEquivalence.defEq(Interpreter.evalApply(fn, Vector(peanoFrom(n, fn))), peanoFrom(2 * (n + 1), fn)))
    }
  }

  test("missing arguments fail before the body and deferred evidence stays unforced") {
    val fn = runProgram(
      """
        |def need [h: True]: Nat := 1
        |def caller (n: Nat): Nat := need()
        |{ caller }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    interceptError[ArityMismatch](Interpreter.evalApply(fn, Vector.empty))
    val nat = fn.tpe.env("Nat")
    val arg = VPacked.nat(3, nat)
    val forced = forcings {
      assertEquals(natPayload(Interpreter.evalApply(fn, Vector(arg))), BigInt(1))
      assertEquals(natPayload(Interpreter.evalApply(fn, Vector(arg))), BigInt(1))
    }
    assertEquals(forced, 0L)
  }

  test("a neutral match preserves its blocker and captured variable identity") {
    val fn = runProgram(
      peano +
        """
          |def choose (x: Peano): Peano := {
          |  match x returning Peano with
          |  | Peano.zero => Peano.zero
          |  | Peano.succ p => p
          |}
          |{ choose }
          |""".stripMargin
    ).asInstanceOf[Value.VLam]
    val (_, neutral) = FreshVar.freshValue("unknown", fn.tpe.env("Peano"))
    val stuck = Interpreter.evalApply(fn, Vector(neutral)).asInstanceOf[Value.NeutralThunk]

    assertEquals(stuck.term.cases.map(_.ctorName), Vector("Peano.zero", "Peano.succ"))
    assertEquals(stuck.blockedOn, neutral.synDeps)
    assertEquals(stuck.synDeps, neutral.synDeps)
    val captured = stuck.id.asInstanceOf[Value.ValueId.LocalId].captures
    assertEquals(captured.length, 1)
    assert(captured.head eq neutral)
    assert(ValueEquivalence.defEq(stuck.tpe, peanoType(fn)))
    assert(ValueEquivalence.defEq(Interpreter.evalApply(fn, Vector(peanoSucc(fn, peanoZero(fn)))), peanoZero(fn)))
    assert(stuck.env.localValuesIterator.exists(_ eq neutral))

    val repeated = Interpreter.evalApply(fn, Vector(neutral)).asInstanceOf[Value.NeutralThunk]
    assertEquals(repeated.key, stuck.key)
    assertEquals(repeated.blockedOn, neutral.synDeps)
    assertEquals(repeated.synDeps, neutral.synDeps)
    val repeatedCaptures = repeated.id.asInstanceOf[Value.ValueId.LocalId].captures
    assertEquals(repeatedCaptures.length, 1)
    assert(repeatedCaptures.head eq neutral)
    assert(repeated.env.localValuesIterator.exists(_ eq neutral))
  }

  test("mutual recursive peers return even exactly for even Nat inputs") {
    val fn = runProgram(
      """
        |mutual {
        |  def even (n: Nat): Bool decreases structural(n) := {
        |    match n returning Bool with
        |    | Nat.zero => Bool.true
        |    | Nat.succ k => odd(k)
        |  }
        |  def odd (n: Nat): Bool decreases structural(n) := {
        |    match n returning Bool with
        |    | Nat.zero => Bool.false
        |    | Nat.succ k => even(k)
        |  }
        |}
        |{ even }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    Vector(0, 1, 2, 9, 32).foreach { n =>
      val result = Interpreter.evalApply(fn, Vector(VPacked.nat(n, fn.tpe.env("Nat"))))
      assert(ValueEquivalence.defEq(result, bool(fn.tpe.env, n % 2 == 0)))
    }
  }

  test("dependent Pi snapshots survive later calls and scope returns the outer value") {
    val makeType = runProgram(
      """
        |def makeType (n: Nat): Type := {
        |  let copied := n
        |  (x: Eq(Nat, copied, copied)) -> Nat
        |}
        |{ makeType }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    val nat = makeType.tpe.env("Nat")
    val one = VPacked.nat(1, nat)
    val two = VPacked.nat(2, nat)
    val first = Interpreter.evalApply(makeType, Vector(one)).asInstanceOf[Value.VPi]
    val second = Interpreter.evalApply(makeType, Vector(two)).asInstanceOf[Value.VPi]
    val firstAgain = Interpreter.evalApply(makeType, Vector(one)).asInstanceOf[Value.VPi]
    val firstBinderType = Interpreter.evalTerm(first.binders.head.ty, first.env)
    val secondBinderType = Interpreter.evalTerm(second.binders.head.ty, second.env)

    assert(ValueEquivalence.defEq(firstBinderType, runProgram("{ Eq(Nat, 1, 1) }")))
    assert(ValueEquivalence.defEq(secondBinderType, runProgram("{ Eq(Nat, 2, 2) }")))
    assertEquals(first.key, firstAgain.key)
    assertNotEquals(first.key, second.key)

    val scoped = runProgram("def scoped (n: Nat): Nat := scope l => n\n{ scoped }").asInstanceOf[Value.VLam]
    val seven = VPacked.nat(7, scoped.tpe.env("Nat"))
    assertEquals(natPayload(Interpreter.evalApply(scoped, Vector(seven))), BigInt(7))
  }

  test("equation matches and disabled native operations return their source-defined values") {
    val fn = runProgram(
      """
        |def choose (n: Nat): Nat := {
        |  let increased := Nat.add(n, 1)
        |  match h : Nat.isZero(n) returning Nat with
        |  | Bool.true => 0
        |  | Bool.false => increased
        |}
        |{ choose }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    val nat = fn.tpe.env("Nat")
    Vector(BigInt(0) -> BigInt(0), BigInt(1) -> BigInt(2), BigInt(17) -> BigInt(18)).foreach { case (input, expected) =>
      val result = Interpreter.evalApply(fn, Vector(VPacked.nat(input, nat)))
      assertEquals(natPayload(result), expected)
    }
    val disabled = Packed.withOpsDisabled(Interpreter.evalApply(fn, Vector(VPacked.nat(4, nat))))
    assertEquals(natPayload(disabled), BigInt(5))
  }

  test("separate nominal module contexts retain their own Peano constructor types") {
    val module = peano +
      """
        |def wrap (x: Peano): Peano := Peano.succ(x)
        |""".stripMargin
    val first = outside(module, "{ wrap }").getOrElse(fail("First module has no body")).asInstanceOf[Value.VLam]
    val second = outside(module, "{ wrap }").getOrElse(fail("Second module has no body")).asInstanceOf[Value.VLam]
    val firstResult = Interpreter.evalApply(first, Vector(peanoZero(first)))
    val secondResult = Interpreter.evalApply(second, Vector(peanoZero(second)))
    val firstExpected = peanoSucc(first, peanoZero(first))
    val secondExpected = peanoSucc(second, peanoZero(second))

    assertEquals(ctorName(firstResult), constructor(first, "Peano.succ").name)
    assertEquals(ctorName(secondResult), constructor(second, "Peano.succ").name)
    assert(ValueEquivalence.defEq(firstResult, firstExpected))
    assert(ValueEquivalence.defEq(secondResult, secondExpected))
    assert(firstResult.tpe eq peanoType(first))
    assert(secondResult.tpe eq peanoType(second))
    assert(!(firstResult.tpe eq secondResult.tpe))
  }

  test("tail calls handle layouts that grow and shrink") {
    val fn = runProgram(
      """
        |def narrow (x: Nat): Nat := x
        |def wide (x: Nat)(y: Nat): Nat := narrow(Nat.add(x, y))
        |def run (n: Nat): Nat := wide(n, 3)
        |{ run }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    val nat = fn.tpe.env("Nat")
    Vector(BigInt(0), BigInt(1), BigInt(10), BigInt(Long.MaxValue) + 1).foreach { n =>
      val result = Interpreter.evalApply(fn, Vector(VPacked.nat(n, nat)))
      assertEquals(natPayload(result), n + 3)
    }
  }

  test("same-thread callbacks can reenter evaluation without overwriting the outer frame") {
    val fn = runProgram(
      """
        |def callback (n: Nat): Nat := n
        |def run (n: Nat): Nat := Nat.add(callback(n), n)
        |{ run }
        |""".stripMargin
    ).asInstanceOf[Value.VLam]
    val originalCore = fn.body.asInstanceOf[Value.LamBody.Core]
    val callback = originalCore.env("callback").asInstanceOf[Value.VLam]
    var runFn: Value.VLam = null
    var calls = 0
    val callbackBody = Value.LamBody.Native(
      (args, _) => {
        calls += 1
        if (calls == 1) assertEquals(natPayload(Interpreter.evalApply(runFn, args)), BigInt(4))
        args.head
      },
      callback.body.asInstanceOf[Value.LamBody.Core].env,
      isRawRecursive = false
    )
    val native = callback.copy(body = callbackBody)
    val modifiedEnv = originalCore.env.copy(
      globals = originalCore.env.globals.updated("callback", GlobalBinding.Strict(native))
    )
    val modified = fn.copy(body = originalCore.copy(env = modifiedEnv))
    runFn = modified

    assertEquals(natPayload(Interpreter.evalApply(runFn, Vector(VPacked.nat(2, fn.tpe.env("Nat"))))), BigInt(4))
    assertEquals(calls, 2)
    assertEquals(natPayload(Interpreter.evalApply(runFn, Vector(VPacked.nat(3, fn.tpe.env("Nat"))))), BigInt(6))
    assertEquals(calls, 3)
  }
}
