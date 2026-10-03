package com.raccoonlang

import com.raccoonlang.Value.{NatCodec, VPacked, VLam}
import java.nio.file.Paths

class ScalarEvaluationTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.fromPath(Paths.get("gpu/Prelude.rac"))

  private def nat(value: BigInt, fn: VLam): VPacked = VPacked.nat(value, fn.tpe.env("Nat"))

  private def natPayload(value: Value): BigInt =
    value match {
      case packed: VPacked if packed.codec == NatCodec => packed.natValue.getOrElse(fail("Missing Nat payload"))
      case other                                       => fail(s"Expected packed Nat, got $other")
    }

  private def bool(env: Env, expected: Boolean): Value = {
    val suffix = if (expected) "Bool.true" else "Bool.false"
    val name = env.globals.keys.find(_.endsWith(suffix)).getOrElse(fail(s"No $suffix constructor"))
    Packed.construct(env(name).asInstanceOf[Value.ConstructorHead], Vector.empty, env("Bool"))
  }

  test("scalar arithmetic follows its BigInt formula through Long overflow") {
    val fn = runProgram(
      """
        |def calc (x: Nat): Nat := {
        |  let product := Nat.mul(x, 3)
        |  let sum := Nat.add(product, 5)
        |  Nat.mod(sum, 257)
        |}
        |{ calc }
        |""".stripMargin
    ).asInstanceOf[VLam]
    val inputs = Vector(BigInt(0), BigInt(1), BigInt(256), BigInt(Long.MaxValue), BigInt(Long.MaxValue) + 1)
    inputs.foreach { value =>
      val result = Interpreter.evalApply(fn, Vector(nat(value, fn)))
      assertEquals(natPayload(result), (value * 3 + 5) % 257)
    }
  }

  test("zero modulus returns its dividend across a boxed constructor boundary") {
    val fn = runProgram(
      """
        |def calc (x: Nat): List(Nat) := {
        |  let value := Nat.mod(Nat.add(x, 1), 0)
        |  List.cons(value, List.nil(Nat))
        |}
        |{ calc }
        |""".stripMargin
    ).asInstanceOf[VLam]
    val result = Interpreter.evalApply(fn, Vector(nat(3, fn)))
    val expected = runProgram("{ List.cons(4, List.nil(Nat)) }")
    assert(ValueEquivalence.defEq(result, expected))
    val sourceResult = Packed.withOpsDisabled(Interpreter.evalApply(fn, Vector(nat(3, fn))))
    assert(ValueEquivalence.defEq(sourceResult, expected))
  }

  test("addition overflow and multiplication by zero retain exact Nat results") {
    val add = runProgram("def addOne (x: Nat): Nat := Nat.add(x, 1)\n{ addOne }").asInstanceOf[VLam]
    val multiply = runProgram("def zeroMul (x: Nat): Nat := Nat.mul(x, 0)\n{ zeroMul }").asInstanceOf[VLam]
    val max = BigInt(Long.MaxValue)
    Vector(max -> (max + 1), (max + 1) -> (max + 2)).foreach { case (input, expected) =>
      assertEquals(natPayload(Interpreter.evalApply(add, Vector(nat(input, add)))), expected)
    }
    Vector(max, max + 1).foreach { input =>
      assertEquals(natPayload(Interpreter.evalApply(multiply, Vector(nat(input, multiply)))), BigInt(0))
    }
  }

  test("subtraction, division by zero and comparisons follow Nat equations") {
    val arithmetic = runProgram(
      "def calc (x: Nat): Nat := Nat.add(Nat.sub(x, 3), Nat.div(x, 0))\n{ calc }"
    ).asInstanceOf[VLam]
    val compare = runProgram(
      "def cmp (x: Nat): Bool := Nat.blt(Nat.sub(x, 3), Nat.div(x, 2))\n{ cmp }"
    ).asInstanceOf[VLam]
    val eq = runProgram("def cmp (x: Nat): Bool := Nat.beq(x, 3)\n{ cmp }").asInstanceOf[VLam]
    val le = runProgram("def cmp (x: Nat): Bool := Nat.ble(x, 3)\n{ cmp }").asInstanceOf[VLam]
    val inputs = Vector(BigInt(0), BigInt(3), BigInt(4), BigInt(Long.MaxValue), BigInt(Long.MaxValue) + 1)
    inputs.foreach { value =>
      assertEquals(
        natPayload(Interpreter.evalApply(arithmetic, Vector(nat(value, arithmetic)))),
        (value - 3).max(BigInt(0))
      )
      val compared = Interpreter.evalApply(compare, Vector(nat(value, compare)))
      val expectedComparison = (value - 3).max(BigInt(0)) < value / 2
      assert(ValueEquivalence.defEq(compared, bool(compare.tpe.env, expectedComparison)))
      assert(ValueEquivalence.defEq(Interpreter.evalApply(eq, Vector(nat(value, eq))), bool(eq.tpe.env, value == 3)))
      assert(ValueEquivalence.defEq(Interpreter.evalApply(le, Vector(nat(value, le))), bool(le.tpe.env, value <= 3)))
    }
    val disabled = Packed.withOpsDisabled(Interpreter.evalApply(compare, Vector(nat(3, compare))))
    assert(ValueEquivalence.defEq(disabled, bool(compare.tpe.env, expected = true)))
  }

  test("computed scalar arguments remain valid under deferred equality evidence") {
    val fn = runProgram(
      """
        |def need (n: Nat)[h: Eq(Nat, n, n)]: Nat := n
        |def run (x: Nat): Nat := {
        |  let computed := Nat.add(x, 1)
        |  need(computed)
        |}
        |{ run }
        |""".stripMargin
    ).asInstanceOf[VLam]
    val first = nat(2, fn)
    val second = nat(3, fn)
    val forced = forcings {
      assertEquals(natPayload(Interpreter.evalApply(fn, Vector(first))), BigInt(3))
      assertEquals(natPayload(Interpreter.evalApply(fn, Vector(second))), BigInt(4))
      assertEquals(natPayload(Interpreter.evalApply(fn, Vector(first))), BigInt(3))
    }
    assertEquals(forced, 0L)
  }

  test("tail-recursive scalar arguments and escaping closure captures remain exact") {
    val iterate = runProgram(
      """
        |def iterate (n: Nat)(acc: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => acc
        |  | Nat.succ k => iterate(k, Nat.add(acc, 1))
        |}
        |def run (n: Nat): Nat := iterate(n, 0)
        |{ run }
        |""".stripMargin
    ).asInstanceOf[VLam]
    Vector(BigInt(0), BigInt(1), BigInt(9), BigInt(100)).foreach { n =>
      assertEquals(natPayload(Interpreter.evalApply(iterate, Vector(nat(n, iterate)))), n)
    }

    val maker = runProgram(
      """
        |def maker (n: Nat): Nat -> Nat := {
        |  let captured := Nat.add(n, 1)
        |  fun (ignored: Nat): Nat => captured
        |}
        |{ maker }
        |""".stripMargin
    ).asInstanceOf[VLam]
    val three = nat(3, maker)
    val four = nat(4, maker)
    val first = Interpreter.evalApply(maker, Vector(three))
    val second = Interpreter.evalApply(maker, Vector(four))
    val firstAgain = Interpreter.evalApply(maker, Vector(three))
    assertEquals(natPayload(Interpreter.evalApply(first, Vector(three))), BigInt(4))
    assertEquals(natPayload(Interpreter.evalApply(second, Vector(three))), BigInt(5))
    assertEquals(first.key, firstAgain.key)
    assertNotEquals(first.key, second.key)
  }
}
