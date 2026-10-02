package com.raccoonlang

import com.raccoonlang.Value._
import java.nio.file.Paths

class PreparedScalarTests extends munit.FunSuite with TestSupport {
  override protected val suitePrelude: Prelude.Config = Prelude.fromPath(Paths.get("gpu/Prelude.rac"))
  private def nat(value: BigInt, fn: VLam): Value = VPacked.nat(value, fn.tpe.env("Nat"))

  test("prepared scalar arithmetic agrees across small, overflow and BigInt inputs") {
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
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked scalar closure was not eligible"))
    Vector(BigInt(0), BigInt(1), BigInt(256), BigInt(Long.MaxValue), BigInt(Long.MaxValue) + 1).foreach { n =>
      val arg = nat(n, fn)
      val generic = Interpreter.evalApply(fn, Vector(arg))
      val fast = prepared.run(Vector(arg))
      assertEquals(fast.key, generic.key)
      assert(ValueEquivalence.defEq(fast, generic))
    }
  }

  test("zero modulus, source fallback and a boxed constructor boundary agree") {
    val fn = runProgram(
      """
        |def calc (x: Nat): List(Nat) := {
        |  let value := Nat.mod(Nat.add(x, 1), 0)
        |  List.cons(value, List.nil(Nat))
        |}
        |{ calc }
        |""".stripMargin
    ).asInstanceOf[VLam]
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked scalar closure was not eligible"))
    val arg = nat(3, fn)
    assertEquals(prepared.run(Vector(arg)).key, Interpreter.evalApply(fn, Vector(arg)).key)
    val sourceFast = Packed.withOpsDisabled(prepared.run(Vector(arg)))
    val sourceGeneric = Packed.withOpsDisabled(Interpreter.evalApply(fn, Vector(arg)))
    assertEquals(sourceFast.key, sourceGeneric.key)
  }

  test("add overflow and zero multiplication retain exact Nat results") {
    val add = runProgram("def addOne (x: Nat): Nat := Nat.add(x, 1)\n{ addOne }").asInstanceOf[VLam]
    val multiply = runProgram("def zeroMul (x: Nat): Nat := Nat.mul(x, 0)\n{ zeroMul }").asInstanceOf[VLam]
    val addPrepared = PreparedEval.prepare(add).getOrElse(fail("Checked add was not eligible"))
    val mulPrepared = PreparedEval.prepare(multiply).getOrElse(fail("Checked mul was not eligible"))
    val max = nat(BigInt(Long.MaxValue), add)
    assertEquals(addPrepared.run(Vector(max)).key, Interpreter.evalApply(add, Vector(max)).key)
    val mulArg = nat(BigInt(Long.MaxValue), multiply)
    assertEquals(mulPrepared.run(Vector(mulArg)).key, Interpreter.evalApply(multiply, Vector(mulArg)).key)
  }

  test("trusted subtraction, division and comparisons retain zero and large-value semantics") {
    val arithmetic = runProgram(
      "def calc (x: Nat): Nat := Nat.add(Nat.sub(x, 3), Nat.div(x, 0))\n{ calc }"
    ).asInstanceOf[VLam]
    val compare = runProgram(
      "def cmp (x: Nat): Bool := Nat.blt(Nat.sub(x, 3), Nat.div(x, 2))\n{ cmp }"
    ).asInstanceOf[VLam]
    val eq = runProgram("def cmp (x: Nat): Bool := Nat.beq(x, 3)\n{ cmp }").asInstanceOf[VLam]
    val le = runProgram("def cmp (x: Nat): Bool := Nat.ble(x, 3)\n{ cmp }").asInstanceOf[VLam]
    Vector(arithmetic, compare, eq, le).foreach { fn =>
      val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked scalar closure was not eligible"))
      Vector(BigInt(0), BigInt(3), BigInt(4), BigInt(Long.MaxValue), BigInt(Long.MaxValue) + 1).foreach { n =>
        val arg = nat(n, fn)
        assertEquals(prepared.run(Vector(arg)).key, Interpreter.evalApply(fn, Vector(arg)).key)
      }
    }
    val three = nat(3, compare)
    assertEquals(
      Packed.withOpsDisabled(PreparedEval.prepare(compare).get.run(Vector(three))).key,
      Packed.withOpsDisabled(Interpreter.evalApply(compare, Vector(three))).key
    )
  }

  test("computed scalar used by deferred evidence keeps its exact captured value") {
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
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked evidence caller was not eligible"))
    val first = nat(2, fn)
    val second = nat(3, fn)
    assertEquals(prepared.run(Vector(first)).key, Interpreter.evalApply(fn, Vector(first)).key)
    assertEquals(prepared.run(Vector(second)).key, Interpreter.evalApply(fn, Vector(second)).key)
    assertEquals(prepared.run(Vector(first)).key, Interpreter.evalApply(fn, Vector(first)).key)
  }

  test("tail recursive scalar arguments survive frame reuse and closure capture") {
    val fn = runProgram(
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
    val prepared = PreparedEval.prepare(fn).getOrElse(fail("Checked scalar closure was not eligible"))
    Vector(0, 1, 9, 100).foreach { n =>
      val arg = nat(BigInt(n), fn)
      assertEquals(prepared.run(Vector(arg)).key, Interpreter.evalApply(fn, Vector(arg)).key)
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
    val makePrepared = PreparedEval.prepare(maker).getOrElse(fail("Checked maker was not eligible"))
    val three = nat(3, maker)
    val escaped = makePrepared.run(Vector(three))
    makePrepared.run(Vector(nat(4, maker)))
    assertEquals(
      Interpreter.evalApply(escaped, Vector(three)).key,
      Interpreter.evalApply(Interpreter.evalApply(maker, Vector(three)), Vector(three)).key
    )
  }
}
