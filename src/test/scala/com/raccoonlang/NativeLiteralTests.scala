package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.Value.{NatCodec, VPacked}

class NativeLiteralTests extends munit.FunSuite {
  private def parse(src: String, prelude: Prelude.Config): CoreAst.Program =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) => Elaborator.elab(value, prelude)
      case err: Failure         => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private def runProgram(src: String): Value = runProgram(src, Prelude.default)

  private def runProgram(src: String, prelude: Prelude.Config): Value =
    try Interpreter.run(parse(src, prelude), prelude).getOrElse(fail("Program has no body"))
    catch {
      case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
    }

  private def typecheckDecls(src: String): Unit =
    try Interpreter.run(parse(src, Prelude.default), Prelude.default)
    catch {
      case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
    }

  private def payload(value: Value): BigInt =
    value match {
      case p: VPacked if p.codec == NatCodec => p.payload
      case other                             => fail(s"Expected packed Nat, got $other")
    }

  private def ctorName(value: Value): String =
    value match {
      case Value.VCtor(head, _, _) => head.name
      case other                   => fail(s"Expected constructor value, got $other")
    }

  private def expectTypeError[E <: TypeError](src: String, prelude: Prelude.Config)(implicit
      tag: reflect.ClassTag[E]
  ): E =
    intercept[E](Interpreter.run(parse(src, prelude), prelude))

  test("literal syntax, constructor folding, and printing use packed Nats") {
    assertEquals(payload(runProgram("{ 5 }")), BigInt(5))
    assertEquals(PrettyPrinter.print(runProgram("{ 5 }")), "5")
    assertEquals(payload(runProgram("{ Nat.zero }")), BigInt(0))
    assertEquals(payload(runProgram("{ Nat.succ(41) }")), BigInt(42))
    typecheckDecls("def five : Nat := 5")
  }

  test("literal and constructor forms are definitionally equal") {
    typecheckDecls(
      """
        |def p : Eq(Nat, 5, Nat.succ(4)) := Eq.refl(5)
        |def q : Eq(Nat, Nat.succ(Nat.succ(Nat.zero)), 2) := Eq.refl(2)
        |""".stripMargin
    )
  }

  test("matching and constructor folding stay constant-time for large literals") {
    assertEquals(payload(runProgram("{ Nat.pred(1000000) }")), BigInt(999999))
  }

  test("accelerated Nat operations follow the Prelude conventions") {
    assertEquals(payload(runProgram("{ Nat.add(2, 3) }")), BigInt(5))
    assertEquals(payload(runProgram("{ Nat.sub(3, 5) }")), BigInt(0))
    assertEquals(payload(runProgram("{ Nat.mul(7, 8) }")), BigInt(56))
    assertEquals(payload(runProgram("{ Nat.pow(2, 10) }")), BigInt(1024))
    assertEquals(payload(runProgram("{ Nat.pow(7, 0) }")), BigInt(1))
    assertEquals(ctorName(runProgram("{ Nat.beq(5, 5) }")), "Bool.true")
    assertEquals(ctorName(runProgram("{ Nat.ble(2, 3) }")), "Bool.true")
    assertEquals(ctorName(runProgram("{ Nat.blt(3, 3) }")), "Bool.false")
  }

  test("pow enforces the native exponent limit without structural fallback") {
    val limit = Packed.MaxPowExponent
    assertEquals(payload(runProgram(s"{ Nat.pow(1, $limit) }")), BigInt(1))

    val error = expectTypeError[NativeOperationLimitExceeded](
      s"{ Nat.pow(1, ${limit + 1}) }",
      Prelude.default
    )
    assertEquals(error.operation, "Nat.pow")
    assertEquals(error.argument, limit + 1)
    assertEquals(error.limit, limit)
  }

  test("native operations agree with their structural definitions") {
    val arithmeticRanges = Vector("add" -> 12, "sub" -> 12, "mul" -> 6, "pow" -> 3)
    arithmeticRanges.foreach { case (op, limit) =>
      for {
        a <- 0 to limit
        b <- 0 to limit
      } {
        val src = s"{ Nat.$op($a, $b) }"
        val accelerated = runProgram(src)
        val structural = Packed.withOpsDisabled(runProgram(src))
        assert(ValueEquivalence.defEq(accelerated, structural), s"Nat.$op disagreed at ($a, $b)")
      }
    }

    Vector("beq", "ble", "blt").foreach { op =>
      for {
        a <- 0 to 12
        b <- 0 to 12
      } {
        val src = s"{ Nat.$op($a, $b) }"
        val accelerated = runProgram(src)
        val structural = Packed.withOpsDisabled(runProgram(src))
        assert(ValueEquivalence.defEq(accelerated, structural), s"Nat.$op disagreed at ($a, $b)")
      }
    }
  }

  test("large native-operation results use exact BigInt arithmetic") {
    val two64 = BigInt(2).pow(64)
    val two128 = BigInt(2).pow(128)
    assertEquals(payload(runProgram(s"{ Nat.mul($two64, $two64) }")), two128)
    assertEquals(payload(runProgram(s"{ Nat.add($two128, $two128) }")), two128 * 2)
    assertEquals(ctorName(runProgram(s"{ Nat.blt($two64, $two128) }")), "Bool.true")

    val random = new java.util.Random(0x4b33L)
    val pairs = Vector.fill(10) {
      val a = BigInt(new java.math.BigInteger(128, random))
      val b = BigInt(new java.math.BigInteger(128, random))
      (a, b)
    }
    pairs.foreach { case (a, b) =>
      assertEquals(payload(runProgram(s"{ Nat.add($a, $b) }")), a + b)
      assertEquals(payload(runProgram(s"{ Nat.sub($a, $b) }")), (a - b).max(0))
      assertEquals(payload(runProgram(s"{ Nat.mul($a, $b) }")), a * b)
      assertEquals(ctorName(runProgram(s"{ Nat.beq($a, $b) }")), if (a == b) "Bool.true" else "Bool.false")
      assertEquals(ctorName(runProgram(s"{ Nat.ble($a, $b) }")), if (a <= b) "Bool.true" else "Bool.false")
      assertEquals(ctorName(runProgram(s"{ Nat.blt($a, $b) }")), if (a < b) "Bool.true" else "Bool.false")

      val smallBase = a & ((BigInt(1) << 32) - 1)
      val smallExponent = (b & 7).toInt
      assertEquals(payload(runProgram(s"{ Nat.pow($smallBase, $smallExponent) }")), smallBase.pow(smallExponent))
    }
  }

  test("packed literals refine constructor equations and prove apartness") {
    typecheckDecls(
      """
        |def refine (n: Nat)(h: Eq(Nat, Nat.succ(n), 5)): Eq(Nat, n, 4) := {
        |  match h returning Eq(Nat, n, 4) with
        |  | Eq.refl z => Eq.refl(n)
        |}
        |
        |def distinct (h: Eq(Nat, 3, 5)): False := {
        |  match h returning False with
        |}
        |""".stripMargin
    )
  }

  test("forced implicits project constructor fields from packed literals") {
    val src =
      """
        |def predecessor {n: Nat}(h: Eq(Nat, Nat.succ(n), 5)): Nat := n
        |{ predecessor(Eq.refl(5)) }
        |""".stripMargin
    assertEquals(payload(runProgram(src)), BigInt(4))
  }

  test("packed versus an opaque neutral is stuck, never apart") {
    expectTypeError[MissingCase](
      """
        |opaque def k : Nat := 5
        |def notApart (h: Eq(Nat, k, 5)): False := {
        |  match h returning False with
        |}
        |""".stripMargin,
      Prelude.default
    )
  }

  test("ground literal matches enforce their one reachable constructor") {
    assertEquals(
      payload(
        runProgram(
          """
            |{
            |  match 3 returning Nat with
            |  | Nat.succ p => p
            |}
            |""".stripMargin
        )
      ),
      BigInt(2)
    )

    expectTypeError[UnreachableCase](
      """
        |{
        |  match 3 returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ p => p
        |}
        |""".stripMargin,
      Prelude.default
    )
  }

  test("structural recursion can decrease directly on packed payloads") {
    val src =
      """
        |def fib (n: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ p => {
        |    match p returning Nat with
        |    | Nat.zero => 1
        |    | Nat.succ q => Nat.add(fib(p), fib(q))
        |  }
        |}
        |
        |{ fib(20) }
        |""".stripMargin
    assertEquals(payload(runProgram(src)), BigInt(6765))
  }

  test("packed literals survive quote and residual evaluation") {
    val src =
      """
        |def addFive : (n: Nat) -> Nat := fun (n: Nat): Nat => Nat.add(n, 5)
        |{ addFive(2) }
        |""".stripMargin
    assertEquals(payload(runProgram(src)), BigInt(7))

    val original = runProgram("{ 1000000 }")
    val quoted = ValueQuote.quoteTerm(original, ValueQuote.quoteContext(Prelude.default.checkedEnv), Span(0, 0))
    val roundTripped = Interpreter.evalTerm(quoted, Prelude.default.checkedEnv)
    assertEquals(roundTripped.key, original.key)
  }

  test("native Nat names are reserved outside the bundled Prelude") {
    val natDecl =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |""".stripMargin

    assertEquals(expectTypeError[ReservedKernelName](natDecl, Prelude.none).name, "Nat")
    assertEquals(expectTypeError[ReservedKernelName](natDecl, Prelude.test).name, "Nat")

    val custom = Prelude.fromSource("custom-prelude", natDecl)
    assertEquals(intercept[ReservedKernelName](custom.checkedEnv).name, "Nat")

    val reservedOp =
      """
        |namespace Nat {
        |  def add (A: Type): Type := A
        |}
        |""".stripMargin
    assertEquals(expectTypeError[ReservedKernelName](reservedOp, Prelude.none).name, "Nat.add")

    assertEquals(payload(runProgram("{ Nat.add(2, 3) }")), BigInt(5))
  }
}
