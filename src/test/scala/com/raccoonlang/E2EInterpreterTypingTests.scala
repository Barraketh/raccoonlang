package com.raccoonlang

import com.raccoonlang.Interpreter.{ConstType, ConstructorHead, Symbol, Value}

class E2EInterpreterTypingTests extends munit.FunSuite {
  private def runProgram(src: String): Interpreter.Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  // Erased shape comparison helpers
  sealed trait Shape
  case class SConst(name: String, ct: ConstType) extends Shape
  case class SApp(head: Shape, args: List[Shape]) extends Shape

  private def toShape(v: Value): Shape = v match {
    case Interpreter.VConst(n, ct, _) => SConst(n, ct)
    case Interpreter.VApp(h, args, _) => SApp(toShape(h), args.toList.map(toShape))
    case other                        => SConst(other.toString, ConstructorHead) // fallback
  }

  private val zeroS = SConst("Nat.zero", ConstructorHead)
  private def succS(s: Shape) = SApp(SConst("Nat.succ", ConstructorHead), List(s))

  test("inline id typechecks and reduces") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inline def id (A: Type)(x: A): A := x
        |
        |do {
        |  id Nat Nat.zero
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("inline def: declared return too large (A -> A) expected, value A") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inline def bad (A: Type)(x: A): A -> A := x
        |
        |do { Nat.zero }
        |""".stripMargin

    intercept[RuntimeException] {
      runProgram(p)
    }
  }

  test("let with mismatched ascription fails (constructor vs Nat)") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |do {
        |  let s : Nat := Nat.succ
        |  s
        |}
        |""".stripMargin

    intercept[RuntimeException] {
      runProgram(p)
    }
  }

  test("ascribed function type alpha-equals: (x: Nat)->Nat vs fun (y: Nat) => y") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |do {
        |  let f : (x: Nat) -> Nat := fun (y: Nat): Nat => y
        |  f Nat.zero
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("pred on Nat typechecks and reduces via match") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inline def pred (n: Nat): Nat :=
        |  match n as _ returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ x => x
        |
        |do {
        |  pred (Nat.succ Nat.zero)
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), zeroS)
  }

  test("inline def: declared result Type but branch returns Nat => mismatch") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inline def bad (n: Nat): Type :=
        |  match n as _ returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.succ x => x
        |
        |do { Nat.zero }
        |""".stripMargin

    intercept[RuntimeException] {
      runProgram(p)
    }
  }

  test("opaque constant stays symbol and is callable but not reduced") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |def inc (n: Nat): Nat := Nat.succ n
        |
        |do { inc }
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), SConst("inc", Symbol))
  }

  test("unannotated let with constructor synthesizes type and reduces when applied") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |do {
        |  let one := Nat.succ Nat.zero
        |  one
        |}
        |""".stripMargin

    val res = runProgram(p)
    assertEquals(toShape(res), succS(zeroS))
  }
}
