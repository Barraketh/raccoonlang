package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class MatchExhaustivenessTests extends munit.FunSuite {
  private def runProgram(src: String): Interpreter.Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("non-exhaustive: missing succ case on Nat") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |def onlyZero (n: Nat): Nat := {
        |  match n as _ returning Nat with
        |  | Nat.zero => Nat.zero
        |}
        |
        |do { Nat.zero }
        |""".stripMargin

    intercept[TypeErrWithSpan] {
      runProgram(p)
    }
  }

  test("duplicate case: two Nat.zero branches") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |def dup (n: Nat): Nat := {
        |  match n as _ returning Nat with
        |  | Nat.zero => Nat.zero
        |  | Nat.zero => Nat.zero
        |  | Nat.succ x => x
        |}
        |
        |do { Nat.zero }
        |""".stripMargin

    intercept[TypeErrWithSpan] {
      runProgram(p)
    }
  }

  test("unreachable case: Vec.cons on Vec A Nat.zero") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inductive Vec(A: Type)(n: Nat) : Type
        | | nil(A: Type): Vec A Nat.zero
        | | cons(A: Type)(n: Nat)(xs: Vec A n)(x: A): Vec A (Nat.succ n)
        |
        |def f (A: Type)(v: Vec A Nat.zero): Nat := {
        |  match v as _ returning Nat with
        |  | Vec.nil t => Nat.zero
        |  | Vec.cons a n xs x => Nat.zero
        |}
        |
        |do { Nat.zero }
        |""".stripMargin

    intercept[TypeErrWithSpan] {
      runProgram(p)
    }
  }
}
