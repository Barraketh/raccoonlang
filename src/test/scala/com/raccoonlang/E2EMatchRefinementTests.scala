package com.raccoonlang

import com.raccoonlang.Interpreter.TypeErr

class E2EMatchRefinementTests extends munit.FunSuite {
  private def runProgram(src: String): Interpreter.Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("match refinement: symmEq over neutral VApp scrut succeeds") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inductive Eq : (A: Type) -> A -> A -> Type
        | | refl (A: Type)(x: A) : Eq A x x
        |
        |def symmEq (a: Nat)(b: Nat)(p: Eq Nat a b): Eq Nat b a :=
        |  match p as p0 returning Eq Nat b a with
        |  | Eq.refl A x => Eq.refl A x
        |
        |do { Nat.zero }
        |""".stripMargin

    runProgram(p)
  }

  test("match refinement: congSucc via wrapped scrut succeeds") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inductive Eq : (A: Type) -> A -> A -> Type
        | | refl (A: Type)(x: A) : Eq A x x
        |
        |def congSucc2 (a: Nat)(b: Nat)(p: Eq Nat a b): Eq Nat (Nat.succ a) (Nat.succ b) :=
        |  match p as p0 returning Eq Nat (Nat.succ a) (Nat.succ b) with
        |  | Eq.refl A x => Eq.refl Nat (Nat.succ x)
        |
        |do { Nat.zero }
        |""".stripMargin

    runProgram(p)
  }

  test("match refinement negative: mismatched motive (extra succ) fails (ctor scrut)") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inductive Eq : (A: Type) -> A -> A -> Type
        | | refl (A: Type)(x: A) : Eq A x x
        |
        |def badCongCtor (a: Nat): Eq Nat a (Nat.succ a) :=
        |  match Eq.refl Nat a as p0 returning Eq Nat a (Nat.succ a) with
        |  | Eq.refl A x => Eq.refl Nat x
        |
        |do { Nat.zero }
        |""".stripMargin

    intercept[RuntimeException] {
      runProgram(p)
    }
  }
}
