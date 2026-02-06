package com.raccoonlang

import com.raccoonlang.Interpreter.TypeErr

class E2EEqualityCommTests extends munit.FunSuite {
  private def runProgram(src: String): Interpreter.Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        Interpreter.run(core)
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("attempt to prove add commutativity (structured proof, should fail until J)") {
    val p =
      """
         |inductive Nat : Type
         | | zero : Nat
         | | succ : Nat -> Nat
         |
         |inline def add (a: Nat)(b: Nat): Nat :=
         |  match b as _ returning Nat with
         |  | Nat.zero => a
         |  | Nat.succ x => add (Nat.succ a) x
         |
         |inductive Eq : (A: Type) -> A -> A -> Type
         | | refl (A: Type)(x: A) : Eq A x x
         |
         |def congSucc (a: Nat)(b: Nat)(p: Eq Nat a b): Eq Nat (Nat.succ a) (Nat.succ b) :=
         |  match p as p0 returning Eq Nat (Nat.succ a) (Nat.succ b) with
         |  | Eq.refl A x => Eq.refl Nat (Nat.succ x)
         |
         |do { Nat.zero }
         |""".stripMargin

      runProgram(p)
  }
}
