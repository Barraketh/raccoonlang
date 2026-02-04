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
         |inductive Eq (A: Type)(x: A)(y: A) : Type
         | | refl (A: Type)(x: A) : Eq A x x
         |
         |def congSucc (a: Nat)(b: Nat)(p: Eq Nat a b): Eq Nat (Nat.succ a) (Nat.succ b) :=
         |  match p as p0 returning Eq Nat (Nat.succ a) (Nat.succ b) with
         |  | Eq.refl A x => Eq.refl Nat (Nat.succ x)
         |
         |def symm (a: Nat)(b: Nat)(p: Eq Nat a b): Eq Nat b a :=
         |  match p as p0 returning Eq Nat b a with
         |  | Eq.refl A x => Eq.refl Nat x
         |
         |def trans (a: Nat)(b: Nat)(c: Nat)(p: Eq Nat a b)(q: Eq Nat b c): Eq Nat a c :=
         |  match p as p0 returning Eq Nat a c with
         |  | Eq.refl A x => q
         |
         |def add_succ_left (n: Nat)(k: Nat): Eq Nat (add (Nat.succ n) k) (Nat.succ (add n k)) :=
         |  match k as kk returning Eq Nat (add (Nat.succ n) kk) (Nat.succ (add n kk)) with
         |  | Nat.zero => Eq.refl Nat (Nat.succ n)
         |  | Nat.succ x => congSucc (add (Nat.succ n) x) (Nat.succ (add n x)) (add_succ_left n x)
         |
         |def add_comm (n: Nat)(k: Nat): Eq Nat (add n k) (add k n) :=
         |  match k as kk returning Eq Nat (add n kk) (add kk n) with
         |  | Nat.zero => Eq.refl Nat n
         |  | Nat.succ x => trans (add n (Nat.succ x)) (Nat.succ (add n x)) (add (Nat.succ x) n) (add_succ_left n x) (trans (Nat.succ (add n x)) (Nat.succ (add x n)) (add (Nat.succ x) n) (congSucc (add n x) (add x n) (add_comm n x)) (symm (add (Nat.succ x) n) (Nat.succ (add x n)) (add_succ_left x n)))
         |
         |do { Nat.zero }
         |""".stripMargin

      runProgram(p)
  }
}
