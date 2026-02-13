package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class E2EEqualityCommTests extends munit.FunSuite {
  private def runProgram(src: String): Interpreter2.Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter2.run(core)
        } catch {
          case t: TypeErrWithSpan =>
            val source = Source(src)
            fail(ErrorReporter.pretty(t, source))
        }
      case err: Failure => fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }
  }

  test("prove add commutativity (a + b = b + a)") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ : Nat -> Nat
        |
        |inline def add (a: Nat)(b: Nat): Nat := {
        |  match b as (_: Nat) returning Nat with
        |  | Nat.zero => a
        |  | Nat.succ x => add (Nat.succ a) x
        |}
        |
        |inductive Eq : (A: Type) -> A -> A -> Type
        | | refl (A: Type)(x: A) : Eq A x x
        |
        |def trans (A: Type)(x: A)(y: A)(z: A)(p: Eq A x y)(q: Eq A y z): Eq A x z := {
        |  match p as (p0: Eq A x y) returning Eq A x z with
        |  | Eq.refl A0 w => q
        |}
        |
        |def symm (A: Type)(x: A)(y: A)(p: Eq A x y): Eq A y x := {
        |  match p as (p0: Eq A x y) returning Eq A y x with
        |  | Eq.refl A0 w => Eq.refl A w
        |}
        |
        |def congSucc (a: Nat)(b: Nat)(p: Eq Nat a b): Eq Nat (Nat.succ a) (Nat.succ b) := {
        |  match p as (p0: Eq Nat a b) returning Eq Nat (Nat.succ a) (Nat.succ b) with
        |  | Eq.refl A x => Eq.refl Nat (Nat.succ x)
        |}
        |
        |def addSuccLeft (a: Nat)(b: Nat): Eq Nat (add (Nat.succ a) b) (Nat.succ (add a b)) := {
        |  match b as (b0: Nat) returning Eq Nat (add (Nat.succ a) b0) (Nat.succ (add a b0)) with
        |  | Nat.zero => Eq.refl Nat (Nat.succ a)
        |  | Nat.succ x => {
        |     trans Nat (add (Nat.succ a) (Nat.succ x)) (add (Nat.succ (Nat.succ a)) x) (Nat.succ (add a (Nat.succ x))) (Eq.refl Nat (add (Nat.succ (Nat.succ a)) x)) (trans Nat (add (Nat.succ (Nat.succ a)) x) (Nat.succ (add (Nat.succ a) x)) (Nat.succ (add a (Nat.succ x))) (addSuccLeft (Nat.succ a) x) (Eq.refl Nat (Nat.succ (add (Nat.succ a) x))))
        |  }
        |}
        |
        |def addZeroLeft (a: Nat): Eq Nat (add Nat.zero a) a := {
        |  match a as (a0: Nat) returning Eq Nat (add Nat.zero a0) a0 with
        |  | Nat.zero => Eq.refl Nat Nat.zero
        |  | Nat.succ x => trans Nat (add Nat.zero (Nat.succ x)) (add (Nat.succ Nat.zero) x) (Nat.succ x) (Eq.refl Nat (add (Nat.succ Nat.zero) x)) (trans Nat (add (Nat.succ Nat.zero) x) (Nat.succ (add Nat.zero x)) (Nat.succ x) (addSuccLeft Nat.zero x) (congSucc (add Nat.zero x) x (addZeroLeft x)))
        |}
        |
        |def addComm (a: Nat)(b: Nat): Eq Nat (add a b) (add b a) := {
        |  match b as (b0: Nat) returning Eq Nat (add a b0) (add b0 a) with
        |  | Nat.zero => symm Nat (add Nat.zero a) a (addZeroLeft a)
        |  | Nat.succ x => trans Nat (add a (Nat.succ x)) (add (Nat.succ a) x) (add (Nat.succ x) a) (Eq.refl Nat (add (Nat.succ a) x)) (trans Nat (add (Nat.succ a) x) (Nat.succ (add a x)) (add (Nat.succ x) a) (addSuccLeft a x) (trans Nat (Nat.succ (add a x)) (Nat.succ (add x a)) (add (Nat.succ x) a) (congSucc (add a x) (add x a) (addComm a x)) (symm Nat (add (Nat.succ x) a) (Nat.succ (add x a)) (addSuccLeft x a))))
        |}
        |
        |do { addComm Nat.zero Nat.zero }
        |""".stripMargin

    runProgram(p)
  }
}
