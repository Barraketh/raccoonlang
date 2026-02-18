package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class EqualityCommTests extends munit.FunSuite {
  private def runProgram(src: String): Interpreter.Value = {
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        val core = Elaborator.elab(value)
        try {
          Interpreter.run(core)
        } catch {
          case t: TypeError =>
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
        |  match b as _ returning Nat with
        |  | Nat.zero => a
        |  | Nat.succ x => add (Nat.succ a) x
        |}
        |
        |inductive Eq : (A: Type) -> A -> A -> Type
        | | refl (A: Type)(x: A) : Eq A x x
        |
        |def trans (A: Type)(x: A)(y: A)(z: A)(p: Eq A x y)(q: Eq A y z): Eq A x z := {
        |  match p as _ returning Eq A x z with
        |  | Eq.refl A0 w => q
        |}
        |
        |def symm (A: Type)(x: A)(y: A)(p: Eq A x y): Eq A y x := {
        |  match p as _ returning Eq A y x with
        |  | Eq.refl A0 w => Eq.refl A w
        |}
        |
        |def congSucc (a: Nat)(b: Nat)(p: Eq Nat a b): Eq Nat (Nat.succ a) (Nat.succ b) := {
        |  match p as _ returning Eq Nat (Nat.succ a) (Nat.succ b) with
        |  | Eq.refl A x => Eq.refl Nat (Nat.succ x)
        |}
        |
        |def succAdd (a: Nat)(b: Nat): Eq Nat (add (Nat.succ a) b) (Nat.succ (add a b)) := {
        |  match b as b0 returning Eq Nat (add (Nat.succ a) b0) (Nat.succ (add a b0)) with
        |  | Nat.zero => Eq.refl Nat (Nat.succ a)
        |  | Nat.succ x => succAdd (Nat.succ a) x
        |}
        |
        |// add 0 b = b
        |def zeroAdd (b: Nat): Eq Nat (add Nat.zero b) b := {
        |  match b as b0 returning Eq Nat (add Nat.zero b0) b0 with
        |  | Nat.zero => Eq.refl Nat Nat.zero
        |  | Nat.succ x => {
        |    let ih := zeroAdd x
        |    let step1 := succAdd Nat.zero x
        |    let step2 := congSucc (add Nat.zero x) x ih
        |    trans Nat (add (Nat.succ Nat.zero) x) (Nat.succ (add Nat.zero x)) (Nat.succ x) step1 step2
        |  }
        |}
        |
        |// add commutativity: a + b = b + a
        |def addComm (a: Nat)(b: Nat): Eq Nat (add a b) (add b a) := {
        |  match b as b0 returning Eq Nat (add a b0) (add b0 a) with
        |  | Nat.zero => symm Nat (add Nat.zero a) a (zeroAdd a)
        |  | Nat.succ x => {
        |    let ih := addComm a x
        |    let step1 := succAdd a x
        |    let stepCong := congSucc (add a x) (add x a) ih
        |    let stepSwap := symm Nat (add (Nat.succ x) a) (Nat.succ (add x a)) (succAdd x a)
        |    let tail := trans Nat (Nat.succ (add a x)) (Nat.succ (add x a)) (add (Nat.succ x) a) stepCong stepSwap
        |    trans Nat (add (Nat.succ a) x) (Nat.succ (add a x)) (add (Nat.succ x) a) step1 tail
        |  }
        |}
        |
        |do { addComm Nat.zero Nat.zero }
        |""".stripMargin

    runProgram(p)
  }
}
