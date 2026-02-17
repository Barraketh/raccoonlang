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
        |  match b as _ returning Eq Nat (add (Nat.succ a) b) (Nat.succ (add a b)) with
        |  | Nat.zero => Eq.refl Nat (Nat.succ a)
        |  | Nat.succ x => {
        |    succAdd (Nat.succ a) x
        |  }
        |}
        |do { addComm Nat.zero Nat.zero }
        |""".stripMargin

    runProgram(p)
  }
}
