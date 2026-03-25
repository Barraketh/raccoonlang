package com.raccoonlang

class MatchRefinementTests extends munit.FunSuite {
  private def runProgram(src: String): Value = {
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
        | | succ (p: Nat) : Nat
        |
        |inductive Eq (A: Type) indices (x: A) (y: A) : Sort Level.one
        | | refl (x: A) : Eq A x x
        |
        |def symmEq (a: Nat)(b: Nat)(p: Eq Nat a b): Eq Nat b a := {
        |  match p as _ returning Eq Nat b a with
        |  | Eq.refl x => Eq.refl Nat x
        |}
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
        | | succ (p: Nat) : Nat
        |
        |inductive Eq (A: Type) indices (x: A) (y: A) : Sort Level.one
        | | refl (x: A) : Eq A x x
        |
        |def congSucc2 (a: Nat)(b: Nat)(p: Eq Nat a b): Eq Nat (Nat.succ a) (Nat.succ b) := {
        |  match p as _ returning Eq Nat (Nat.succ a) (Nat.succ b) with
        |  | Eq.refl x => Eq.refl Nat (Nat.succ x)
        |}
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
        | | succ (p: Nat) : Nat
        |
        |inductive Eq (A: Type) indices (x: A) (y: A) : Sort Level.one
        | | refl (x: A) : Eq A x x
        |
        |def badCongCtor (a: Nat): Eq Nat a (Nat.succ a) := {
        |  match Eq.refl Nat a as _ returning Eq Nat a (Nat.succ a) with
        |  | Eq.refl x => Eq.refl Nat x
        |}
        |
        |do { Nat.zero }
        |""".stripMargin

    intercept[TypeMismatch] {
      runProgram(p)
    }
  }

  test("match refinement: cumulative family parameter on neutral Vec scrut succeeds") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (p: Nat) : Nat
        |
        |inductive Vec (u: Level)(A: Sort u) indices (n: Nat) : Sort u
        | | nil : Vec u A Nat.zero
        | | cons (n: Nat) (xs: Vec u A n) (x: A) : Vec u A (Nat.succ n)
        |
        |inline def keepVec (n: Nat)(v: Vec Level.one Nat n): Vec Level.one Nat n := {
        |  match v as self returning Vec Level.one Nat n with
        |  | Vec.nil => self
        |  | Vec.cons k xs x => self
        |}
        |
        |do { Nat.zero }
        |""".stripMargin

    runProgram(p)
  }
}
