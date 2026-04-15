package com.raccoonlang

class MatchExhaustivenessTests extends munit.FunSuite {
  private def typecheckDecls(src: String): Unit = {
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
        | | succ (_: Nat) : Nat
        |
        |def onlyZero (n: Nat): Nat := {
        |  match n as _ returning Nat with
        |  | Nat::zero => Nat::zero
        |}
        |
        |""".stripMargin

    intercept[MissingCase] { typecheckDecls(p) }
  }

  test("duplicate case: two Nat::zero branches") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def dup (n: Nat): Nat := {
        |  match n as _ returning Nat with
        |  | Nat::zero => Nat::zero
        |  | Nat::zero => Nat::zero
        |  | Nat::succ x => x
        |}
        |
        |""".stripMargin

    intercept[DuplicateCase] { typecheckDecls(p) }
  }

  test("unreachable case: Vec::cons on Vec A Nat::zero") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |inductive Vec (A: Type) indices (n: Nat) : Sort(Level::one)
        | | nil : Vec(A, Nat::zero)
        | | cons (n: Nat) (xs: Vec(A, n)) (x: A): Vec(A, Nat::succ(n))
        |
        |def f (A: Type)(v: Vec(A, Nat::zero)): Nat := {
        |  match v as _ returning Nat with
        |  | Vec::nil => Nat::zero
        |  | Vec::cons n xs x => Nat::zero
        |}
        |
        |""".stripMargin

    intercept[UnreachableCase] { typecheckDecls(p) }
  }

  test("non-exhaustive: opaque scrutinee application should still require succ case") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |// OPAQUE (not inline): evaluator will keep this as a Symbol head
        |def g (n: Nat): Nat := Nat::zero
        |
        |def bad (n: Nat): Nat := {
        |  // scrutinee is neutral/opaque application: g n
        |  match g(n) as _ returning Nat with
        |  | Nat::zero => Nat::zero
        |}
        |
        |""".stripMargin

    intercept[MissingCase] { typecheckDecls(p) }
  }

  test("exhaustive: opaque scrutinee application should typecheck") {
    val p =
      """
        |inductive Nat : Type
        | | zero : Nat
        | | succ (_: Nat) : Nat
        |
        |def g (n: Nat): Nat := n   // not(inline) => opaque
        |
        |def ok (n: Nat): Nat := {
        |  match g(n) as _ returning Nat with
        |  | Nat::zero => Nat::zero
        |  | Nat::succ x => x
        |}
        |
        |""".stripMargin

    // Should typecheck (even if it evaluates to a stuck match at runtime for opaque g).
    typecheckDecls(p)
  }
}
