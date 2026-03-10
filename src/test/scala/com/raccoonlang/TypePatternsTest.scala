package com.raccoonlang

class TypePatternsTest extends munit.FunSuite {
  test("Indexed Vec") {
    val program =
      """
        |inductive Nat : Type
        |  | zero: Nat
        |  | succ (_: Nat): Nat
        |
        |inductive Vec (A: Type $u)(n: Nat): Type u
        |  | nil(A: Type _): Vec A Nat.zero
        |  | cons(vec: Vec $A $n)(elem: A): Vec A (Nat.succ n)
        |
        |""".stripMargin
  }

  test("Patterns of patterns") {
    val program =
      """
        |def foo(a: ($A : Type $u)): Type u := A
        |""".stripMargin
  }

  test("Pattern of patterns 2") {
    val program =
      """
        |def foo(a: Vec $B _)
        |""".stripMargin
  }

}
