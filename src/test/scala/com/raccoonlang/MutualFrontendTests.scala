package com.raccoonlang

class MutualFrontendTests extends munit.FunSuite with TestSupport {
  test("surface mutual definitions elaborate, check, and run") {
    val result = runProgram(
      """
        |mutual {
        |  def even (n: Nat): Bool decreases structural(n) := {
        |    match n with
        |    | Nat.zero => Bool.true
        |    | Nat.succ k => odd(k)
        |  }
        |  def odd (n: Nat): Bool decreases structural(n) := {
        |    match n with
        |    | Nat.zero => Bool.false
        |    | Nat.succ k => even(k)
        |  }
        |}
        |
        |{ even(2) }
        |""".stripMargin
    )
    assertEquals(ctorName(result), "Bool.true")
  }

  test("surface mutual inductives expose sibling families atomically") {
    typecheckDecls(
      """
        |mutual {
        |  inductive Even : Type
        |   | zero : Even
        |   | succ (odd: Odd) : Even
        |
        |  inductive Odd : Type
        |   | succ (even: Even) : Odd
        |}
        |""".stripMargin
    )
  }

  test("surface mutual inductives preserve a shared parameter telescope") {
    typecheckDecls(
      """
        |mutual {
        |  inductive Even (A: Type) : Type
        |   | zero : Even(A)
        |   | succ (odd: Odd(A)) : Even(A)
        |
        |  inductive Odd (A: Type) : Type
        |   | succ (even: Even(A)) : Odd(A)
        |}
        |""".stripMargin
    )
  }

  test("mutually recursive structs publish selectors after the atomic block") {
    typecheckDecls(
      """
        |mutual {
        |  struct Left : Type
        |   | mk (right: Right) : Left
        |
        |  struct Right : Type
        |   | mk (left: Left) : Right
        |}
        |
        |def rightOf (value: Left): Right := value.right
        |def leftOf (value: Right): Left := value.left
        |""".stripMargin
    )
  }

  test("mutual groups containing a struct still reject mixed declaration kinds") {
    expectTypeError[InvalidRecursiveGroup](
      """
        |mutual {
        |  struct S : Type
        |   | mk : S
        |
        |  def f (n: Nat): Nat decreases structural(n) := Nat.zero
        |}
        |""".stripMargin
    )
  }

  test("qualified mutual peers resolve inside a namespace") {
    val result = runProgram(
      """
        |namespace Qualified {
        |  mutual {
        |    def even (n: Nat): Bool decreases structural(n) := {
        |      match n with
        |      | Nat.zero => Bool.true
        |      | Nat.succ k => Qualified.odd(k)
        |    }
        |    def odd (n: Nat): Bool decreases structural(n) := {
        |      match n with
        |      | Nat.zero => Bool.false
        |      | Nat.succ k => _root_.Qualified.even(k)
        |    }
        |  }
        |}
        |
        |{ Qualified.even(2) }
        |""".stripMargin
    )
    assertEquals(ctorName(result), "Bool.true")
  }

  test("mutual definitions require a decrease specification for every member") {
    expectTypeError[InvalidDecreaseSpec](
      """
        |mutual {
        |  def first (n: Nat): Nat decreases structural(n) := {
        |    match n with
        |    | Nat.zero => Nat.zero
        |    | Nat.succ k => second(k)
        |  }
        |  def second (n: Nat): Nat := Nat.zero
        |}
        |""".stripMargin
    )
  }

  test("mutual groups reject mixed declaration kinds") {
    expectTypeError[InvalidRecursiveGroup](
      """
        |mutual {
        |  def f (n: Nat): Nat decreases structural(n) := Nat.zero
        |  inductive T : Type
        |   | mk : T
        |}
        |""".stripMargin
    )
  }

  test("mutual recursive calls must decrease across peers") {
    expectTypeError[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def even (n: Nat): Bool decreases structural(n) := {
        |    match n with
        |    | Nat.zero => Bool.true
        |    | Nat.succ k => odd(n)
        |  }
        |  def odd (n: Nat): Bool decreases structural(n) := Bool.false
        |}
        |""".stripMargin
    )
  }
}
