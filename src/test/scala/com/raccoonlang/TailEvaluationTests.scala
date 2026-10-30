package com.raccoonlang

import com.raccoonlang.ProgramFixtures.Programs

/**
 * Tail positions run in a loop (docs/kernel.md, "Evaluation depth"): a block's result, a match's chosen branch and a
 * lambda's body where it is applied take no host stack, so these programs run on a 1 MiB stack, where a frame per call
 * would overflow. Recursion outside tail position is still bounded by the stack (`EvaluationTooDeepTests`).
 */
class TailEvaluationTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = true)
  import programs._

  private def onSmallStack[T](body: => T): T = Execution.onStack(1L << 20)(body)

  test("a 100,000-deep tail recursion runs") {
    val src =
      """
        |def count (n: Nat)(acc: Nat): Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => acc
        |  | Nat.succ k => count(k, Nat.add(acc, 1))
        |}
        |
        |count(100000, 0)
        |""".stripMargin
    assertEquals(onSmallStack(result(src)), "100000")
  }

  test("a block's result after its lets and an accumulated list are tails") {
    val src =
      """
        |def build (n: Nat)(acc: List(Nat)): List(Nat) decreases structural(n) := {
        |  match n returning List(Nat) with
        |  | Nat.zero => acc
        |  | Nat.succ k => {
        |    let next := List.cons(k, acc)
        |    build(k, next)
        |  }
        |}
        |
        |List.length(build(100000, List.nil(Nat)))
        |""".stripMargin
    assertEquals(onSmallStack(result(src)), "100000")
  }

  test("calls between the members of a mutual block in tail position run in a loop") {
    val src =
      """
        |mutual {
        |  def isEven (n: Nat) : Bool decreases structural(n) := {
        |    match n returning Bool with
        |    | Nat.zero => Bool.true
        |    | Nat.succ k => isOdd(k)
        |  }
        |  def isOdd (n: Nat) : Bool decreases structural(n) := {
        |    match n returning Bool with
        |    | Nat.zero => Bool.false
        |    | Nat.succ k => isEven(k)
        |  }
        |}
        |
        |isEven(100001)
        |""".stripMargin
    assertEquals(onSmallStack(result(src)), "Bool.false")
  }

  test("a demanded proof whose recursion is in tail position runs in a loop") {
    val src =
      """
        |def walk (n: Nat) : True decreases structural(n) := {
        |  match n returning True with
        |  | Nat.zero => True.intro
        |  | Nat.succ k => walk(k)
        |}
        |
        |def t : True := {
        |  match walk(100000) returning True with
        |  | True.intro => True.intro
        |}
        |
        |t
        |""".stripMargin
    assertEquals(onSmallStack(result(src)), "True.intro")
  }

  test("an error in a tail position is located at the innermost term, as without the loop") {
    val src =
      """
        |def loop (n: Nat)(acc: Nat) : Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => {
        |    let big := Nat.pow(2, acc)
        |    Nat.pow(big, big)
        |  }
        |  | Nat.succ k => loop(k, Nat.add(acc, 40))
        |}
        |
        |loop(2, 0)
        |""".stripMargin
    assertErrorAt[NatValueTooLarge](src, "(big, big)")
  }
}
