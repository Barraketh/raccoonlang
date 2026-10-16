package com.raccoonlang

class SubsingletonTests extends munit.FunSuite with TestSupport {

  test("the data Subsingleton family does not accept a proposition as its carrier") {
    expectAnyTypeError(
      """
        |axiom trueSubsingleton : Subsingleton(True)
        |""".stripMargin
    )
  }

  test("distinct proofs remain definitionally equal without a Subsingleton witness") {
    val prelude = TestSupport.preludeAssuming(
      TestSupport.bundledPreludeSource,
      """
        |inductive Amb : Prop
        | | left : Amb
        | | right : Amb
        |""".stripMargin
    )
    val left = runProgram("{ Amb.left }", prelude)
    val right = runProgram("{ Amb.right }", prelude)

    assert(ValueEquivalence.defEq(left, right))
  }
}
