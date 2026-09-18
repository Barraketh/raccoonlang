package com.raccoonlang

class SubsingletonTests extends munit.FunSuite {
  test("same-proposition proof conversion is subsingleton") {
    val proposition = Value.VConst("P", Value.Symbol, Value.PropTpe)
    val left = Value.VProof(proposition)
    val right = Value.VApp(Value.VConst("w", Value.Symbol, proposition), Vector.empty, proposition)
    assert(ValueEquivalence.defEq(left, right))
  }

  test("different propositions are not identified by proof irrelevance") {
    val p = Value.VConst("P", Value.Symbol, Value.PropTpe)
    val q = Value.VConst("Q", Value.Symbol, Value.PropTpe)
    assert(!ValueEquivalence.defEq(Value.VProof(p), Value.VProof(q)))
  }
}
