package com.raccoonlang

class FunctionEqualityTests extends munit.FunSuite {
  private def check(source: String): Option[Value] =
    LanguageParser.parseProgram(source) match {
      case Success(parsed, _, _) => Interpreter.run(Elaborator.elab(parsed, Prelude.test), Prelude.test)
      case failure: Failure      => fail(s"Failed to parse: $failure")
    }

  private def value(term: String): Value = check(s"{ $term }\n").getOrElse(fail("Program has no body"))

  private def assertDifferent(left: String, right: String): Unit = {
    val a = value(left)
    val b = value(right)
    assert(!ValueEquivalence.defEq(a, b), s"Unexpected equality: $left = $right")
    assert(!ValueEquivalence.defEq(b, a), s"Unexpected equality: $right = $left")
  }

  test("regression: a narrow function cannot be stored as a function over a larger universe") {
    val source =
      """
        |def identityType (A: Type): Type := A
        |
        |inductive Store : Sort(Level.succ(Level.one))
        | | mk (f: (A: Sort(Level.one)) -> Type) : Store
        |
        |def lower (s: Store): Type := {
        | match s returning Type with
        | | Store.mk f => f(Type)
        |}
        |
        |lower(Store.mk(identityType))
        |""".stripMargin

    intercept[TypeMismatch] { check(source) }
  }

  test("Pi and lambda equality distinguish universe domains in both directions") {
    assertDifferent("(A: Type) -> Type", "(A: Sort(Level.one)) -> Type")
    assertDifferent(
      "fun (A: Type): Type => Prop",
      "fun (A: Sort(Level.one)): Type => Prop"
    )
  }

  test("Pi equality compares constrained capture classifiers exactly") {
    assertDifferent("(x: $A in Type) -> Type", "(x: $B in Sort(Level.one)) -> Type")
    assertDifferent("(x: $A in Prop) -> Prop", "(x: $B in Type) -> Prop")
  }

  test("Pi equality distinguishes the domains admitted by level capture patterns") {
    assertDifferent("(A: Sort($u)) -> Type", "(A: Sort(Level.succ($v))) -> Type")
    assertDifferent("(A: Type) -> Type", "(A: Sort($u)) -> Type")
  }

  test("equivalent domains and dependent captures compare equally under renaming") {
    val pairs = Vector(
      ("(A: Type) -> (x: A) -> A", "(B: Sort(Level.zero)) -> (y: B) -> B"),
      ("(x: $A in Sort($u)) -> (y: A) -> A", "(z: $B in Sort($v)) -> (w: B) -> B"),
      ("(A: Sort(Level.succ($u))) -> Sort(u)", "(B: Sort(Level.succ($v))) -> Sort(v)")
    )

    pairs.foreach { case (left, right) =>
      val a = value(left)
      val b = value(right)
      assert(ValueEquivalence.defEq(a, b), s"Expected equality: $left = $right")
      assert(ValueEquivalence.defEq(b, a), s"Expected equality: $right = $left")
    }
  }

  test("ordinary argument checking retains universe cumulativity") {
    val result = check(
      """
        |def accept (A: Sort(Level.succ(Level.one))): Sort(Level.succ(Level.one)) := A
        |
        |accept(Type)
        |""".stripMargin
    ).getOrElse(fail("Program has no body"))
    assertEquals(result, Value.TypeTpe)
  }
}
