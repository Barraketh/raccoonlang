package com.raccoonlang

class CoreLanguageTests extends munit.FunSuite with TestSupport {
  test("numerals and source arithmetic produce ordinary constructor trees") {
    val result = runProgram("{ Nat.add(2, 3) }")
    def size(value: Value): Int = value match {
      case Value.VCtor(head, Vector(), _) if head.name == "Nat.zero"         => 0
      case Value.VCtor(head, Vector(previous), _) if head.name == "Nat.succ" => 1 + size(previous)
      case other => fail(s"Expected an ordinary Nat constructor, got $other")
    }
    assertEquals(size(result), 5)
    assert(ValueEquivalence.defEq(result, runProgram("{ 5 }")))
  }

  test("a custom prelude has no special Nat layout or arithmetic signature") {
    val prelude = Prelude.fromSource(
      "ordinary-nat",
      """inductive Nat : Type
        | | zero : Nat
        | | succ (n: Nat) : Nat
        | | extra : Nat
        |
        |namespace Nat {
        |  def add (n: Nat): Nat := n
        |}
        |""".stripMargin
    )
    assertEquals(PrettyPrinter.print(runProgram("{ Nat.add(2) }", prelude)), "2")
    assertEquals(ctorName(runProgram("{ Nat.extra }", prelude)), "Nat.extra")
  }

  test("locals can be duplicated, discarded and captured by ordinary functions") {
    val source =
      """def discard (A: Type)(x: A): Nat := 0
        |def duplicate (A: Type)(x: A): Prod(A, A) := Prod.mk(x, x)
        |def capture (A: Type)(x: A): Unit -> A := fun (u: Unit): A => x
        |{ Nat.add(discard(Nat, 9), capture(Nat, Prod.snd(duplicate(Nat, 4)))(Unit.unit)) }
        |""".stripMargin
    assertEquals(PrettyPrinter.print(runProgram(source)), "4")
  }

  test("a program can define its own Nat without a prelude") {
    val source =
      """inductive Nat : Type
        | | zero : Nat
        | | succ (n: Nat) : Nat
        |{ 2 }
        |""".stripMargin
    assertEquals(PrettyPrinter.print(runProgram(source, Prelude.none)), "2")
  }

  test("sort fields only accept universe levels") {
    for (field <- Vector("kind", "scope")) {
      LanguageParser.parseProgram(s"{ Type { $field = one } }") match {
        case Failure(_, _, message) => assert(message.contains(s"Unknown field $field"))
        case other                  => fail(s"Expected rejection of removed sort field, got $other")
      }
    }
  }
}
