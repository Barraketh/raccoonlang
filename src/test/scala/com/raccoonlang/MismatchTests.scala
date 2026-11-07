package com.raccoonlang

import com.raccoonlang.ProgramFixtures._

/**
 * Type-mismatch messages (docs/language.md, "Type mismatches"): the expected type as written, the actual type, the
 * first pair of subterms that differ, and the expected type as it evaluates, with long types abbreviated around the
 * difference.
 */
class MismatchTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs._

  /** The program's mismatch, without variable numbering. */
  private def mismatch(src: String)(implicit loc: munit.Location): String =
    intercept[TypeMismatch](runChecked(src)).getMessage.replaceAll("#[0-9]+", "")

  test("short types print whole, with the first pair of subterms that differ") {
    assertEquals(
      mismatch("def f (a: Nat)(b: Nat) : Eq(Nat, a, b) := Eq.refl(a)\n"),
      "Type mismatch: expected type: Eq(Nat, a, b), actual: Eq(Nat, a, a); first difference: expected b, actual a"
    )
  }

  test("an annotation shows as written, and the type it evaluates to after the difference") {
    assertEquals(
      mismatch("def g (n: Nat) : Nat := Nat.add(n, n)\ndef f : Eq(Nat, g(2), 5) := Eq.refl(5)\n"),
      "Type mismatch: expected type: Eq(Nat, g(2), 5), actual: Eq(Nat, 5, 5); first difference: expected 4, actual 5; " +
        "the expected type evaluates to Eq(Nat, 4, 5)"
    )
  }

  test("a parameter's type shows as written, its earlier parameters as the call's arguments") {
    val needs = "def needs (a: Nat)(b: Nat)(h: Eq(Bool, Nat.ble(a, b), Bool.true)) : Nat := a\n"
    assertEquals(
      mismatch(needs + "def bad (x: Nat) : Nat := needs(Nat.add(x, 5), x, Eq.refl(Bool.true))\n"),
      "Type mismatch: expected type: Eq(Bool, Nat.ble(Nat.add(x, 5), x), Bool.true), actual: Eq(Bool, Bool.true, Bool.true); " +
        "first difference: expected Bool.false, actual Bool.true; the expected type evaluates to Eq(Bool, Bool.false, Bool.true)"
    )
    // An argument too long to show is its parameter's name; a capture shows as its value.
    val long = "Nat.add(Nat.add(Nat.add(x, 1), Nat.add(x, 2)), Nat.add(Nat.add(x, 3), Nat.add(x, 4)))"
    val message = mismatch(needs + s"def bad (x: Nat) : Nat := needs($long, x, Eq.refl(Bool.true))\n")
    assert(message.startsWith("Type mismatch: expected type: Eq(Bool, Nat.ble(a, x), Bool.true), actual:"), message)
  }

  /** `range(lo, n)`, the `n` numbers from `lo`. */
  private val range =
    """
      |def range (lo: Nat)(n: Nat) : List(Nat) decreases structural(n) := {
      |  match n returning List(Nat) with
      |  | Nat.zero => List.nil(Nat)
      |  | Nat.succ k => List.cons(lo, range(Nat.add(lo, 1), k))
      |}
      |""".stripMargin

  test("a long type prints along the path to the difference, other long parts as …") {
    val message = mismatch(
      range + "def bad : Eq(List(Nat), range(0, 60), List.append(range(0, 30), List.cons(99, List.nil(Nat)))) := Eq.refl(range(0, 60))\n"
    )
    // A list shows at most three elements before the one that differs, and none after it.
    assertEquals(
      message,
      "Type mismatch: expected type: Eq(List(Nat), range(0, 60), List.append(range(0, 30), List.cons(99, List.nil(Nat)))), " +
        "actual: Eq(List(Nat), …, […, 27, 28, 29, 30, …]); first difference: expected 99, actual 30; " +
        "the expected type evaluates to Eq(List(Nat), …, […, 27, 28, 29, 99])"
    )
  }

  test("lists that agree on the elements they share differ in what follows them") {
    val message = mismatch(range + "def bad : Eq(List(Nat), range(0, 60), range(0, 30)) := Eq.refl(range(0, 60))\n")
    val rest = (30 until 60).mkString("[", ", ", "]")
    assertEquals(
      message,
      "Type mismatch: expected type: Eq(List(Nat), range(0, 60), range(0, 30)), " +
        s"actual: Eq(List(Nat), …, […, 27, 28, 29] ++ $rest); first difference: expected [], actual $rest; " +
        "the expected type evaluates to Eq(List(Nat), …, […, 27, 28, 29] ++ [])"
    )
  }

  test("a function type's codomain, a lambda's body and a projection's base are looked through") {
    val codomain = mismatch(
      "def f (P: Nat -> Prop)(h: (n: Nat) -> P(n)) : (n: Nat) -> P(Nat.add(n, 1)) := h\n"
    )
    // Two short arguments of an application show with it, which says what they are.
    assert(codomain.contains("first difference: expected P(n + 1), actual P(n)"), codomain)
    val body = mismatch(
      """
        |inductive All (p: Nat -> Bool) : Prop
        | | mk {p: Nat -> Bool} : All(p)
        |
        |def f (a: All(fun (m: Nat): Bool => Bool.and(Nat.isZero(m), Bool.false))) : All(fun (m: Nat): Bool => Bool.and(Nat.isZero(m), Bool.true)) := a
        |""".stripMargin
    )
    // The bodies are matches stuck on `Nat.isZero(m)`, of one code, that captured different second arguments.
    assert(body.contains("first difference: expected Bool.true, actual Bool.false"), body)
    val field = mismatch(
      """
        |inductive Box : Type
        | | mk (n: Nat)(b: Bool) : Box
        |
        |def f (x: Box)(y: Box) : Eq(Nat, x.n, 0) := Eq.refl(y.n)
        |""".stripMargin
    )
    assert(field.contains("first difference: expected x.n, actual y.n"), field)
  }
}
