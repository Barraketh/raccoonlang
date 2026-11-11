package com.raccoonlang

import com.raccoonlang.ProgramFixtures.Programs

/**
 * A diagnostic prints values within a budget (`Mismatch.Bounds`; docs/language.md, "Type mismatches"), so printing an
 * error never exhausts the heap. Here the values are trees of 2^40 leaves, shared down one path, whose text as a whole
 * no heap holds: each prints in at most the budget's characters, quickly, with what it leaves out marked by how much,
 * its first difference whole, and its text in order through a Nat form and a closure's captured value. A short message
 * is as it was.
 */
class MessageBudgetTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs.runChecked

  /** The program's error message, without variable numbering, and the seconds printing it took. */
  private def message(src: String)(implicit loc: munit.Location): (String, Double) = {
    val error = intercept[TypeError](runChecked(src))
    val start = System.nanoTime()
    val text = error.getMessage
    (text.replaceAll("#[0-9]+", ""), (System.nanoTime() - start) / 1e9)
  }

  private val bounds = Mismatch.bounds
  private val past = s"…(over ${bounds.measure} chars)"

  /** A message of `values` printed values, each at most the cap and a marker, that took at most a few seconds. */
  private def bounded(text: String, seconds: Double, values: Int)(implicit loc: munit.Location): Unit = {
    assert(text.length <= values * (bounds.cap + past.length) + 200, s"${text.length} characters: $text")
    assert(seconds < 5, s"$seconds seconds to print")
    assert(text.contains(past), text)
  }

  private val tree =
    """
      |inductive T : Type
      | | leaf : T
      | | node (l: T)(r: T) : T
      |
      |def tree (n: Nat) : T decreases structural(n) := {
      |  match n returning T with
      |  | Nat.zero => T.leaf
      |  | Nat.succ k => {
      |    let t := tree(k)
      |    T.node(t, t)
      |  }
      |}
      |""".stripMargin

  test("a mismatch of huge values prints within the budget, quickly, its first difference whole") {
    val (text, seconds) = message(tree + "def bad : Eq(T, tree(40), tree(39)) := Eq.refl(tree(40))\n")
    bounded(text, seconds, values = 5)
    assert(
      text.startsWith(s"Type mismatch: expected type: Eq(T, tree(40), tree(39)), actual: Eq(T, $past, T.node(T.node("),
      text
    )
    // Along the path to the difference, each other part prints whole up to `bounds.part` characters, and otherwise as
    // `…` and its length; the type as a whole is clipped, with how much it leaves out.
    assert(text.contains("T.node(T.node(T.leaf, T.leaf), T.node(T.leaf, T.leaf))), …(118 chars)), …(246 chars))"), text)
    assert(text.contains("first difference: expected T.leaf, actual T.node(T.leaf, T.leaf)"), text)
  }

  test("a huge value in a closure, under a Nat form, prints within the budget, in order") {
    val (text, seconds) = message(
      tree +
        """
          |def leaves (t: T) : Nat decreases structural(t) := {
          |  match t returning Nat with
          |  | T.leaf => 1
          |  | T.node l r => Nat.add(leaves(l), leaves(r))
          |}
          |
          |def pick (x: Nat)(t: T) : Nat := {
          |  match x returning Nat with
          |  | Nat.zero => 0
          |  | Nat.succ k => leaves(t)
          |}
          |
          |def bad (x: Nat) : Eq(Nat, Nat.add(Nat.mul(2, pick(x, tree(40))), 1), 1) := Eq.refl(1)
          |""".stripMargin
    )
    bounded(text, seconds, values = 3)
    // The stuck match's syntax, its captured tree printed in place.
    assert(
      text.contains(
        "first difference: expected 2 * match x returning Nat with | Nat.zero => 0 | Nat.succ k => leaves(T.node(T.node("
      ),
      text
    )
  }

  test("a capture that cannot be read off a huge type names the type within the budget") {
    val (text, seconds) = message(
      tree +
        """
          |inductive Box (A: Type) : Type
          | | mk {A: Type}(a: A) : Box(A)
          |
          |def unbox (b: Box($A)) : A := {
          |  match b returning A with
          |  | Box.mk a => a
          |}
          |
          |inductive Tag (t: T) : Type
          | | mk {t: T} : Tag(t)
          |
          |def Ty (x: Nat)(t: T) : Type := {
          |  match x returning Type with
          |  | Nat.zero => Nat
          |  | Nat.succ k => Tag(t)
          |}
          |
          |def bad (x: Nat)(y: Ty(x, tree(40))) : Nat := unbox(y)
          |""".stripMargin
    )
    bounded(text, seconds, values = 1)
    assert(
      text.startsWith(
        "The type-pattern capture $A cannot be read off match x returning Type with | Nat.zero => Nat | Nat.succ k => Tag(T.node("
      ),
      text
    )
    assert(text.endsWith(s"$past, which has no argument 0"), text)
  }

  test("short messages are unchanged") {
    def same(src: String, expected: String)(implicit loc: munit.Location): Unit = assertEquals(message(src)._1, expected)
    same(
      "def f (a: Nat)(b: Nat) : Eq(Nat, a, b) := Eq.refl(a)\n",
      "Type mismatch: expected type: Eq(Nat, a, b), actual: Eq(Nat, a, a); first difference: expected b, actual a"
    )
    same(
      "def g (n: Nat) : Nat := Nat.add(n, n)\ndef f : Eq(Nat, g(2), 5) := Eq.refl(5)\n",
      "Type mismatch: expected type: Eq(Nat, g(2), 5), actual: Eq(Nat, 5, 5); first difference: expected 4, actual 5; " +
        "the expected type evaluates to Eq(Nat, 4, 5)"
    )
    same(
      "inductive Box (A: Type) : Type\n | mk {A: Type}(a: A) : Box(A)\n\n" +
        "def unbox (b: Box($A)) : A := {\n  match b returning A with\n  | Box.mk a => a\n}\n\ndef bad : Nat := unbox(Nat.zero)\n",
      "The type-pattern capture $A cannot be read off Nat, which has no argument 0"
    )
    same(
      "def f (g: Nat -> Nat) : Nat := {\n  match g returning Nat with\n  | Nat.zero => 0\n}\n",
      "Cannot match on non-inductive type Nat -> Nat"
    )
    same("def f (x: Nat.add(1, 2)) : Nat := 0\n", "3 is not a type")
  }
}
