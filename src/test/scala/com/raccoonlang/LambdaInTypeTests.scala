package com.raccoonlang

import com.raccoonlang.ProgramFixtures.Programs

/**
 * Lambdas in types (KERNEL_FOLLOWUPS 2.8; docs/kernel.md, "Lambdas in types"): a lambda may stand wherever a type holds
 * a term, as an application's argument in a binder type, a codomain, a `let` annotation, a field type or a motive. It
 * is an ordinary checked lambda: F4 and F5 apply to it, and positivity and the size rules read it as a function value.
 */
class LambdaInTypeTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = true)
  import programs._

  /** `All(xs, p)`, a family over a predicate, and `Every`, the predicate as a computed proposition. */
  private val lib =
    ProgramFixtures.lnats +
      """
        |inductive All (xs: List(Nat))(p: Nat -> Prop) : Prop
        | | mk {xs: List(Nat)}{p: Nat -> Prop} : All(xs, p)
        |
        |def Every (xs: List($A in Sort($u)))(f: A -> Prop): Prop decreases structural(xs) := {
        |  match xs returning Prop with
        |  | List.nil => True
        |  | List.cons x rest => And(f(x), Every(rest, f))
        |}
        |
        |def everyTrue (xs: List(Nat)): Every(xs, fun (x: Nat): Prop => True) decreases structural(xs) := {
        |  match xs returning Every(xs, fun (x: Nat): Prop => True) with
        |  | List.nil => True.intro
        |  | List.cons x rest => And.intro(True, Every(rest, fun (y: Nat): Prop => True), True.intro, everyTrue(rest))
        |}
        |
        |""".stripMargin

  test("a lambda parses and checks in a binder type, a codomain, an annotation and a motive") {
    assertEquals(
      result(
        lib +
          """
            |def needs (xs: List(Nat))(h: Every(xs, fun (x: Nat): Prop => True)) : Nat := List.length(xs)
            |
            |def annotated (xs: List(Nat)) : Nat := {
            |  let h : Every(xs, fun (z: Nat): Prop => True) := everyTrue(xs)
            |  needs(xs, h)
            |}
            |
            |annotated(List.cons(4, List.cons(5, List.nil(Nat))))
            |""".stripMargin
      ),
      "2"
    )
  }

  test("lambdas in types convert by their bodies on fresh arguments, not by their names") {
    run(
      lib +
        "def same (xs: List(Nat))(h: Every(xs, fun (a: Nat): Prop => Eq(Nat, a, a))): " +
        "Every(xs, fun (b: Nat): Prop => Eq(Nat, b, b)) := h\n"
    )
    intercept[TypeMismatch](
      runChecked(
        lib +
          "def other (xs: List(Nat))(h: Every(xs, fun (a: Nat): Prop => True)): " +
          "Every(xs, fun (b: Nat): Prop => False) := h\n"
      )
    )
  }

  test("a lambda in a type pattern stands beside a capture") {
    assertEquals(
      result(
        lib +
          """
            |def items (h: All($xs, fun (n: Nat): Prop => True)) : List(Nat) := xs
            |
            |items(All.mk(List.cons(1, List.nil(Nat)), fun (n: Nat): Prop => True))
            |""".stripMargin
      ),
      "[1]"
    )
  }

  test("a lambda as a whole binder type is NotAType") {
    intercept[NotAType](runChecked(lib + "def f (x: fun (y: Nat): Nat => y) : Nat := 0\n"))
  }

  test("a field type may hold a lambda, and a record's projections state it with the earlier fields projected") {
    assertEquals(
      result(
        lib +
          """
            |inductive Bounded : Type
            | | mk (bound: Nat)(xs: List(Nat))(ok: All(xs, fun (x: Nat): Prop => Nat.le(x, bound))) : Bounded
            |
            |def okOf (b: Bounded) : All(b.xs, fun (x: Nat): Prop => Nat.le(x, b.bound)) := b.ok
            |
            |List.length(Bounded.mk(3, List.cons(1, List.nil(Nat)), All.mk(List.cons(1, List.nil(Nat)), fun (x: Nat): Prop => Nat.le(x, 3))).xs)
            |""".stripMargin
      ),
      "1"
    )
  }

  // A projection's type is the field's own, so a name the lambda rebinds is never mistaken for the field `n`.
  test("a lambda's parameter, a case field and a let shadow an earlier field in a projection's type") {
    run(
      lib +
        """
          |inductive S : Type
          | | mk (n: Nat)(xs: List(Nat))(p: All(xs, fun (n: Nat): Prop => Nat.le(n, 3)))
          |     (q: All(xs, fun (x: Nat): Prop => match List.cons(x, List.nil(Nat)) returning Prop with
          |       | List.cons n rest => Nat.le(n, 3)
          |     ))
          |     (r: All(xs, fun (x: Nat): Prop => {
          |       let n := x
          |       Nat.le(n, 3)
          |     })) : S
          |
          |def nOf (s: S) : Nat := s.n
          |def pOf (s: S) : All(s.xs, fun (k: Nat): Prop => Nat.le(k, 3)) := s.p
          |def qOf (s: S) : All(s.xs, fun (k: Nat): Prop => Nat.le(k, 3)) := s.q
          |def rOf (s: S) : All(s.xs, fun (k: Nat): Prop => Nat.le(k, 3)) := s.r
          |""".stripMargin
    )
  }

  // As every stuck match, a lambda's body stuck on its own match converts by the match's identity, so only with itself.
  test("lambdas whose bodies are stuck on matches written apart do not convert") {
    intercept[TypeMismatch](
      runChecked(
        lib +
          """
            |def apart (xs: List(Nat))(h: All(xs, fun (x: Nat): Prop => match x returning Prop with
            |  | Nat.zero => True
            |  | Nat.succ k => False
            |)) : All(xs, fun (x: Nat): Prop => match x returning Prop with
            |  | Nat.zero => True
            |  | Nat.succ k => False
            |) := h
            |""".stripMargin
      )
    )
  }

  // F5: a type is a read, but a lambda in it still captures no linear local.
  test("F5: a lambda in a codomain or a binder type captures no linear local") {
    assertErrorAt[LinearCapture](
      lib +
        "def bad (xs: LNats)(h: All(List.nil(Nat), fun (n: Nat): Prop => Eq(Nat, n, count(xs)))) : Nat := count(xs)\n",
      "xs",
      within = "count(xs))))"
    )
    assertErrorAt[LinearCapture](
      lib + "def bad (xs: LNats) : All(List.nil(Nat), fun (n: Nat): Prop => Eq(Nat, n, count(xs))) := All.mk\n",
      "xs",
      within = "count(xs)))"
    )
  }

  // S1 and F4: a lambda in a type may have a linear parameter, which its body uses at most once.
  test("S1 and F4: a lambda in a type with a linear parameter uses it at most once") {
    run(lib + "def ok (n: Nat)(h: Eq((t: LNats) -> Nat, fun (t: LNats): Nat => count(t), count)) : Nat := n\n")
    assertErrorAt[LinearReused](
      lib + "def bad (n: Nat)(h: Eq((t: LNats) -> Nat, fun (t: LNats): Nat => Nat.add(count(t), count(t)), count)) : Nat := n\n",
      "t",
      within = "(t)), count)"
    )
  }

  test("positivity opens a lambda in a field type on fresh arguments: the family may not occur in its body") {
    run(lib + "inductive T : Type\n | leaf : T\n | node (h: All(List.nil(Nat), fun (n: Nat): Prop => True)) : T\n")
    intercept[NonStrictlyPositive](
      runChecked(
        lib +
          "inductive T : Type\n | leaf : T\n | node (h: All(List.nil(Nat), fun (n: Nat): Prop => Eq(Type, T, T))) : T\n"
      )
    )
    // A stuck body that names the family certifies nothing either.
    intercept[NonStrictlyPositive](
      runChecked(
        lib +
          """
            |inductive T : Type
            | | leaf : T
            | | node (h: All(List.nil(Nat), fun (n: Nat): Prop => {
            |     match n returning Prop with
            |     | Nat.zero => Eq(Type, T, T)
            |     | Nat.succ k => True
            |   })) : T
            |""".stripMargin
      )
    )
  }

  test("the size rules read a lambda in a field or parameter type by the type it gives") {
    // Two constructors, so a holder is no record, which the size rule would charge by its fields.
    val holder =
      lib +
        "inductive Holder (F: Nat -> Sort(Level.one)) : Sort(Level.one)\n" +
        " | a {F: Nat -> Sort(Level.one)} : Holder(F)\n | b {F: Nat -> Sort(Level.one)} : Holder(F)\n\n"
    run(holder + "inductive Big : Sort(Level.one)\n | mk (h: Holder(fun (n: Nat): Sort(Level.one) => Type)) : Big\n")
    intercept[InductiveUniverseTooSmall](
      runChecked(holder + "inductive Small : Type\n | mk (h: Holder(fun (n: Nat): Sort(Level.one) => Type)) : Small\n")
    )
    intercept[FamilyArgumentTooLarge](
      runChecked(holder + "inductive W (h: Holder(fun (n: Nat): Sort(Level.one) => Type)) : Type\n")
    )
  }
}
