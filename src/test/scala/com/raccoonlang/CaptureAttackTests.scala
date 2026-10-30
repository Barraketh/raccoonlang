package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.Programs

/**
 * Adversarial review of a5e0062e (TypePatternOps.checkOpenedPattern): captures re-checked as the arguments of their
 * heads. A test labelled BREAK is a program that must be refused; every other test is a held attack or a sound control.
 */
class CaptureAttackTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs.runChecked

  private def accepts(src: String)(implicit loc: munit.Location): Unit =
    try { runChecked(src); () }
    catch { case t: TypeError => fail("REJECTED (should accept): " + ErrorReporter.pretty(t, Source(src))) }

  private def rejects(src: String)(implicit loc: munit.Location): TypeError =
    try {
      runChecked(src)
      fail("ACCEPTED (BREAK: should be rejected)")
    } catch {
      case t: TypeError =>
        println(
          s"HELD-BY ${t.getClass.getSimpleName}: ${t.getMessage.linesIterator.nextOption().getOrElse("").take(160)}"
        )
        t
    }

  private val base =
    ProgramFixtures.lnats + ProgramFixtures.both +
      """
        |def SList (A: Sort($u)) : Sort(u) := List(A)
        |""".stripMargin

  // 1. Captures that the opening never collects: under Level.max the level is no capture path, so the declaration is
  // refused (CaptureWithoutOpening).
  test("cap-1 a level capture under Level.max at a binder (uncollected capture)") {
    rejects(base + "def f (A: Sort(Level.max($u, $v))) : Nat := 0\ndef bad : Nat := f(Nat)\n")
  }

  // 2. A capture used twice in one pattern.
  test("cap-2 the same capture name twice in one pattern") {
    rejects(
      base +
        """
          |def K (A: Sort($u))(B: Univ($k, $v)) : Univ(k, v) := B
          |def dupK (x: K($A, $A)) : Prod(A, A) := Prod.mk(A, A, x, x)
          |def bad (s: Protocol.Supply) : Nat := { let p := dupK(s)  0 }
          |""".stripMargin
    )
  }

  // 3. A local head: the higher-order binder's own type fixes the capture's type.
  test("cap-3 a local head of a kind-polymorphic type, given the alias") {
    rejects(
      base +
        """
          |def dupF (F: (A: Univ($k, $u)) -> Univ(k, u))(xs: F($A)) : Prod(F(A), F(A)) := Prod.mk(F(A), F(A), xs, xs)
          |def bad (xs: List(Protocol.Supply)) : Nat := { let p := dupF(SList, xs)  0 }
          |""".stripMargin
    )
  }

  // 4. Lambda conversion: defEq of two lambdas opens the second on the first's generic arguments.
  test("cap-4 eta: a lambda of an alias binder against a kind-polymorphic one") {
    rejects(
      base +
        """
          |def keep (xs: SList($A)) : List(A) := List.append(xs, xs)
          |def ho (f: (xs: List($A)) -> List(A))(ys: List(Protocol.Supply)) : List(Protocol.Supply) := f(ys)
          |def bad (ys: List(Protocol.Supply)) : List(Protocol.Supply) := ho(fun (xs: SList($A)): List(A) => keep(xs), ys)
          |""".stripMargin
    )
  }

  // 5. Sound control: the alias at a copyable list.
  test("cap-5 the alias at a copyable list (sound control)") {
    accepts(
      base + "def keep (xs: SList($A)) : List(A) := List.append(xs, xs)\ndef ok : List(Nat) := keep(List.cons(1, List.nil(Nat)))\n"
    )
  }

  // Was a defect: the declaration checked and every call failed with NotFound. It is refused where it is declared.
  test("cap-1b a Level.max binder declares captures no binding opens, so its declaration is refused") {
    rejects(base + "def f (A: Sort(Level.max($u, $v))) : Nat := 0\n") match {
      case e: CaptureWithoutOpening => assertEquals(e.name, "u")
      case other                    => fail(s"refused by ${other.getClass.getSimpleName}, not CaptureWithoutOpening")
    }
  }

  test("cap-6 defEqPi under a binder: the alias binder in a nested codomain") {
    rejects(
      base +
        """
          |def keep (n: Nat)(xs: SList($A)) : List(A) := List.append(xs, xs)
          |def ho (f: (n: Nat) -> (xs: List($A)) -> List(A))(ys: List(Protocol.Supply)) : List(Protocol.Supply) := f(0, ys)
          |def bad (ys: List(Protocol.Supply)) : List(Protocol.Supply) := ho(keep, ys)
          |""".stripMargin
    )
  }

  test("cap-7 a constructor field with the alias pattern, built at a linear list") {
    rejects(
      base +
        """
          |inductive W (A: Univ($k, $u)) : Univ(k, u)
          | | mk (x: SList($A)) : W(A)
          |
          |def bad (xs: List(Protocol.Supply)) : W(Protocol.Supply) := W.mk(xs)
          |""".stripMargin
    )
  }

  test("cap-8 instance search: a local instance of the alias type at a linear list") {
    rejects(
      base +
        """
          |inductive D (A: Univ($k, $u)) : Univ(k, u)
          | | mk {A: Univ($k, $u)} (f: (x: A) -> Prod(A, A)) : D(A)
          |
          |def instance dl [xs: SList($A)] : D(SList(A)) :=
          |  D.mk(SList(A), fun (x: SList(A)): Prod(SList(A), SList(A)) => Prod.mk(SList(A), SList(A), x, x))
          |def bad (n: Nat) : D(List(Protocol.Supply)) := derive[D(List(Protocol.Supply))]
          |""".stripMargin
    )
  }

  test("cap-9 an erased constructor binder whose type is the alias pattern") {
    rejects(
      base +
        """
          |inductive E (A: Univ($k, $u)) : Univ(k, u)
          | | mk {A: SList($B)} (n: Nat) : E(B)
          |
          |def bad : Nat := 0
          |""".stripMargin
    )
  }

  test("cap-10 alias-6 via a local head: SPair passed as F, duplicating a linear first component") {
    rejects(
      base +
        """
          |def SPair (A: Sort($u))(B: Sort($v)) : Sort(Level.max(u, v)) := Prod(A, B)
          |def dupP (F: (A: Sort($u)) -> (B: Sort($v)) -> Sort(Level.max(u, v)))(p: F($A, $B)) : Prod(F(A, B), F(A, B)) :=
          |  Prod.mk(F(A, B), F(A, B), p, p)
          |def bad (s: Protocol.Supply) : Nat := { let q := dupP(SPair, Prod.mk(Protocol.Supply, Nat, s, 0))  0 }
          |""".stripMargin
    )
  }

  test("cap-11 alias-10 via instance search: an instance of W(Supply) built through the alias") {
    rejects(
      base +
        """
          |inductive W (A: Univ($k, $u)) : Univ(k, u)
          | | mk (x: SList($A)) : W(A)
          |
          |def instance wi [xs: SList($A)] : W(A) := W.mk(xs)
          |def noW (w: W(Protocol.Supply)) : False := {
          |  match w returning False with
          |}
          |def bad (xs: List(Protocol.Supply)) : False := noW(derive[W(Protocol.Supply)])
          |""".stripMargin
    )
  }

  test("cap-12 a constrained kind capture against the alias parameter is refused at declaration") {
    rejects(base + "def f (xs: SList($A in Univ($k, $u))) : Nat := 0\n")
  }

  test("cap-13 alias-20 at Univ parameters: Swap($A, $B) on a linear pair is accepted and stays affine (sound)") {
    accepts(
      base +
        """
          |def Swap (A: Univ($k1, $u))(B: Univ($k2, $v)) : Univ(Kind.join(k1, k2), Level.max(u, v)) := Prod(B, A)
          |def keep (p: Swap($A, $B)) : Prod(B, A) := p
          |def ok (p: Prod(Protocol.Supply, Protocol.Supply)) : Prod(Protocol.Supply, Protocol.Supply) := keep(p)
          |""".stripMargin
    )
  }

  // docs/kernel.md, "Type patterns": a capture under a head that computes reads only positions the head keeps.
  test(
    "cap-14 LIMIT: an alias that nests its argument, S2(A) := List(List(A)), never matches by position (sound refusal)"
  ) {
    rejects(
      base +
        """
          |def S2 (A: Sort($u)) : Sort(u) := SList(SList(A))
          |def keep (xs: S2($A)) : Nat := 0
          |def ok (xs: List(List(Nat))) : Nat := keep(xs)
          |""".stripMargin
    )
  }

  test("cap-15 performance: a ten-deep SList pattern checks quickly (sound control)") {
    val t0 = System.nanoTime()
    accepts(
      base +
        """
          |def deep (xs: SList(SList(SList(SList(SList(SList(SList(SList(SList(SList($A))))))))))) : Nat := 0
          |def ok (xs: List(List(List(List(List(List(List(List(List(List(Nat))))))))))) : Nat := deep(xs)
          |""".stripMargin
    )
    println(s"cap-15 took ${(System.nanoTime() - t0) / 1000000} ms")
  }
}
