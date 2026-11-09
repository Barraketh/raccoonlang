package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.Programs

/**
 * Three fixes, each with programs that must check and controls that must still be refused:
 *  - a match's motive taken from the context is quoted in the match's scope when its own binders are numbered below it
 *    (`MatchChecker`, `CapturedIndexes.bindsBelow`);
 *  - `rewrite` against a goal written as a `let`'s name quotes it through the `let`'s value (`Rewrite.plan`);
 *  - a `$` capture inside a constructor of a parameterized family reads its stored fields after the erased family
 *    arguments, and an erased argument off the value's type (`TypePatternOps.project`).
 */
class ScopeAndCaptureFixTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs.runChecked

  private def accepts(src: String)(implicit loc: munit.Location): Unit =
    try { runChecked(src); () }
    catch { case t: TypeError => fail("REJECTED (should accept): " + ErrorReporter.pretty(t, Source(src))) }

  private def rejects(src: String)(implicit loc: munit.Location): Unit =
    try {
      runChecked(src)
      fail("ACCEPTED (should be rejected)")
    } catch { case _: TypeError => () }

  private val restore =
    """
      |def putF (R: Nat -> Nat)(id: Nat)(s: Nat): Nat -> Nat := fun (x: Nat): Nat => Bool.cond(Nat.beq(x, id), Nat, s, R(x))
      |def restoreF (R: Nat -> Nat)(saved: List(Prod(Nat, Nat))): Nat -> Nat decreases structural(saved) := {
      |  match saved with
      |  | List.nil => R
      |  | List.cons p rest => restoreF(putF(R, p.fst, p.snd), rest)
      |}
      |""".stripMargin

  test("a recursive function returning a function type, its match with no `returning`, converts at its stuck call") {
    accepts(
      restore +
        """
          |def same (Rg: Nat -> Nat)(saved: List(Prod(Nat, Nat)))(h: Eq(Nat -> Nat, restoreF(Rg, saved), restoreF(Rg, saved))): Eq(Nat -> Nat, restoreF(Rg, saved), restoreF(Rg, saved)) := h
          |""".stripMargin
    )
  }

  test("the same stuck call in an inductive's index") {
    accepts(
      restore +
        """
          |inductive Stk indices (Rg: Nat -> Nat)(c: Nat) : Prop
          | | exit (Rg: Nat -> Nat) : Stk(Rg, 0)
          | | block (Rg: Nat -> Nat)(saved: List(Prod(Nat, Nat)))(ck: Nat)(k: Stk(restoreF(Rg, saved), ck)) : Stk(Rg, ck)
          |""".stripMargin
    )
  }

  test("control: the recursive function still computes, and a wrong value is refused") {
    accepts(
      restore + "def five (R: Nat -> Nat): Eq(Nat, restoreF(R, List.cons(Prod.mk(Nat, Nat, 0, 5), List.nil(Prod(Nat, Nat))))(0), 5) := Eq.refl(5)\n"
    )
    rejects(
      restore + "def wrong (R: Nat -> Nat): Eq(Nat, restoreF(R, List.cons(Prod.mk(Nat, Nat, 0, 5), List.nil(Prod(Nat, Nat))))(0), R(0)) := Eq.refl(R(0))\n"
    )
  }

  test("an empty match under a case's fields inside `rewrite`") {
    accepts(
      """
        |def f (a: Nat)(b: Nat)(q: Eq(Nat, a, b))(h: Or(True, False)): Nat.le(a, b) := {
        |  let apart := fun (x: False): False => x
        |  rewrite q in {
        |    match h with
        |    | Or.inl t => Eq.refl(Bool.true)
        |    | Or.inr no => {
        |      match apart(no) with
        |    }
        |  }
        |}
        |""".stripMargin
    )
  }

  test("control: a match with no `returning` still refines hypotheses and refuses a wrong case") {
    val own =
      """
        |inductive Spot : Type
        | | thread (u: Nat) : Spot
        | | cur (i: Nat) : Spot
        |def Own (a: Nat)(sp: Spot): Prop := {
        |  match sp returning Prop with
        |  | Spot.thread u => Eq(Nat, u, a)
        |  | Spot.cur i => Eq(Nat, i, 0)
        |}
        |""".stripMargin
    accepts(
      own + """
        |def ok (a: Nat)(b: Nat)(e: Eq(Nat, b, a))(sp: Spot)(h: Own(a, sp)): Own(b, sp) := {
        |  match sp with
        |  | Spot.thread u => Eq.trans(h, Eq.symm(e))
        |  | Spot.cur i => h
        |}
        |""".stripMargin
    )
    rejects(
      own + """
        |def bad (a: Nat)(b: Nat)(e: Eq(Nat, b, a))(sp: Spot)(h: Own(a, sp)): Own(b, sp) := {
        |  match sp with
        |  | Spot.thread u => h
        |  | Spot.cur i => h
        |}
        |""".stripMargin
    )
  }

  private val pick = "def pick (b: Bool)(n: Nat): Nat := Bool.cond(b, Nat, n, 0)\n"

  test("`rewrite` against a goal written as a `let`'s name") {
    accepts(
      pick +
        """
          |def viaLet (b: Bool)(n: Nat)(h: Eq(Bool, b, Bool.true)): Eq(Nat, pick(b, n), n) := {
          |  let G := Eq(Nat, pick(b, n), n)
          |  (fun (h2: Eq(Bool, b, Bool.true)): G => rewrite h2 in Eq.refl(n))(h)
          |}
          |""".stripMargin
    )
  }

  test("control: `rewrite` through a `let`'s goal still checks the rewritten goal") {
    rejects(
      pick +
        """
          |def wrong (b: Bool)(n: Nat)(h: Eq(Bool, b, Bool.true)): Eq(Nat, pick(b, n), 0) := {
          |  let G := Eq(Nat, pick(b, n), 0)
          |  (fun (h2: Eq(Bool, b, Bool.true)): G => rewrite h2 in Eq.refl(n))(h)
          |}
          |""".stripMargin
    )
  }

  private val tile =
    """
      |inductive G (S: Type) : Type
      | | tile {S: Type} (ty: Nat)(o: Bool) : G(S)
      |inductive Box (S: Type) indices (g: G(S)) : Type
      | | mk {S: Type} (g: G(S)) : Box(S, g)
      |def tyOf (b: Box($S, G.tile(S, $ty, $o))): Nat := ty
      |def oOf (b: Box($S, G.tile(S, $ty, $o))): Bool := o
      |""".stripMargin

  test("a `$` capture inside a parameterized constructor reads the field it names") {
    accepts(tile + "def three (S: Type): Eq(Nat, tyOf(Box.mk(S, G.tile(S, 3, Bool.true))), 3) := Eq.refl(3)\n")
    accepts(tile + "def yes (S: Type): Eq(Bool, oOf(Box.mk(S, G.tile(S, 3, Bool.true))), Bool.true) := Eq.refl(Bool.true)\n")
  }

  test("control: a captured field's value is the stored one, and other values are refused") {
    rejects(tile + "def wrong (S: Type): Eq(Nat, tyOf(Box.mk(S, G.tile(S, 3, Bool.true))), 4) := Eq.refl(4)\n")
    rejects(tile + "def wrong (S: Type): Eq(Bool, oOf(Box.mk(S, G.tile(S, 3, Bool.true))), Bool.false) := Eq.refl(Bool.false)\n")
  }
}
