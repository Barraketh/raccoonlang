package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.Programs

/**
 * Fixes, each with programs that must check and controls that must still be refused:
 *  - a match's motive taken from the context is quoted in the match's scope when its own binders are numbered below it
 *    (`MatchChecker`, `CapturedIndexes.bindsBelow`);
 *  - `rewrite` against a goal written as a `let`'s name quotes it through the `let`'s value (`Rewrite.plan`);
 *  - a `$` capture inside a constructor of a parameterized family reads its stored fields after the erased family
 *    arguments, and an erased argument off the value's type (`TypePatternOps.project`);
 *  - a stuck match is identified by the record fields it reads (`MatchIdentity`), each projected only from a value of
 *    the record the code names: resumed where a refinement retypes the local as another record, it is captured whole.
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

  private val rec =
    """
      |inductive Rec : Type
      | | mk (a: Nat)(b: Nat) : Rec
      |inductive Sp : Type
      | | one (u: Nat) : Sp
      | | two : Sp
      |def bump (r: Rec): Rec := Rec.mk(r.a, Nat.succ(r.b))
      |""".stripMargin

  test("a stuck match over a record converts with the same match over a record agreeing on the fields it reads") {
    accepts(
      rec +
        """
          |def get (r: Rec)(sp: Sp): Bool := {
          |  match sp with
          |  | Sp.one u => Nat.beq(u, r.a)
          |  | Sp.two => Bool.false
          |}
          |def same (r: Rec)(sp: Sp)(h: Eq(Bool, get(r, sp), Bool.true)): Eq(Bool, get(bump(r), sp), Bool.true) := h
          |def five : Eq(Bool, get(Rec.mk(5, 0), Sp.one(5)), Bool.true) := Eq.refl(Bool.true)
          |""".stripMargin
    )
  }

  test("control: a stuck match reading a field the records disagree on, or the record whole, does not convert") {
    rejects(
      rec +
        """
          |def get (r: Rec)(sp: Sp): Bool := {
          |  match sp with
          |  | Sp.one u => Nat.beq(u, r.b)
          |  | Sp.two => Bool.false
          |}
          |def same (r: Rec)(sp: Sp)(h: Eq(Bool, get(r, sp), Bool.true)): Eq(Bool, get(bump(r), sp), Bool.true) := h
          |""".stripMargin
    )
    rejects(
      rec +
        """
          |def sum (r: Rec): Nat := Nat.add(r.a, r.b)
          |def get (r: Rec)(sp: Sp): Bool := {
          |  match sp with
          |  | Sp.one u => Nat.beq(u, r.a)
          |  | Sp.two => Nat.beq(sum(r), 0)
          |}
          |def same (r: Rec)(sp: Sp)(h: Eq(Bool, get(r, sp), Bool.true)): Eq(Bool, get(bump(r), sp), Bool.true) := h
          |""".stripMargin
    )
  }

  // `P(w)` is `Prod` at `true` and another record at `false`; `pick`'s match reads `h` only as `h.fst` or `h.snd`, typed
  // under its case's refinement. `same` blocks the match on `w`, so refining `w` to `false` resumes it, with `h` retyped.
  private def retyped(other: String, field: String): String =
    s"""
      |inductive Is indices (w: Bool) : Type
      | | yes : Is(Bool.true)
      | | no : Is(Bool.false)
      |inductive Box : Type
      | | mk (v: Nat) : Box
      |def P (w: Bool): Type := Bool.cond(w, Type, Prod(Nat, Nat), $other)
      |def same (w: Bool)(m: Is(w)): Is(w) := {
      |  match w with
      |  | Bool.true => m
      |  | Bool.false => m
      |}
      |def pick (w: Bool)(m: Is(w))(h: P(w)): Nat := {
      |  match m returning Nat with
      |  | Is.yes => h.$field
      |  | Is.no => 0
      |}
      |""".stripMargin

  test("a stuck match reading a record's field, resumed where a refinement makes the local another record") {
    val body =
      """
        |def t (w: Bool)(m: Is(w))(h: P(w)): Nat := {
        |  let g := pick(w, same(w, m), h)
        |  match w returning Nat with
        |  | Bool.true => g
        |  | Bool.false => g
        |}
        |""".stripMargin
    // A record of no fields, and one of fewer fields than the field read.
    accepts(retyped("Unit", "fst") + body)
    accepts(retyped("Box", "snd") + body)
  }

  test("control: the retyped stuck match still computes nothing it cannot") {
    rejects(
      retyped("Unit", "fst") +
        """
          |def t (w: Bool)(m: Is(w))(h: P(w)): Eq(Nat, pick(w, same(w, m), h), 0) := {
          |  let g := pick(w, same(w, m), h)
          |  match w returning Eq(Nat, g, 0) with
          |  | Bool.true => Eq.refl(0)
          |  | Bool.false => Eq.refl(0)
          |}
          |""".stripMargin
    )
  }

  // `at`'s match reads `h` only as `h.left` and `h.right`, where `Every(xs, f)` is `And`; at `nil` it is `True`, a
  // record of no fields. The rewrite's motive holds `count`'s match on `W`, whose `nil` case refines `W` with the
  // let-bound proof live, which quoting the goal forced.
  private val every =
    """
      |inductive Rec : Type
      | | mk (k: Nat)(n: Nat) : Rec
      |def Every (xs: List(Rec))(f: Rec -> Prop): Prop decreases structural(xs) := {
      |  match xs returning Prop with
      |  | List.nil => True
      |  | List.cons x rest => And(f(x), Every(rest, f))
      |}
      |def at (f: Rec -> Prop)(xs: List(Rec))(h: Every(xs, f))(a: Rec)(m: List.Mem(Rec, a, xs)): f(a) decreases structural(m) := {
      |  match m returning f(a) with
      |  | List.Mem.head y ys => h.left
      |  | List.Mem.tail y z zs old => at(f, zs, h.right, y, old)
      |}
      |def count (W: List(Rec))(k: Nat): Nat decreases structural(W) := {
      |  match W returning Nat with
      |  | List.nil => k
      |  | List.cons x rest => Nat.add(count(rest, k), Bool.cond(Nat.beq(x.k, k), Nat, 1, 0))
      |}
      |def same (W: List(Rec))(y: Rec)(m: List.Mem(Rec, y, W)): List.Mem(Rec, y, W) := {
      |  match W with
      |  | List.nil => m
      |  | List.cons x rest => m
      |}
      |""".stripMargin

  private def atKind(goal: String, step: String): String =
    every +
      s"""
        |def t (W: List(Rec))(kd: Nat)(y: Rec)(m: List.Mem(Rec, y, W))(e: Eq(Nat, y.k, kd))
        |    (ev: Every(W, fun (z: Rec): Prop => Eq(Nat, count(W, kd), z.n))): $goal := {
        |  let g : Eq(Nat, count(W, kd), y.n) := at(fun (z: Rec): Prop => Eq(Nat, count(W, kd), z.n), W, ev, y, same(W, y, m))
        |  rewrite [$step] in g
        |}
        |""".stripMargin

  test("`rewrite` of a let-bound proof whose stuck match reads fields of a local the motive's cases retype") {
    accepts(atKind("Eq(Nat, count(W, y.k), y.n)", "e"))
  }

  test("control: the rewrite still checks the rewritten goal and its direction") {
    rejects(atKind("Eq(Nat, count(W, y.k), Nat.succ(y.n))", "e"))
    rejects(atKind("Eq(Nat, count(W, y.k), y.n)", "<- e"))
  }
}
