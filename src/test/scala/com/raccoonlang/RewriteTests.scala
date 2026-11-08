package com.raccoonlang

import com.raccoonlang.ProgramFixtures._

/**
 * Goal-directed rewriting, `rewrite h in e` (docs/language.md, "Rewriting"): sugar for the `Eq.substProp` call a user
 * would write, whose motive abstracts one side of the equation in the type expected of the rewrite, checked as that
 * call.
 */
class RewriteTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs._

  /** `isZero`, a computed `Bool`, and `pick`, a list that a `Bool.cond` on it is stuck on for a variable. */
  private val pick =
    """
      |def isZero (n: Nat) : Bool := {
      |  match n returning Bool with
      |  | Nat.zero => Bool.true
      |  | Nat.succ k => Bool.false
      |}
      |
      |def pick (n: Nat) : List(Nat) := Bool.cond(isZero(n), List(Nat), List.cons(n, List.nil(Nat)), List.nil(Nat))
      |""".stripMargin

  /** A match on a computed scrutinee, as a downstream project's `Statements.coordinate` writes one. */
  private val coordinate =
    """
      |def coordinate (n: Nat)(k: Nat): Option(Nat) := {
      |  match Nat.ble(2147483648, n) returning Option(Nat) with
      |  | Bool.false => Option.some(Nat.add(n, k))
      |  | Bool.true => {
      |    let below := Nat.sub(4294967296, n)
      |    Bool.cond(Nat.ble(below, k), Option(Nat), Option.some(Nat.sub(k, below)), Option.none(Nat))
      |  }
      |}
      |""".stripMargin

  /** The checked body of the definition `name` of `src`, as source. */
  private def residualOf(src: String, name: String)(implicit loc: munit.Location): String =
    declsEnv(src).apply(name) match {
      case Value.VLam(_, _, Value.LamBody.Core(term, _)) => PrettyPrinter.printElabTerm(term.body)
      case other                                         => fail(s"$name is no function: $other")
    }

  test("a rewrite abstracts the left side in the goal and checks its body at the right") {
    run(
      """
        |def forward (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Nat.le(b, 3)) : Nat.le(a, 3) := rewrite e in p
        |def backward (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Nat.le(a, 3)) : Nat.le(b, 3) := rewrite <- e in p
        |def all (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Eq(Nat, Nat.add(b, b), b)) : Eq(Nat, Nat.add(a, a), a) :=
        |  rewrite e in p
        |""".stripMargin
    )
  }

  test("it is exactly the call a user writes: Eq.substProp, through Eq.symm unless reversed") {
    // The motive is the goal as it evaluates, `Nat.le` unfolded, with the side abstracted.
    val src =
      """
        |def forward (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Nat.le(b, 3)) : Nat.le(a, 3) := rewrite e in p
        |def backward (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Nat.le(a, 3)) : Nat.le(b, 3) := rewrite <- e in p
        |""".stripMargin
    assertEquals(
      residualOf(src, "forward"),
      "Eq.substProp(Eq.symm(e), (fun (_rewritten: Nat): Prop => Eq(Bool, Nat.ble(_rewritten, 3), Bool.true)), p)"
    )
    assertEquals(
      residualOf(src, "backward"),
      "Eq.substProp(e, (fun (_rewritten: Nat): Prop => Eq(Bool, Nat.ble(_rewritten, 3), Bool.true)), p)"
    )
  }

  test("a scrutinee that evaluation removed from the body's type is found in the goal's evaluated form") {
    // `List.Mem.head` proves membership in `[n]`; the goal is membership in `pick(n)`, a `Bool.cond` stuck on
    // `isZero(n)`. Rewriting the proof's type forward could not work: `Bool.true` no longer occurs in it.
    run(
      pick +
        """
          |def member (n: Nat)(z: Eq(Bool, isZero(n), Bool.true)) : List.Mem(Nat, n, pick(n)) :=
          |  rewrite z in List.Mem.head(n, List.nil(Nat))
          |
          |def absent (n: Nat)(z: Eq(Bool, isZero(n), Bool.false)) : Eq(List(Nat), pick(n), List.nil(Nat)) :=
          |  rewrite z in Eq.refl(List.nil(Nat))
          |""".stripMargin
    )
  }

  // A stuck match is identified by its scrutinee's value, not its scrutinee's code, so the value occurs in the goal.
  test("a match's computed scrutinee is found in the goal, and abstracted as the match's scrutinee") {
    val src =
      coordinate +
        """
          |def low (n: Nat)(k: Nat)(h: Eq(Bool, Nat.ble(2147483648, n), Bool.false))
          |    : Eq(Option(Nat), coordinate(n, k), Option.some(Nat.add(n, k))) :=
          |  rewrite h in Eq.refl(Option.some(Nat.add(n, k)))
          |
          |def back (n: Nat)(k: Nat)(h: Eq(Bool, Bool.false, Nat.ble(2147483648, n)))
          |    : Eq(Option(Nat), coordinate(n, k), Option.some(Nat.add(n, k))) :=
          |  rewrite <- h in Eq.refl(Option.some(Nat.add(n, k)))
          |
          |def high (n: Nat)(k: Nat)(h: Eq(Bool, Nat.ble(2147483648, n), Bool.true))
          |    (far: Eq(Bool, Nat.ble(Nat.sub(4294967296, n), k), Bool.false))
          |    : Eq(Option(Nat), coordinate(n, k), Option.none(Nat)) :=
          |  rewrite [h, far] in Eq.refl(Option.none(Nat))
          |
          |// To a variable: the goal's match and the match restated on it, which the motive at `b` gives.
          |def restated (b: Bool)(n: Nat)(k: Nat): Option(Nat) := {
          |  match b returning Option(Nat) with
          |  | Bool.false => Option.some(Nat.add(n, k))
          |  | Bool.true => {
          |    let below := Nat.sub(4294967296, n)
          |    Bool.cond(Nat.ble(below, k), Option(Nat), Option.some(Nat.sub(k, below)), Option.none(Nat))
          |  }
          |}
          |
          |def any (n: Nat)(k: Nat)(b: Bool)(h: Eq(Bool, Nat.ble(2147483648, n), b))
          |    : Eq(Option(Nat), coordinate(n, k), restated(b, n, k)) :=
          |  rewrite h in Eq.refl(restated(b, n, k))
          |""".stripMargin
    run(src)
    val motive = residualOf(src, "low")
    assert(motive.contains("match _rewritten returning Option(Nat) with"), motive)
  }

  // A lambda is identified by its code, so the goal's predicate, written apart from the equation's, is the same value.
  test("a side holding a lambda is found where the goal writes the same lambda") {
    run(
      """
        |def filtered (xs: List(Nat))(ys: List(Nat))
        |    (h: Eq(List(Nat), List.filter(xs, fun (x: Nat): Bool => Nat.isZero(x)), ys))
        |    (q: Eq(Nat, List.length(ys), 0))
        |    : Eq(Nat, List.length(List.filter(xs, fun (y: Nat): Bool => Nat.isZero(y))), 0) :=
        |  rewrite h in q
        |""".stripMargin
    )
  }

  test("steps apply in order, each against the goal the earlier ones leave") {
    run(
      """
        |def chain (a: Nat)(b: Nat)(c: Nat)(e1: Eq(Nat, a, b))(e2: Eq(Nat, b, c))(p: Nat.le(c, 5)) : Nat.le(a, 5) :=
        |  rewrite [e1, e2] in p
        |
        |// docs/language.md's example: `<- e2` rewrites `b` to `c`.
        |def mixed (a: Nat)(b: Nat)(c: Nat)(e1: Eq(Nat, a, b))(e2: Eq(Nat, c, b))(p: Nat.le(c, 5)) : Nat.le(a, 5) :=
        |  rewrite [e1, <- e2] in p
        |
        |def back (a: Nat)(b: Nat)(c: Nat)(e1: Eq(Nat, a, b))(e2: Eq(Nat, b, c))(p: Nat.le(c, 5)) : Nat.le(a, 5) := {
        |  let q : Nat.le(a, 5) := rewrite [
        |    e1,
        |    e2, <- e2
        |  ] in rewrite e2 in p
        |  q
        |}
        |""".stripMargin
    )
  }

  test("a rewrite takes its goal from a let's annotation, a lambda's result, a match's case and an argument") {
    run(
      pick +
        """
          |def letted (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Nat.le(b, 3)) : Nat.le(a, 3) := {
          |  let q : Nat.le(a, 3) := rewrite e in p
          |  q
          |}
          |
          |def lambda (a: Nat)(b: Nat)(e: Eq(Nat, a, b)) : Nat.le(b, 3) -> Nat.le(a, 3) :=
          |  fun (p: Nat.le(b, 3)): Nat.le(a, 3) => rewrite e in p
          |
          |// In each case the goal is refined to `Nat.le(a, 3)`, where `a` occurs; unrefined, it is under a stuck `Bool.cond`.
          |def cased (b: Bool)(a: Nat)(c: Nat)(e: Eq(Nat, a, c))(p: Nat.le(c, 3)) : Nat.le(Bool.cond(b, Nat, a, a), 3) := {
          |  match b returning Nat.le(Bool.cond(b, Nat, a, a), 3) with
          |  | Bool.true => rewrite e in p
          |  | Bool.false => rewrite e in p
          |}
          |
          |// A constructor's parameter that captures from its argument's type expects nothing, so a let states the goal.
          |def constructed (n: Nat)(z: Eq(Bool, isZero(n), Bool.true)) : Or(List.Mem(Nat, n, pick(n)), False) := {
          |  let m : List.Mem(Nat, n, pick(n)) := rewrite z in List.Mem.head(n, List.nil(Nat))
          |  Or.inl(False, m)
          |}
          |
          |def small (n: Nat)(h: Nat.le(n, 3)) : Nat.le(n, 3) := h
          |
          |def argument (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Nat.le(b, 3)) : Nat.le(a, 3) := small(a, rewrite e in p)
          |""".stripMargin
    )
  }

  test("without a goal a rewrite asks for one") {
    val error = assertErrorAt[RewriteNeedsExpectedType](
      """
        |def unannotated (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Nat.le(b, 3)) : Nat.le(a, 3) := {
        |  let q := rewrite e in p
        |  q
        |}
        |""".stripMargin,
      "e",
      within = "e in p"
    )
    assert(error.getMessage.contains("`let x : T := rewrite h in e`"), error.getMessage)
    // A parameter whose type captures from its argument's type expects nothing before the argument is checked.
    val captured = assertErrorAt[RewriteNeedsExpectedType](
      """
        |def captured (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Eq(Nat, b, 3)) : Eq(Nat, a, 3) :=
        |  Eq.trans(rewrite e in p, Eq.refl(3))
        |""".stripMargin,
      "(rewrite e in p, Eq.refl(3))"
    )
    assert(captured.getMessage.contains("the parameter p it is passed to"), captured.getMessage)
  }

  test("a side the goal does not mention is refused, with the other direction suggested when it fits") {
    val error = assertErrorAt[RewriteFailed](
      "def wrong (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Nat.le(a, 3)) : Nat.le(b, 3) := rewrite e in p\n",
      "e",
      within = "e in p"
    )
    assert(error.getMessage.contains("has no occurrence of a#"), error.getMessage)
    assert(error.getMessage.contains("so the step may need a `<-`"), error.getMessage)
    val reversed = assertErrorAt[RewriteFailed](
      "def wrong (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Nat.le(b, 3)) : Nat.le(a, 3) := rewrite <- e in p\n",
      "<- e",
      within = "<- e in p"
    )
    assert(reversed.getMessage.contains("so the step may need no `<-`"), reversed.getMessage)
    val neither = assertErrorAt[RewriteFailed](
      "def wrong (a: Nat)(b: Nat)(c: Nat)(e: Eq(Nat, a, b))(p: Nat.le(c, 3)) : Nat.le(c, 3) := rewrite e in p\n",
      "e",
      within = "e in p"
    )
    assert(!neither.getMessage.contains("`<-`"), neither.getMessage)
  }

  test("an equation must be an Eq, and the goal a proposition") {
    val notEq = assertErrorAt[RewriteFailed](
      "def bad (a: Nat)(p: Or(Eq(Nat, a, 3), Eq(Nat, a, 4))) : Nat.le(a, 3) := rewrite p in p\n",
      "p",
      within = "p in p"
    )
    assert(notEq.getMessage.contains("which is no Eq(A, x, y)"), notEq.getMessage)
    val data = assertErrorAt[RewriteFailed](
      "def bad (a: Nat)(b: Nat)(e: Eq(Nat, a, b)) : Nat := rewrite e in a\n",
      "e",
      within = "e in a"
    )
    assert(data.getMessage.contains("is no proposition"), data.getMessage)
  }

  test("a motive left ill-typed by the abstraction fails its check, as the rewrite's failure") {
    // `x : Box(a)`, so `Eq(Box(_rewritten), x, x)` is ill-typed: abstracting `a` everywhere breaks the dependency.
    val error = assertErrorAt[RewriteFailed](
      """
        |inductive Box (n: Nat) : Type
        | | mk {n: Nat} : Box(n)
        |
        |def bad (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(x: Box(a))(p: Eq(Box(b), Box.mk(b), Box.mk(b))) : Eq(Box(a), x, x) :=
        |  rewrite e in p
        |""".stripMargin,
      "e",
      within = "e in p"
    )
    assert(error.getMessage.contains("is ill-typed"), error.getMessage)
  }

  test("a body that does not prove the goal at the other side is a mismatch at the body") {
    val error = assertErrorAt[TypeMismatch](
      "def bad (a: Nat)(b: Nat)(e: Eq(Nat, a, b))(p: Nat.le(a, 4)) : Nat.le(a, 3) := rewrite e in p\n",
      "p",
      within = "in p"
    )
    assert(error.getMessage.contains("Eq(Bool, Nat.ble(b#"), error.getMessage)
  }

  test("rewrite is no keyword") {
    assertEquals(
      result(
        """
          |def rewrite (n: Nat) : Nat := Nat.add(n, 1)
          |
          |def twice (rewrite: Bool) : Bool := {
          |  match rewrite returning Bool with
          |  | Bool.true => Bool.false
          |  | Bool.false => Bool.true
          |}
          |
          |Nat.add(rewrite(1), Bool.cond(twice(Bool.false), Nat, 10, 20))
          |""".stripMargin
      ),
      "12"
    )
  }
}
