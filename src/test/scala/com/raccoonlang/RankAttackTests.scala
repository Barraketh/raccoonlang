package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.{lnats, Programs}

/**
 * Measure components of a `lexicographic` metric, constant ranks among them (KERNEL_FOLLOWUPS 2.10, mut-14;
 * docs/kernel.md, "Mutual blocks"), and their adversarial review.
 *
 * CONTROL tests are terminating programs the kernel must accept, each one evaluated. Every other test is an attack, a
 * program the kernel must refuse; the comment of each one that runs forever names the arguments it loops at, so its
 * acceptance would be a break. No break was found.
 */
class RankAttackTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)

  private def report(t: TypeError, src: String): String =
    s"${t.getClass.getSimpleName}: " + ErrorReporter.pretty(t, Source(src))

  /** The program checks, and its evaluated checks hold. */
  private def accepts(src: String)(implicit loc: munit.Location): Unit = { programs.run(src); () }

  /** The program is refused with `T`; an acceptance is a break, any other refusal a misdiagnosis. */
  private def refusesWith[T <: TypeError](src: String)(implicit loc: munit.Location, ct: reflect.ClassTag[T]): T =
    try {
      programs.runChecked(src)
      fail(s"ACCEPTED (BREAK: should be refused with ${ct.runtimeClass.getSimpleName})")
    } catch {
      case refusal: T   => refusal
      case t: TypeError => fail(s"refused, but not with ${ct.runtimeClass.getSimpleName}: " + report(t, src))
    }

  /** The program is refused because a call does not decrease. Returns the refusal, which names the callee. */
  private def refuses(src: String)(implicit loc: munit.Location): NonDecreasingRecursiveCall =
    refusesWith[NonDecreasingRecursiveCall](src)

  private val peano =
    """
      |inductive P indices (n: Nat) : Prop
      | | z : P(0)
      | | s (n: Nat)(h: P(n)) : P(Nat.succ(n))
      |""".stripMargin

  // ------------------------------------------------------------------------------------------------------------------
  // Controls.
  // ------------------------------------------------------------------------------------------------------------------

  test("rank-1 CONTROL mut-14's proof block, with a rank after the proof") {
    // f to g: h2 is a proof field of h. g to f: h is unchanged, and the rank goes from 1 to 0.
    val block =
      peano +
        """
          |mutual {
          |  def f (n: Nat)(h: P(n)) : True decreases lexicographic(h, measure(0)) := {
          |    match h returning True with
          |    | P.z => True.intro
          |    | P.s m h2 => g(m, h2)
          |  }
          |
          |  def g (n: Nat)(h: P(n)) : True decreases lexicographic(h, measure(1)) := f(n, h)
          |}
          |""".stripMargin
    assertEquals(programs.result(block + "f(2, P.s(1, P.s(0, P.z)))\n"), "True.intro")
    // The same cycle rebuilding the proof, so that its value shows the run went through every call.
    assertEquals(
      programs.result(
        peano +
          """
            |mutual {
            |  def f (n: Nat)(h: P(n)) : P(n) decreases lexicographic(h, measure(0)) := {
            |    match h returning P(n) with
            |    | P.z => P.z
            |    | P.s m h2 => P.s(m, g(m, h2))
            |  }
            |
            |  def g (n: Nat)(h: P(n)) : P(n) decreases lexicographic(h, measure(1)) := f(n, h)
            |}
            |
            |f(2, P.s(1, P.s(0, P.z)))
            |""".stripMargin
      ),
      "P.s(1, P.s(0, P.z))"
    )
  }

  test("rank-2 CONTROL mut-14's measure block, with ranks after the measure") {
    // f to g: k + b < k + 1 + b. g to f: y + x converts with x + y, and the rank goes from 1 to 0. f counts its calls.
    accepts(
      """
        |mutual {
        |  def f (a: Nat)(b: Nat) : Nat decreases lexicographic(measure(Nat.add(a, b)), measure(0)) := {
        |    match a returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => Nat.succ(g(k, b))
        |  }
        |
        |  def g (x: Nat)(y: Nat) : Nat decreases lexicographic(measure(Nat.add(x, y)), measure(1)) := f(y, x)
        |}
        |
        |def t : Eq(Nat, f(3, 2), 5) := Eq.refl(5)
        |""".stripMargin
    )
  }

  test("rank-3 CONTROL a single definition with a rank that is a measure of a parameter") {
    // A fresh call keeps n and drops the rank from 1 to 0; a stale one decreases n.
    accepts(
      """
        |def tick (n: Nat)(fresh: Bool) : Nat decreases lexicographic(n, measure(Bool.cond(fresh, Nat, 1, 0))) := {
        |  match fresh returning Nat with
        |  | Bool.true => Nat.succ(tick(n, Bool.false))
        |  | Bool.false => {
        |      match n returning Nat with
        |      | Nat.zero => 0
        |      | Nat.succ k => tick(k, Bool.true)
        |    }
        |}
        |
        |def t : Eq(Nat, tick(3, Bool.true), 4) := Eq.refl(4)
        |""".stripMargin
    )
  }

  test("rank-4 CONTROL a block whose ranks are a constant and a measure") {
    // f to g decreases n. g keeps n: to itself, its rank goes from j + 2 to j + 1; to f, from 1 to 0.
    accepts(
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases lexicographic(n, measure(0)) := {
        |    match n returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ m => g(m, 2)
        |  }
        |
        |  def g (n: Nat)(extra: Nat) : Nat decreases lexicographic(n, measure(Nat.succ(extra))) := {
        |    match extra returning Nat with
        |    | Nat.zero => f(n)
        |    | Nat.succ j => Nat.succ(g(n, j))
        |  }
        |}
        |
        |def t : Eq(Nat, f(3), 6) := Eq.refl(6)
        |""".stripMargin
    )
  }

  test("rank-5 CONTROL a rank that reads a linear argument is no use of it (L6)") {
    // count consumes its argument, but in a measure it only reads it, so the body may still consume xs.
    accepts(
      lnats +
        """
          |mutual {
          |  def f (xs: LNats) : Nat decreases lexicographic(measure(count(xs)), measure(0)) := {
          |    match xs returning Nat with
          |    | LNats.nil => 0
          |    | LNats.cons h t => g(t)
          |  }
          |
          |  def g (xs: LNats) : Nat decreases lexicographic(measure(count(xs)), measure(1)) := Nat.succ(f(xs))
          |}
          |
          |def t : Eq(Nat, f(LNats.cons(4, LNats.cons(5, LNats.nil))), 2) := Eq.refl(2)
          |""".stripMargin
    )
  }

  test("rank-6 CONTROL a parameter whose name starts with measure is a parameter component") {
    accepts(
      """
        |def f (measured: Nat)(b: Nat) : Nat decreases lexicographic(measured, measure(b)) := {
        |  match measured returning Nat with
        |  | Nat.zero => b
        |  | Nat.succ k => f(k, Nat.add(b, 1))
        |}
        |
        |def t : Eq(Nat, f(2, 0), 2) := Eq.refl(2)
        |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Ranks that do not descend around a cycle.
  // ------------------------------------------------------------------------------------------------------------------

  test("rank-7 equal ranks around a cycle") {
    // f(n, h), g(n, h), f(n, h), ...
    val proof = refuses(
      peano +
        """
          |mutual {
          |  def f (n: Nat)(h: P(n)) : True decreases lexicographic(h, measure(0)) := g(n, h)
          |
          |  def g (n: Nat)(h: P(n)) : True decreases lexicographic(h, measure(0)) := f(n, h)
          |}
          |""".stripMargin
    )
    assertEquals(proof.function, "g")
    // f(n), g(n), f(n), ...
    val data = refuses(
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases lexicographic(n, measure(1)) := g(n)
        |
        |  def g (n: Nat) : Nat decreases lexicographic(n, measure(1)) := f(n)
        |}
        |""".stripMargin
    )
    assertEquals(data.function, "g")
  }

  test("rank-8 a rank that grows") {
    // Constant ranks cannot fall both ways: f's call to g falls from 1 to 0, so g's call back rises. f(n), g(n), ...
    val constant = refuses(
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases lexicographic(n, measure(1)) := g(n)
        |
        |  def g (n: Nat) : Nat decreases lexicographic(n, measure(0)) := f(n)
        |}
        |""".stripMargin
    )
    assertEquals(constant.function, "f")
    // A measure rank of the call's arguments, larger than the caller's; loops at every argument.
    refuses("def f (n: Nat)(k: Nat) : Nat decreases lexicographic(n, measure(k)) := f(n, Nat.succ(k))\n")
    // g's rank is f's minus one at the same arguments, so g's call back rises; f(n, k), g(n, k), ...
    val measured = refuses(
      """
        |mutual {
        |  def f (n: Nat)(k: Nat) : Nat decreases lexicographic(n, measure(Nat.succ(k))) := g(n, k)
        |
        |  def g (n: Nat)(k: Nat) : Nat decreases lexicographic(n, measure(k)) := f(n, k)
        |}
        |""".stripMargin
    )
    assertEquals(measured.function, "f")
    // The rank is read at the call's arguments: g's rank k is below f's k + 1 at f's own, but the call passes k + 2,
    // and g passes back k; f(n, k), g(n, k + 2), f(n, k), ...
    val atCall = refuses(
      """
        |mutual {
        |  def f (n: Nat)(k: Nat) : Nat decreases lexicographic(n, measure(Nat.succ(k))) := g(n, Nat.add(k, 2))
        |
        |  def g (n: Nat)(k: Nat) : Nat decreases lexicographic(n, measure(k)) := {
        |    match k returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ i => {
        |        match i returning Nat with
        |        | Nat.zero => 0
        |        | Nat.succ j => f(n, j)
        |      }
        |  }
        |}
        |""".stripMargin
    )
    assertEquals(atCall.function, "g")
  }

  test("rank-9 a rank that reads an argument the cycle rebuilds") {
    // g rebuilds the list f passed it, so its count is unchanged and the rank rises; f([h]), g([h]), f([h]), ...
    val rebuilt = refuses(
      lnats +
        """
          |mutual {
          |  def f (xs: LNats) : Nat decreases lexicographic(measure(count(xs)), measure(1)) := g(xs)
          |
          |  def g (xs: LNats) : Nat decreases lexicographic(measure(count(xs)), measure(0)) := {
          |    match xs returning Nat with
          |    | LNats.nil => 0
          |    | LNats.cons h t => f(LNats.cons(h, t))
          |  }
          |}
          |""".stripMargin
    )
    assertEquals(rebuilt.function, "f")
    // The call swaps the summands, so the measure is unchanged and the rank reads the other one; f(2, 1), f(1, 2), ...
    refuses(
      """
        |def f (a: Nat)(b: Nat) : Nat decreases lexicographic(measure(Nat.add(a, b)), measure(b)) := {
        |  match a returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(b, Nat.succ(k))
        |}
        |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Metrics that are not allowed.
  // ------------------------------------------------------------------------------------------------------------------

  test("rank-10 a rank over a proof is refused, whatever the function returns") {
    // Each loops at every argument.
    Vector("True", "Nat").foreach { result =>
      val refusal = refusesWith[InvalidDecreaseSpec](
        peano + s"def f (n: Nat)(h: P(n)) : $result decreases lexicographic(n, measure(h)) := f(n, h)\n"
      )
      assert(refusal.reason.contains("decrease measures must live in Type"), refusal.reason)
    }
    // A proof built in the rank; loops at every argument.
    val built = refusesWith[InvalidDecreaseSpec](
      peano + "def f (n: Nat)(h: P(n)) : True decreases lexicographic(n, measure(P.s(n, h))) := f(n, h)\n"
    )
    assert(built.reason.contains("decrease measures must live in Type"), built.reason)
  }

  test("rank-11 a proof component with ranks in a function whose result is not a proposition") {
    val refusal = refusesWith[InvalidDecreaseSpec](
      peano +
        """
          |mutual {
          |  def f (n: Nat)(h: P(n)) : Nat decreases lexicographic(h, measure(0)) := {
          |    match h returning Nat with
          |    | P.z => 0
          |    | P.s m h2 => g(m, h2)
          |  }
          |
          |  def g (n: Nat)(h: P(n)) : Nat decreases lexicographic(h, measure(1)) := f(n, h)
          |}
          |""".stripMargin
    )
    assert(refusal.reason.contains("only for functions returning a proposition"), refusal.reason)
  }

  test("rank-12 members whose metrics have different lengths") {
    programs.assertErrorAt[InvalidDecreaseSpec](
      peano +
        """
          |mutual {
          |  def f (n: Nat)(h: P(n)) : True decreases lexicographic(h, measure(0)) := {
          |    match h returning True with
          |    | P.z => True.intro
          |    | P.s m h2 => g(m, h2)
          |  }
          |
          |  def g (n: Nat)(h: P(n)) : True decreases structural(h) := f(n, h)
          |}
          |""".stripMargin,
      "structural(h)"
    )
    programs.assertErrorAt[InvalidDecreaseSpec](
      """
        |mutual {
        |  def f (a: Nat)(b: Nat) : Nat decreases measure(Nat.add(a, b)) := {
        |    match a returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => g(k, b)
        |  }
        |
        |  def g (x: Nat)(y: Nat) : Nat decreases lexicographic(measure(Nat.add(x, y)), measure(1)) := f(y, x)
        |}
        |""".stripMargin,
      "lexicographic(measure(Nat.add(x, y)), measure(1))"
    )
  }

  test("rank-13 a rank's read keeps each call's linear inputs separate (L6, S1)") {
    // The rank is a read extent of its own, so it may read xs, but not pass it twice to one call.
    programs.assertErrorAt[LinearReusedInType](
      lnats +
        """
          |def both (xs: LNats)(ys: LNats) : Nat := Nat.add(count(xs), count(ys))
          |
          |def f (n: Nat)(xs: LNats) : Nat decreases lexicographic(n, measure(both(xs, xs))) := count(xs)
          |""".stripMargin,
      "xs",
      "xs))) :="
    )
  }

  test("rank-14 a rank that is not inductive, or names the function itself") {
    val sort = refusesWith[InvalidDecreaseSpec]("def f (n: Nat) : Nat decreases lexicographic(n, measure(Nat)) := 0\n")
    assert(sort.reason.contains("must have an inductive type"), sort.reason)
    refusesWith[InvalidDecreaseSpec](
      "def f (g: Nat -> Nat)(n: Nat) : Nat decreases lexicographic(n, measure(g)) := 0\n"
    )
    // The function is not bound in its own metric; loops at every argument.
    refusesWith[NotFound]("def f (n: Nat) : Nat decreases lexicographic(measure(f(n)), n) := f(n)\n")
  }

  test("rank-15 a parameter named twice among ranks") {
    refusesWith[InvalidDecreaseSpec]("def f (n: Nat) : Nat decreases lexicographic(n, measure(0), n) := 0\n")
  }
}
