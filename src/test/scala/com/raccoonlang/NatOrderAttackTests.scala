package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source
import com.raccoonlang.ProgramFixtures.{lnats, Programs}

/**
 * Nat metric components ordered by `<` (KERNEL_FOLLOWUPS 2.10, mut-14; docs/kernel.md, "Mutual blocks"), and its
 * adversarial review.
 *
 * CONTROL tests are terminating programs the kernel must accept, each refused before the order. Every other test is an
 * attack, a program the kernel must refuse because a call does not decrease; the comment of each one that runs forever
 * names the arguments it loops at, so its acceptance would be a break. OVER-REJECTION tests pin terminating programs
 * the order still refuses. No break was found.
 */
class NatOrderAttackTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)

  /** The program checks, and its evaluated checks hold. */
  private def accepts(src: String)(implicit loc: munit.Location): Unit = { programs.run(src); () }

  /** The program is refused because a call does not decrease; an acceptance is a break. Returns the refusal. */
  private def refuses(src: String)(implicit loc: munit.Location): NonDecreasingRecursiveCall =
    try {
      programs.runChecked(src)
      fail("ACCEPTED (BREAK: should be refused with NonDecreasingRecursiveCall)")
    } catch {
      case refusal: NonDecreasingRecursiveCall => refusal
      case t: TypeError =>
        fail(
          s"refused, but not as non-decreasing: ${t.getClass.getSimpleName}: " + ErrorReporter.pretty(t, Source(src))
        )
    }

  private val vec =
    """
      |inductive Vec (A: Type) indices (n: Nat) : Type
      | | nil {A: Type} : Vec(A, Nat.zero)
      | | cons {A: Type} (m: Nat)(tail: Vec(A, m)) (head: A) : Vec(A, Nat.succ(m))
      |""".stripMargin

  private val half =
    """
      |def half (n: Nat) : Nat decreases structural(n) := {
      |  match n returning Nat with
      |  | Nat.zero => 0
      |  | Nat.succ m => {
      |      match m returning Nat with
      |      | Nat.zero => 0
      |      | Nat.succ p => Nat.succ(half(p))
      |    }
      |}
      |""".stripMargin

  // ------------------------------------------------------------------------------------------------------------------
  // Controls: a Nat component decreases when the caller's value minus the candidate is at least 1.
  // ------------------------------------------------------------------------------------------------------------------

  test("lt-1 CONTROL a measure decreases by dropping a summand") {
    // b < k + 1 + b, but b is no structural subterm of it.
    accepts(
      """
        |def phases (a: Nat)(b: Nat) : Nat decreases measure(Nat.add(a, b)) := {
        |  match a returning Nat with
        |  | Nat.zero => {
        |      match b returning Nat with
        |      | Nat.zero => 0
        |      | Nat.succ c => phases(0, c)
        |    }
        |  | Nat.succ k => phases(0, b)
        |}
        |
        |def t : Eq(Nat, phases(3, 4), 0) := Eq.refl(0)
        |""".stripMargin
    )
  }

  test("lt-2 CONTROL a structural Nat parameter is ordered by <, so a smaller numeral decreases it") {
    accepts(
      """
        |def settle (n: Nat) : Nat decreases structural(n) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => {
        |      match k returning Nat with
        |      | Nat.zero => settle(0)
        |      | Nat.succ j => settle(1)
        |    }
        |}
        |
        |def t : Eq(Nat, settle(9), 0) := Eq.refl(0)
        |""".stripMargin
    )
  }

  test("lt-3 CONTROL the decrease shows only through the branch's refinement of an index") {
    // In the cons case `n` is `m + 1`, so the measure is `m + 1 + extra`, above `extra`.
    accepts(
      vec +
        """
          |def walk (n: Nat)(v: Vec(Nat, n))(extra: Nat) : Nat decreases measure(Nat.add(n, extra)) := {
          |  match v returning Nat with
          |  | Vec.nil => {
          |      match extra returning Nat with
          |      | Nat.zero => 0
          |      | Nat.succ e => walk(0, Vec.nil(Nat), e)
          |    }
          |  | Vec.cons m tail head => walk(0, Vec.nil(Nat), extra)
          |}
          |
          |def t : Eq(Nat, walk(1, Vec.cons(Nat, 0, Vec.nil(Nat), 7), 2), 0) := Eq.refl(0)
          |""".stripMargin
    )
    // Without the refinement, `n + extra` is above `extra` only when `n` is positive; it loops at n = 0.
    refuses(
      vec +
        """
          |def walk (n: Nat)(v: Vec(Nat, n))(extra: Nat) : Nat decreases measure(Nat.add(n, extra)) :=
          |  walk(0, Vec.nil(Nat), extra)
          |""".stripMargin
    )
  }

  test("lt-4 CONTROL lexicographically, a first component below by <, or at most by <=, then a later one below") {
    accepts(
      """
        |def f (a: Nat)(b: Nat) : Nat decreases lexicographic(a, b) := {
        |  match a returning Nat with
        |  | Nat.zero => {
        |      match b returning Nat with
        |      | Nat.zero => 0
        |      | Nat.succ j => f(0, j)
        |    }
        |  | Nat.succ k => f(0, Nat.add(b, 5))
        |}
        |
        |def t : Eq(Nat, f(2, 1), 0) := Eq.refl(0)
        |""".stripMargin
    )
    // 1 <= k + 1 is no equality, and j < j + 1.
    accepts(
      """
        |def f (a: Nat)(b: Nat) : Nat decreases lexicographic(a, b) := {
        |  match a returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => {
        |      match b returning Nat with
        |      | Nat.zero => f(k, 7)
        |      | Nat.succ j => f(1, j)
        |    }
        |}
        |
        |def t : Eq(Nat, f(4, 3), 0) := Eq.refl(0)
        |""".stripMargin
    )
  }

  test("lt-5 CONTROL a measure through a linear value, whose rest is dropped") {
    accepts(
      lnats +
        """
          |def drain (xs: LNats)(n: Nat) : Nat decreases measure(Nat.add(count(xs), n)) := {
          |  match xs returning Nat with
          |  | LNats.nil => {
          |      match n returning Nat with
          |      | Nat.zero => 0
          |      | Nat.succ m => drain(LNats.nil, m)
          |    }
          |  | LNats.cons h _ => drain(LNats.nil, n)
          |}
          |
          |def t : Eq(Nat, drain(LNats.cons(4, LNats.cons(5, LNats.nil)), 3), 0) := Eq.refl(0)
          |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Equal, or smaller only for some values of the variables.
  // ------------------------------------------------------------------------------------------------------------------

  test("lt-6 an equal measure: commuted, rebuilt by arithmetic, or rebuilt from the refinement") {
    // Each loops at every argument it reaches.
    refuses("def f (a: Nat)(b: Nat) : Nat decreases measure(Nat.add(a, b)) := f(b, a)\n")
    refuses("def f (n: Nat) : Nat decreases measure(n) := f(Nat.sub(Nat.add(n, 3), 3))\n")
    refuses(
      """
        |def f (n: Nat) : Nat decreases measure(Nat.mul(2, n)) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(Nat.add(k, 1))
        |}
        |""".stripMargin
    )
  }

  test("lt-7 a candidate smaller only when some variable is positive") {
    // The difference is b; loops at (1, 0).
    refuses(
      """
        |def f (a: Nat)(b: Nat) : Nat decreases measure(Nat.add(a, b)) := {
        |  match a returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(Nat.succ(k), 0)
        |}
        |""".stripMargin
    )
    // The difference is k; loops at 1.
    refuses(
      """
        |def f (n: Nat) : Nat decreases measure(n) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(1)
        |}
        |""".stripMargin
    )
    // The difference is m * m; loops at (n, 0).
    refuses("def f (n: Nat)(m: Nat) : Nat decreases measure(Nat.add(n, Nat.mul(m, m))) := f(n, 0)\n")
    // (k + 1) * b against (k + 1) * (b - 1): a product does not distribute; loops at (1, 0).
    refuses(
      """
        |def f (a: Nat)(b: Nat) : Nat decreases measure(Nat.mul(a, b)) := {
        |  match a returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(a, Nat.pred(b))
        |}
        |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Opaque operations and stuck calls: atoms compare only with atoms they convert with.
  // ------------------------------------------------------------------------------------------------------------------

  test("lt-8 truncated subtraction and predecessor") {
    // Counting up with no guard; loops at every argument.
    refuses("def up (i: Nat)(n: Nat) : Nat decreases measure(Nat.sub(n, i)) := up(Nat.succ(i), n)\n")
    // pred(0) = 0; each loops at 0.
    refuses("def f (n: Nat) : Nat decreases measure(n) := f(Nat.pred(n))\n")
    refuses("def f (n: Nat) : Nat decreases measure(Nat.succ(Nat.pred(n))) := f(Nat.pred(n))\n")
    // sub(k + 6, 4) = k + 2, above k + 1; loops at every positive argument.
    refuses(
      """
        |def f (n: Nat) : Nat decreases measure(n) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(Nat.sub(Nat.add(n, 5), 4))
        |}
        |""".stripMargin
    )
    // The difference sub(m, n) - 1 - sub(m, n + 1) holds no atom in common; loops at every argument.
    refuses("def f (n: Nat)(m: Nat) : Nat decreases measure(Nat.add(n, Nat.sub(m, n))) := f(Nat.succ(n), m)\n")
  }

  test("lt-9 measures over a defined division, a function parameter, and a power") {
    // half(n + 1) is stuck, an atom unrelated to half(n); loops at every argument.
    refuses(half + "def f (n: Nat) : Nat decreases measure(half(n)) := f(Nat.add(n, 1))\n")
    // half(p + 2) = half(p) + 1 against half(p + 3) = half(p + 1) + 1; loops at every argument from 2.
    refuses(
      half +
        """
          |def f (n: Nat) : Nat decreases measure(half(n)) := {
          |  match n returning Nat with
          |  | Nat.zero => 0
          |  | Nat.succ m => {
          |      match m returning Nat with
          |      | Nat.zero => 0
          |      | Nat.succ p => f(Nat.add(p, 3))
          |    }
          |}
          |""".stripMargin
    )
    // Loops whenever g is constant.
    refuses("def f (g: Nat -> Nat)(n: Nat) : Nat decreases measure(g(n)) := f(g, Nat.succ(n))\n")
    // 2^(n + 1) = 2 * 2^n is above 2^n; loops at every argument.
    refuses("def f (n: Nat) : Nat decreases measure(Nat.pow(2, n)) := f(Nat.add(n, 1))\n")
  }

  test("lt-10 a candidate through a stuck call of the function itself, or a stuck conditional") {
    // f(0) = 0, so f(1) calls f(0 + 1); loops at 1.
    refuses(
      """
        |def f (n: Nat) : Nat decreases measure(n) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(Nat.add(f(k), n))
        |}
        |""".stripMargin
    )
    // Loops at (false, n).
    refuses(
      """
        |def f (b: Bool)(n: Nat) : Nat decreases measure(n) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(b, Bool.cond(b, Nat, k, Nat.succ(n)))
        |}
        |""".stripMargin
    )
  }

  test("lt-11 a candidate through variables the caller does not control") {
    // A lambda's own parameter; f(1)(1) calls f(0 + 1)(1).
    refuses(
      """
        |def f (n: Nat) : (m: Nat) -> Nat decreases measure(n) := {
        |  match n returning (m: Nat) -> Nat with
        |  | Nat.zero => fun (m: Nat): Nat => 0
        |  | Nat.succ k => fun (m: Nat): Nat => f(Nat.add(k, m))(m)
        |}
        |""".stripMargin
    )
    // Another parameter; loops at (1, 1).
    refuses(
      """
        |def f (n: Nat)(m: Nat) : Nat decreases measure(n) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(Nat.add(k, m), m)
        |}
        |""".stripMargin
    )
    // A field of another argument, which is passed on unchanged; loops at (1, [1]).
    refuses(
      """
        |def f (n: Nat)(xs: List(Nat)) : Nat decreases measure(n) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => {
        |      match xs returning Nat with
        |      | List.nil => 0
        |      | List.cons x rest => f(Nat.add(k, x), xs)
        |    }
        |}
        |""".stripMargin
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // Mutual blocks, and components of other types.
  // ------------------------------------------------------------------------------------------------------------------

  test("lt-12 a measure that decreases in one member and increases in another") {
    // f(1), g(0), f(2), g(1), f(3), ...
    val growing = refuses(
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases measure(n) := {
        |    match n returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => g(k)
        |  }
        |
        |  def g (m: Nat) : Nat decreases measure(m) := f(Nat.add(m, 2))
        |}
        |""".stripMargin
    )
    assertEquals(growing.function, "f")
    // f drops the summand b by <, and g adds back the successor f lost; loops at f(1, 0).
    val restored = refuses(
      """
        |mutual {
        |  def f (a: Nat)(b: Nat) : Nat decreases measure(Nat.add(a, b)) := {
        |    match a returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => g(k, b)
        |  }
        |
        |  def g (x: Nat)(y: Nat) : Nat decreases measure(y) := f(Nat.succ(x), y)
        |}
        |""".stripMargin
    )
    assertEquals(restored.function, "f")
  }

  test("lt-13 a constructor of another type is not below a Nat, though the normal forms read any constructor as zero") {
    // f(1), g(Box.mk(1)), f(1), ...
    val box = refuses(
      """
        |inductive Box : Type
        | | mk (n: Nat) : Box
        |
        |mutual {
        |  def f (n: Nat) : Nat decreases structural(n) := {
        |    match n returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => g(Box.mk(n))
        |  }
        |
        |  def g (b: Box) : Nat decreases structural(b) := {
        |    match b returning Nat with
        |    | Box.mk m => f(m)
        |  }
        |}
        |""".stripMargin
    )
    assertEquals(box.function, "g")
    // f(0), g(Bool.true), f(0), ...
    refuses(
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases measure(Nat.succ(n)) := g(Bool.true)
        |
        |  def g (b: Bool) : Nat decreases structural(b) := f(0)
        |}
        |""".stripMargin
    )
    // Nor is a Nat at most a constructor of another type: a root that is not a Nat keeps its order.
    val boolRoot = refuses(
      """
        |mutual {
        |  def f (n: Nat)(c: Nat) : Nat decreases lexicographic(n, c) := 0
        |
        |  def g (b: Bool)(c: Nat) : Nat decreases lexicographic(b, c) := {
        |    match b returning Nat with
        |    | Bool.false => 0
        |    | Bool.true => {
        |        match c returning Nat with
        |        | Nat.zero => 0
        |        | Nat.succ j => f(0, j)
        |      }
        |  }
        |}
        |""".stripMargin
    )
    assertEquals(boolRoot.function, "f")
  }

  test("lt-14 lexicographic components where <= and < interact") {
    // The first is at most, the second grows; loops at (1, 1), (1, 5), (1, 9), ...
    refuses(
      """
        |def f (a: Nat)(b: Nat) : Nat decreases lexicographic(a, b) := {
        |  match a returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => {
        |      match b returning Nat with
        |      | Nat.zero => 0
        |      | Nat.succ j => f(1, Nat.add(j, 5))
        |    }
        |}
        |""".stripMargin
    )
    // Both at most, neither below; loops at (1, 1).
    refuses(
      """
        |def f (a: Nat)(b: Nat) : Nat decreases lexicographic(a, b) := {
        |  match a returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(1, b)
        |}
        |""".stripMargin
    )
    // The first is above unless b is zero, and the second unchanged; loops at (1, 1).
    refuses(
      """
        |def f (a: Nat)(b: Nat) : Nat decreases lexicographic(a, b) := {
        |  match a returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(Nat.add(k, b), b)
        |}
        |""".stripMargin
    )
    // Across a block: f's call to g is at most in both components; loops at f(1, b), g(1, b), ...
    val block = refuses(
      """
        |mutual {
        |  def f (a: Nat)(b: Nat) : Nat decreases lexicographic(a, b) := {
        |    match a returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => g(1, b)
        |  }
        |
        |  def g (x: Nat)(y: Nat) : Nat decreases lexicographic(x, y) := f(x, y)
        |}
        |""".stripMargin
    )
    assertEquals(block.function, "g")
  }

  test("lt-15 through a linear value rebuilt or a proof's data") {
    // A list rebuilt from its fields measures the same; loops at every cons.
    refuses(
      lnats +
        """
          |def f (xs: LNats) : Nat decreases measure(count(xs)) := {
          |  match xs returning Nat with
          |  | LNats.nil => 0
          |  | LNats.cons h t => f(LNats.cons(h, t))
          |}
          |""".stripMargin
    )
    // Dropping the rest of the list while the other summand gains one, and back; loops at ([h], 0), ([], 1), ([0], 0).
    refuses(
      lnats +
        """
          |def drain (xs: LNats)(n: Nat) : Nat decreases measure(Nat.add(count(xs), n)) := {
          |  match xs returning Nat with
          |  | LNats.nil => {
          |      match n returning Nat with
          |      | Nat.zero => 0
          |      | Nat.succ m => drain(LNats.cons(0, LNats.nil), m)
          |    }
          |  | LNats.cons h _ => drain(LNats.nil, Nat.succ(n))
          |}
          |""".stripMargin
    )
    // A measure cannot read a proof's data at all, so no proof value carries one.
    intercept[PropEliminationRestricted](
      programs.runChecked(
        """
          |inductive Wit : Prop
          | | mk (n: Nat) : Wit
          |
          |def size (w: Wit) : Nat := {
          |  match w returning Nat with
          |  | Wit.mk n => n
          |}
          |
          |def f (w: Wit) : Nat decreases measure(size(w)) := f(Wit.mk(0))
          |""".stripMargin
      )
    )
  }

  // ------------------------------------------------------------------------------------------------------------------
  // What the order does not decide.
  // ------------------------------------------------------------------------------------------------------------------

  test("lt-16 OVER-REJECTION a term is not known positive, and a guard is not read") {
    // Both are for decision (KERNEL_FOLLOWUPS 2.10, lt-16).
    // 2^k is at least 1, but only the difference's constant counts, as for Nat.ble(1, 2^k), which is stuck.
    refuses(
      """
        |def f (n: Nat) : Nat decreases measure(Nat.pow(2, n)) := {
        |  match n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => f(k)
        |}
        |""".stripMargin
    )
    // i < n in the call's branch, but the measure's atoms sub(n, i) and sub(n, i + 1) are unrelated.
    refuses(
      """
        |def up (i: Nat)(n: Nat) : Nat decreases measure(Nat.sub(n, i)) := {
        |  match Nat.ble(n, i) returning Nat with
        |  | Bool.true => 0
        |  | Bool.false => up(Nat.succ(i), n)
        |}
        |""".stripMargin
    )
  }
}
