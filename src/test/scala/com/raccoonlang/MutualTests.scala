package com.raccoonlang

import com.raccoonlang.ProgramFixtures._

/**
 * Mutual blocks (docs/kernel.md, "Mutual blocks"; KERNEL_FOLLOWUPS 2.5): inductive families whose constructors name
 * each other, and recursive definitions that call each other, each checked and published as one block.
 */
class MutualTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs._

  private val evenOdd =
    """
      |mutual {
      |  inductive Even : Type
      |   | zero : Even
      |   | succ (odd: Odd) : Even
      |
      |  inductive Odd : Type
      |   | succ (even: Even) : Odd
      |}
      |
      |mutual {
      |  def evenToNat (e: Even) : Nat decreases structural(e) := {
      |    match e returning Nat with
      |    | Even.zero => 0
      |    | Even.succ o => Nat.succ(oddToNat(o))
      |  }
      |
      |  def oddToNat (o: Odd) : Nat decreases structural(o) := {
      |    match o returning Nat with
      |    | Odd.succ e => Nat.succ(evenToNat(e))
      |  }
      |}
      |""".stripMargin

  // README, "Syntax and layout": a block's members are separated as commands are, so no blank line is needed.
  test("a mutual block's members need no blank line between them, and may have comment lines between them") {
    assertEquals(
      result(
        """
          |mutual {
          |  // a comment right after the brace
          |  inductive Even : Type
          |   | zero : Even
          |   | succ (odd: Odd) : Even
          |  inductive Odd : Type
          |   | succ (even: Even) : Odd
          |}
          |mutual {
          |  def evenToNat (e: Even) : Nat decreases structural(e) := {
          |    match e returning Nat with
          |    | Even.zero => 0
          |    | Even.succ o => Nat.succ(oddToNat(o))
          |  }
          |  // a comment between members
          |  def oddToNat (o: Odd) : Nat
          |      decreases structural(o) := {
          |    match o returning Nat with
          |    | Odd.succ e => Nat.succ(evenToNat(e))
          |  }
          |}
          |evenToNat(Even.succ(Odd.succ(Even.zero)))
          |""".stripMargin
      ),
      "2"
    )
  }

  test("a mutual block's member has no dotted name") {
    val parsed = LanguageParser.parseProgram("mutual {\n  inductive A.T : Type\n   | leaf : T\n}\n")
    parsed match {
      case Failure(_, _, message) =>
        assertEquals(message, "A mutual block's member has no dotted name; put the block in a namespace block")
      case Success(_, _, _) => fail("the program parses")
    }
  }

  test("a mutual pair of copyable families, with mutually recursive functions over them") {
    assertEquals(result(evenOdd + "\nevenToNat(Even.succ(Odd.succ(Even.succ(Odd.succ(Even.zero)))))\n"), "4")
    run(evenOdd + "\ndef two : Eq(Nat, oddToNat(Odd.succ(Even.succ(Odd.succ(Even.zero)))), 3) := Eq.refl(3)\n")
    // A family's constructors are its own: a sibling's constructor is no case of its match.
    assertErrorAt[UnknownConstructor](
      evenOdd + "\ndef bad (e: Even) : Nat := {\n  match e returning Nat with\n  | Odd.succ x => 0\n}\n",
      "| Odd.succ x => 0"
    )
  }

  private val parity =
    """
      |mutual {
      |  def isEven (n: Nat) : Bool decreases structural(n) := {
      |    match n returning Bool with
      |    | Nat.zero => Bool.true
      |    | Nat.succ k => isOdd(k)
      |  }
      |
      |  def isOdd (n: Nat) : Bool decreases structural(n) := {
      |    match n returning Bool with
      |    | Nat.zero => Bool.false
      |    | Nat.succ k => isEven(k)
      |  }
      |}
      |""".stripMargin

  test("mutually recursive definitions are published together, after the block") {
    assertEquals(result(parity + "\nProd.mk(Bool, Bool, isEven(10), isOdd(7))\n"), "Prod.mk(Bool.true, Bool.true)")
    run(parity + "\ndef ten : Eq(Bool, isEven(10), Bool.true) := Eq.refl(Bool.true)\n")
    // Inside a namespace, a member is called by its short or its qualified name.
    run(
      """
        |namespace P {
        |  mutual {
        |    def even (n: Nat) : Bool decreases structural(n) := {
        |      match n returning Bool with
        |      | Nat.zero => Bool.true
        |      | Nat.succ k => P.odd(k)
        |    }
        |
        |    def odd (n: Nat) : Bool decreases structural(n) := {
        |      match n returning Bool with
        |      | Nat.zero => Bool.false
        |      | Nat.succ k => even(k)
        |    }
        |  }
        |}
        |
        |def four : Eq(Bool, P.even(4), Bool.true) := Eq.refl(Bool.true)
        |""".stripMargin
    )
  }

  test("every call between members decreases from the caller's own metric") {
    assertErrorAt[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases structural(n) := g(n)
        |
        |  def g (n: Nat) : Nat decreases structural(n) := 0
        |}
        |""".stripMargin,
      "(n)",
      "g(n)"
    )
    assertErrorAt[NonDecreasingRecursiveCall](
      """
        |mutual {
        |  def f (n: Nat) : Nat decreases structural(n) := {
        |    match n returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => g(Nat.succ(Nat.succ(k)))
        |  }
        |
        |  def g (n: Nat) : Nat decreases structural(n) := f(n)
        |}
        |""".stripMargin,
      "(Nat.succ(Nat.succ(k)))"
    )
    // Lexicographic metrics compare component by component, across members.
    run(
      """
        |mutual {
        |  def f (a: Nat)(b: Nat) : Nat decreases lexicographic(a, b) := {
        |    match b returning Nat with
        |    | Nat.zero => {
        |      match a returning Nat with
        |      | Nat.zero => 0
        |      | Nat.succ a1 => g(a1, 5)
        |    }
        |    | Nat.succ b1 => g(a, b1)
        |  }
        |
        |  def g (x: Nat)(y: Nat) : Nat decreases lexicographic(x, y) := {
        |    match y returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ y1 => f(x, y1)
        |  }
        |}
        |""".stripMargin
    )
    // A measure is one component, so it shares a block with structural metrics.
    run(
      """
        |mutual {
        |  def down (n: Nat) : Nat decreases measure(n) := {
        |    match n returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ k => across(k)
        |  }
        |
        |  def across (m: Nat) : Nat decreases structural(m) := {
        |    match m returning Nat with
        |    | Nat.zero => 0
        |    | Nat.succ j => down(j)
        |  }
        |}
        |""".stripMargin
    )
    assertErrorAt[InvalidDecreaseSpec](
      """
        |mutual {
        |  def f (a: Nat)(b: Nat) : Nat decreases lexicographic(a, b) := 0
        |
        |  def g (n: Nat) : Nat decreases structural(n) := 0
        |}
        |""".stripMargin,
      "structural(n)"
    )
  }

  test("a member is no value inside the block, and the block holds only definitions or only families") {
    intercept[CannotQuoteValue](
      runChecked(
        """
          |mutual {
          |  def f (n: Nat) : (m: Nat) -> Nat decreases structural(n) := g
          |
          |  def g (n: Nat) : Nat decreases structural(n) := 0
          |}
          |""".stripMargin
      )
    )
    intercept[InvalidMutualBlock](
      runChecked(
        "mutual {\n  inductive A : Type\n   | mk : A\n\n  def f (n: Nat) : Nat decreases structural(n) := 0\n}\n"
      )
    )
    intercept[InvalidMutualBlock](runChecked("mutual {\n  def f (n: Nat) : Nat := 0\n}\n"))
    intercept[InvalidMutualBlock](runChecked("mutual {\n}\n"))
    intercept[InvalidMutualBlock](
      runChecked("mutual {\n  def instance f (n: Nat) : Nat decreases structural(n) := 0\n}\n")
    )
    // A member's type sees no member, since the block publishes only once its bodies have checked.
    intercept[NotFound](
      runChecked(
        "mutual {\n  def f (n: Nat) : Nat decreases structural(n) := 0\n\n" +
          "  def g (n: Nat)(e: Eq(Nat, f(n), 0)) : Nat decreases structural(n) := 0\n}\n"
      )
    )
  }

  private val linearForest =
    lnats +
      """
        |mutual {
        |  inductive LTree : Lin(Level.zero)
        |   | node (label: Nat)(kids: LForest) : LTree
        |
        |  inductive LForest : Lin(Level.zero)
        |   | nil : LForest
        |   | cons (t: LTree)(rest: LForest) : LForest
        |}
        |""".stripMargin

  test("a mutual pair of linear families: fields used once, through mutual recursion") {
    run(
      linearForest +
        """
          |mutual {
          |  def collectT (t: LTree)(acc: LNats) : LNats decreases structural(t) := {
          |    match t returning LNats with
          |    | LTree.node label kids => collectF(kids, LNats.cons(label, acc))
          |  }
          |
          |  def collectF (f: LForest)(acc: LNats) : LNats decreases structural(f) := {
          |    match f returning LNats with
          |    | LForest.nil => acc
          |    | LForest.cons t rest => collectF(rest, collectT(t, acc))
          |  }
          |}
          |
          |def sample : Nat :=
          |  count(collectT(LTree.node(1, LForest.cons(LTree.node(2, LForest.nil), LForest.nil)), LNats.nil))
          |
          |def two : Eq(Nat, sample, 2) := Eq.refl(2)
          |""".stripMargin
    )
    assertErrorAt[LinearReused](
      linearForest +
        """
          |mutual {
          |  def collectT (t: LTree)(acc: LNats) : LNats decreases structural(t) := {
          |    match t returning LNats with
          |    | LTree.node label kids => collectF(kids, acc)
          |  }
          |
          |  def collectF (f: LForest)(acc: LNats) : LNats decreases structural(f) := {
          |    match f returning LNats with
          |    | LForest.nil => acc
          |    | LForest.cons t rest => collectF(rest, collectT(t, acc))
          |  }
          |
          |  def twice (f: LForest)(acc: LNats) : LNats decreases structural(f) := {
          |    match f returning LNats with
          |    | LForest.nil => acc
          |    | LForest.cons t rest => collectF(rest, collectT(t, collectT(t, acc)))
          |  }
          |}
          |""".stripMargin,
      "t",
      "t, acc)))"
    )
  }

  test("linear mutual families follow L1 over kinds, each against its own family's kind") {
    // A copyable family holds no field of a linear sibling, while a linear one may hold a copyable sibling.
    assertErrorAt[LinearFieldInUnrestrictedFamily](
      """
        |mutual {
        |  inductive C : Type
        |   | mk (l: L) : C
        |
        |  inductive L : Lin(Level.zero)
        |   | mk (c: C) : L
        |}
        |""".stripMargin,
      "(l: L)"
    )
    run(
      """
        |mutual {
        |  inductive C : Type
        |   | leaf : C
        |   | mk (n: Nat) : C
        |
        |  inductive L : Lin(Level.zero)
        |   | mk (c: C)(rest: L) : L
        |   | stop : L
        |}
        |""".stripMargin
    )
    // Kind-polymorphic siblings: each is of its parameters' kind, and a sibling field is read by its declared kind.
    run(
      """
        |mutual {
        |  inductive T (A: Univ($k, $u)) : Univ(k, u)
        |   | node (x: $A in Univ($k, $u))(f: F(A)) : T(A)
        |
        |  inductive F (A: Univ($k, $u)) : Univ(k, u)
        |   | nil {A: Univ($k, $u)} : F(A)
        |   | cons {A: Univ($k, $u)} (t: T(A))(rest: F(A)) : F(A)
        |}
        |
        |mutual {
        |  def sizeT (A: Univ($k, $u))(t: T(A)) : Nat decreases structural(t) := {
        |    match t returning Nat with
        |    | T.node x f => Nat.succ(sizeF(A, f))
        |  }
        |
        |  def sizeF (A: Univ($k, $u))(f: F(A)) : Nat decreases structural(f) := {
        |    match f returning Nat with
        |    | F.nil => 0
        |    | F.cons t rest => Nat.add(sizeT(A, t), sizeF(A, rest))
        |  }
        |}
        |
        |def copyable : Eq(Nat, sizeT(Nat, T.node(0, F.cons(Nat, T.node(1, F.nil(Nat)), F.nil(Nat)))), 2) := Eq.refl(2)
        |""".stripMargin
    )
  }

  test("in a read extent, mutual definitions only read their linear parameters, with separation per call") {
    run(
      linearForest +
        """
          |mutual {
          |  def SmallT (t: LTree) : Prop decreases structural(t) := {
          |    match t returning Prop with
          |    | LTree.node label kids => And(Eq(Nat, label, label), SmallF(kids))
          |  }
          |
          |  def SmallF (f: LForest) : Prop decreases structural(f) := {
          |    match f returning Prop with
          |    | LForest.nil => True
          |    | LForest.cons t rest => And(SmallT(t), SmallF(rest))
          |  }
          |}
          |
          |def both (t: LTree) : Prop := And(SmallT(t), SmallT(t))
          |""".stripMargin
    )
    assertErrorAt[LinearReusedInType](
      linearForest + both +
        """
          |mutual {
          |  def SelfT (t: LTree) : Prop decreases structural(t) := {
          |    match t returning Prop with
          |    | LTree.node label kids => PairF(kids, kids)
          |  }
          |
          |  def PairF (f: LForest)(g: LForest) : Prop decreases structural(f) := True
          |}
          """.stripMargin,
      "kids",
      "kids)"
    )
  }

  test("a nested family: a block's family nested in another family, with mutual recursion through it") {
    run(
      """
        |mutual {
        |  inductive T : Type
        |   | mk (us: List(U)) : T
        |
        |  inductive U : Type
        |   | leaf : U
        |   | wrap (t: T) : U
        |}
        |
        |mutual {
        |  def sizeT (t: T) : Nat decreases structural(t) := {
        |    match t returning Nat with
        |    | T.mk us => Nat.succ(sizeL(us))
        |  }
        |
        |  def sizeL (us: List(U)) : Nat decreases structural(us) := {
        |    match us returning Nat with
        |    | List.nil => 0
        |    | List.cons u rest => Nat.add(sizeU(u), sizeL(rest))
        |  }
        |
        |  def sizeU (u: U) : Nat decreases structural(u) := {
        |    match u returning Nat with
        |    | U.leaf => 1
        |    | U.wrap t => sizeT(t)
        |  }
        |}
        |
        |def three : Eq(Nat, sizeT(T.mk(List.cons(U.leaf, List.cons(U.wrap(T.mk(List.nil(U))), List.nil(U))))), 3) := Eq.refl(3)
        |""".stripMargin
    )
    // A sibling in a sibling's own arguments is no strictly positive occurrence, nor is one under a binder's domain.
    assertErrorAt[NonStrictlyPositive](
      """
        |mutual {
        |  inductive A : Type
        |   | mk (f: (b: B) -> Nat) : A
        |
        |  inductive B : Type
        |   | mk (a: A) : B
        |}
        |""".stripMargin,
      "(f: (b: B) -> Nat)"
    )
    assertErrorAt[NonStrictlyPositive](
      """
        |mutual {
        |  inductive W (X: Type) : Type
        |   | mk {X: Type} (x: X) : W(X)
        |
        |  inductive V : Type
        |   | mk (w: W(V)) : V
        |}
        |""".stripMargin,
      "(w: W(V))"
    )
  }

  test("an argument is positive only if every position it reaches is, as a fixed point over the block") {
    // `B` reaches `F`'s first argument, which `f` makes negative, so `H` occurs negatively in `F(Nat, H)`. Reading
    // `F`'s own occurrence by its provisional metadata, every argument positive, accepted it.
    assertErrorAt[NonStrictlyPositive](
      """
        |inductive F (A: Type)(B: Type) : Type
        | | leaf {A: Type}{B: Type} : F(A, B)
        | | mk {A: Type}{B: Type} (f: (a: A) -> Nat)(x: F(B, A)) : F(A, B)
        |
        |inductive H : Type
        | | mk (h: F(Nat, H)) : H
        |""".stripMargin,
      "(h: F(Nat, H))"
    )
    assertErrorAt[NonStrictlyPositive](
      """
        |mutual {
        |  inductive F (A: Type)(B: Type) : Type
        |   | leaf {A: Type}{B: Type} : F(A, B)
        |   | mk {A: Type}{B: Type} (x: G(B, A)) : F(A, B)
        |
        |  inductive G (A: Type)(B: Type) : Type
        |   | mk {A: Type}{B: Type} (f: (a: A) -> Nat)(y: F(A, B)) : G(A, B)
        |}
        |
        |inductive H : Type
        | | mk (h: F(Nat, H)) : H
        |""".stripMargin,
      "(h: F(Nat, H))"
    )
    run(
      """
        |inductive Rose (A: Type) : Type
        | | node {A: Type} (label: A)(kids: List(Rose(A))) : Rose(A)
        |
        |inductive Holds : Type
        | | mk (r: Rose(Holds)) : Holds
        |""".stripMargin
    )
  }

  test("mutual Prop families, and recursion on their proofs") {
    run(
      """
        |mutual {
        |  inductive IsEven indices (n: Nat) : Prop
        |   | zero : IsEven(0)
        |   | succ (n: Nat)(h: IsOdd(n)) : IsEven(Nat.succ(n))
        |
        |  inductive IsOdd indices (n: Nat) : Prop
        |   | succ (n: Nat)(h: IsEven(n)) : IsOdd(Nat.succ(n))
        |}
        |
        |mutual {
        |  def evenTrue (n: Nat)(h: IsEven(n)) : True decreases structural(h) := {
        |    match h returning True with
        |    | IsEven.zero => True.intro
        |    | IsEven.succ m p => oddTrue(m, p)
        |  }
        |
        |  def oddTrue (n: Nat)(h: IsOdd(n)) : True decreases structural(h) := {
        |    match h returning True with
        |    | IsOdd.succ m p => evenTrue(m, p)
        |  }
        |}
        |
        |def two : IsEven(2) := IsEven.succ(1, IsOdd.succ(0, IsEven.zero))
        |""".stripMargin
    )
  }

  test("each family of a block is bounded by its own declared universe") {
    assertErrorAt[InductiveUniverseTooSmall](
      """
        |mutual {
        |  inductive Small : Type
        |   | mk (b: Big) : Small
        |
        |  inductive Big : Sort(Level.one)
        |   | mk (T: Type)(s: Small) : Big
        |}
        |""".stripMargin,
      "(b: Big)"
    )
    run(
      """
        |mutual {
        |  inductive Small : Type
        |   | leaf : Small
        |   | mk (n: Nat) : Small
        |
        |  inductive Big : Sort(Level.one)
        |   | mk (T: Type)(s: Small)(b: Big) : Big
        |   | stop : Big
        |}
        |""".stripMargin
    )
    assertErrorAt[FamilyArgumentTooLarge](
      """
        |mutual {
        |  inductive P (F: (X: Type) -> Type) : Type
        |   | mk {F: (X: Type) -> Type} (q: Q) : P(F)
        |
        |  inductive Q : Sort(Level.one)
        |   | mk (F: (X: Type) -> Type) : Q
        |}
        |""".stripMargin,
      "(F: (X: Type) -> Type)",
      "inductive P (F: (X: Type) -> Type)"
    )
  }
}
