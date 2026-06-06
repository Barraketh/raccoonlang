package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class MathlibPilotTests extends munit.FunSuite {
  private def typecheckDecls(src: String): Unit =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        try {
          val core = Elaborator.elab(value, Prelude.default)
          Interpreter.run(core, Prelude.default)
        }
        catch {
          case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private val setCore =
    """
      |namespace MathlibPilot {
      |  struct Set (A: Sort($u)) : Sort(u)
      |   | mk {A: Sort($u)} (mem: A -> Prop) : Set(A)
      |
      |  namespace Set {
      |    def univ (A: Sort($u)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => True)
      |
      |    def empty (A: Sort($u)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => False)
      |
      |    def inter (A: Sort($u))(s: Set(A))(t: Set(A)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => And(Set.mem(s)(x), Set.mem(t)(x)))
      |
      |    def union (A: Sort($u))(s: Set(A))(t: Set(A)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => Or(Set.mem(s)(x), Set.mem(t)(x)))
      |
      |    def compl (A: Sort($u))(s: Set(A)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => Not(Set.mem(s)(x)))
      |
      |    def diff (A: Sort($u))(s: Set(A))(t: Set(A)): Set(A) :=
      |      Set.inter(A, s, Set.compl(A, t))
      |
      |    def singleton (a: $A in Sort($u)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => Eq(A, x, a))
      |
      |    def preimage (A: Sort($u))(B: Sort($v))(f: A -> B)(s: Set(B)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => Set.mem(s)(f(x)))
      |
      |    def image (A: Sort($u))(B: Sort($v))(f: A -> B)(s: Set(A)): Set(B) :=
      |      Set.mk(B, fun (y: B): Prop =>
      |        Exists(A, fun (x: A): Prop => And(Set.mem(s)(x), Eq(B, f(x), y))))
      |
      |    struct Subset (A: Sort($u))(s: Set(A))(t: Set(A)) : Prop
      |     | intro {A: Sort($u)}{s: Set(A)}{t: Set(A)} (apply: (x: A) -> Set.mem(s)(x) -> Set.mem(t)(x)) : Subset(A, s, t)
      |
      |    def subsetRefl (A: Sort($u))(s: Set(A)): Subset(A, s, s) :=
      |      Subset.intro(A, s, s, fun (x: A)(hx: (Set.mem(s)(x))): Set.mem(s)(x) => hx)
      |
      |    def subsetTrans (h1: Subset($A, $s, $t))(h2: Subset(A, t, $u)): Subset(A, s, u) :=
      |      Subset.intro(A, s, u, fun (x: A)(hx: (Set.mem(s)(x))): Set.mem(u)(x) => h2.apply(x, h1.apply(x, hx)))
      |
      |    def emptySubset (A: Sort($u))(s: Set(A)): Subset(A, empty(A), s) :=
      |      Subset.intro(A, empty(A), s, fun (x: A)(hx: (Set.mem(empty(A))(x))): Set.mem(s)(x) => falseElim(hx, Set.mem(s)(x)))
      |
      |    def subsetUniv (A: Sort($u))(s: Set(A)): Subset(A, s, univ(A)) :=
      |      Subset.intro(A, s, univ(A), fun (x: A)(hx: (Set.mem(s)(x))): Set.mem(univ(A))(x) => True.intro)
      |
      |    def interSubsetLeft (A: Sort($u))(s: Set(A))(t: Set(A)): Subset(A, inter(A, s, t), s) :=
      |      Subset.intro(A, inter(A, s, t), s, fun (x: A)(hx: (Set.mem(inter(A, s, t))(x))): Set.mem(s)(x) => And.left(hx))
      |
      |    def interSubsetRight (A: Sort($u))(s: Set(A))(t: Set(A)): Subset(A, inter(A, s, t), t) :=
      |      Subset.intro(A, inter(A, s, t), t, fun (x: A)(hx: (Set.mem(inter(A, s, t))(x))): Set.mem(t)(x) => And.right(hx))
      |
      |    def subsetInter (h1: Subset($A, $u, $s))(h2: Subset(A, u, $t)): Subset(A, u, inter(A, s, t)) :=
      |      Subset.intro(A, u, inter(A, s, t), fun (x: A)(hx: (Set.mem(u)(x))): Set.mem(inter(A, s, t))(x) =>
      |        And.intro(Set.mem(s)(x), Set.mem(t)(x), h1.apply(x, hx), h2.apply(x, hx)))
      |
      |    def subsetUnionLeft (A: Sort($u))(s: Set(A))(t: Set(A)): Subset(A, s, union(A, s, t)) :=
      |      Subset.intro(A, s, union(A, s, t), fun (x: A)(hx: (Set.mem(s)(x))): Set.mem(union(A, s, t))(x) => Or.inl(Set.mem(t)(x), hx))
      |
      |    def subsetUnionRight (A: Sort($u))(s: Set(A))(t: Set(A)): Subset(A, t, union(A, s, t)) :=
      |      Subset.intro(A, t, union(A, s, t), fun (x: A)(hx: (Set.mem(t)(x))): Set.mem(union(A, s, t))(x) => Or.inr(Set.mem(s)(x), hx))
      |
      |    def unionSubset (h1: Subset($A, $s, $u))(h2: Subset(A, $t, u)): Subset(A, union(A, s, t), u) :=
      |      Subset.intro(A, union(A, s, t), u, fun (x: A)(hx: (Set.mem(union(A, s, t))(x))): Set.mem(u)(x) =>
      |        Or.elim(hx, Set.mem(u)(x), fun (hs: (Set.mem(s)(x))): Set.mem(u)(x) => h1.apply(x, hs), fun (ht: (Set.mem(t)(x))): Set.mem(u)(x) => h2.apply(x, ht)))
      |
      |    def diffSubset (A: Sort($u))(s: Set(A))(t: Set(A)): Subset(A, diff(A, s, t), s) :=
      |      interSubsetLeft(A, s, compl(A, t))
      |
      |    def memSingletonSelf (a: $A in Sort($u)): Set.mem(singleton(a))(a) :=
      |      Eq.refl(a)
      |
      |    def singletonSubset (a: $A in Sort($u))(s: Set(A))(h: (Set.mem(s)(a))): Subset(A, singleton(a), s) :=
      |      Subset.intro(A, singleton(a), s, fun (x: A)(hx: (Set.mem(singleton(a))(x))): Set.mem(s)(x) =>
      |        Eq.subst(Eq.symm(hx), Level.zero, fun (z: A): Prop => Set.mem(s)(z), h))
      |
      |    def imageIntro (A: Sort($u))(B: Sort($v))(f: A -> B)(s: Set(A))(x: A)(hx: (Set.mem(s)(x))): Set.mem(image(A, B, f, s))(f(x)) :=
      |      Exists.intro(
      |        A,
      |        fun (w: A): Prop => And(Set.mem(s)(w), Eq(B, f(w), f(x))),
      |        x,
      |        And.intro(Set.mem(s)(x), Eq(B, f(x), f(x)), hx, Eq.refl(f(x)))
      |      )
      |
      |    def ext (s: Set($A))(t: Set(A))(h: (x: A) -> Iff(Set.mem(s)(x), Set.mem(t)(x))): Eq(Set(A), s, t) := {
      |      match s returning Eq(Set(A), s, t) with
      |      | Set.mk smem => {
      |        match t returning Eq(Set(A), Set.mk(A, smem), t) with
      |        | Set.mk tmem => {
      |          let memEq := funext(
      |            A,
      |            Level.one,
      |            fun (x: A): Type => Prop,
      |            smem,
      |            tmem,
      |            fun (x: A): Eq(Prop, smem(x), tmem(x)) => propext(h(x))
      |          )
      |          match memEq returning Eq(Set(A), Set.mk(A, smem), Set.mk(A, tmem)) with
      |          | Eq.refl pred => Eq.refl(Set.mk(A, pred))
      |        }
      |      }
      |    }
      |
      |    def subsetAntisymm (h1: Subset($A, $s, $t))(h2: Subset(A, t, s)): Eq(Set(A), s, t) :=
      |      ext(s, t, fun (x: A): Iff(Set.mem(s)(x), Set.mem(t)(x)) =>
      |        Iff.intro(
      |          Set.mem(s)(x),
      |          Set.mem(t)(x),
      |          fun (hs: (Set.mem(s)(x))): Set.mem(t)(x) => h1.apply(x, hs),
      |          fun (ht: (Set.mem(t)(x))): Set.mem(s)(x) => h2.apply(x, ht)
      |        ))
      |  }
      |}
      |""".stripMargin

  test("Set-like core definitions and subset lemmas typecheck") {
    typecheckDecls(setCore)
  }

  test("Set-like constructors can be combined in mathlib-shaped code") {
    typecheckDecls(
      setCore +
        """
          |namespace MathlibPilot {
          |  def natZeros : Set(Nat) := Set.singleton(Nat.zero)
          |
          |  def natZerosMem (x: Nat): Prop := Set.mem(natZeros)(x)
          |
          |  def idNat (n: Nat): Nat := n
          |
          |  def natUniverseContainsZero : Set.mem(Set.univ(Nat))(Nat.zero) := True.intro
          |
          |  def singletonIsNonempty : Exists(Nat, natZerosMem) :=
          |    Exists.intro(Nat, natZerosMem, Nat.zero, Set.memSingletonSelf(Nat.zero))
          |
          |  def zerosSubsetUniverse : Set.Subset(Nat, natZeros, Set.univ(Nat)) :=
          |    Set.subsetUniv(Nat, natZeros)
          |
          |  def zerosSubsetUnion (s: Set(Nat)): Set.Subset(Nat, natZeros, Set.union(Nat, natZeros, s)) :=
          |    Set.subsetUnionLeft(Nat, natZeros, s)
          |
          |  def interZerosLeft (s: Set(Nat)): Set.Subset(Nat, Set.inter(Nat, natZeros, s), natZeros) :=
          |    Set.interSubsetLeft(Nat, natZeros, s)
          |
          |  def preimageContainsZero : Set.mem(Set.preimage(Nat, Nat, idNat, natZeros))(Nat.zero) :=
          |    Set.memSingletonSelf(Nat.zero)
          |
          |  def imageContainsZero : Set.mem(Set.image(Nat, Nat, idNat, natZeros))(Nat.zero) :=
          |    Set.imageIntro(Nat, Nat, idNat, natZeros, Nat.zero, Set.memSingletonSelf(Nat.zero))
          |}
          |""".stripMargin
    )
  }

  test("Set extensionality and subset antisymmetry typecheck") {
    typecheckDecls(
      setCore +
        """
          |namespace MathlibPilot {
          |  def sameSingletons : Eq(Set(Nat), Set.singleton(Nat.zero), Set.singleton(Nat.zero)) :=
          |    Set.subsetAntisymm(
          |      Set.subsetRefl(Nat, Set.singleton(Nat.zero)),
          |      Set.subsetRefl(Nat, Set.singleton(Nat.zero))
          |    )
          |}
          |""".stripMargin
    )
  }
}
