package com.raccoonlang

import com.raccoonlang.ErrorReporter.Source

class MathlibPilotTests extends munit.FunSuite {
  private def typecheckDecls(src: String): Unit =
    LanguageParser.parseProgram(src) match {
      case Success(value, _, _) =>
        try {
          val core = Elaborator.elab(value, Prelude.default)
          Interpreter.run(core, Prelude.default)
        } catch {
          case t: TypeError => fail(ErrorReporter.pretty(t, Source(src)))
        }
      case err: Failure =>
        fail(s"Failed to parse: $err, ${src.substring(err.curIdx)}")
    }

  private val setCore =
    """
      |namespace MathlibPilot {
      |  // Lean: def Set (A : Type u) := A -> Prop
      |  struct Set (A: Sort($u)) : Sort(u)
      |   | mk (apply: A -> Prop) : Set(A)
      |
      |  namespace Set {
      |    // Lean: def mem (s : Set A) (x : A) : Prop := s x
      |    def mem (s: Set($A))(x: A): Prop := s(x)
      |
      |    // Lean: def univ : Set A := fun _ => True
      |    def univ (A: Sort($u)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => True)
      |
      |    // Lean: def empty : Set A := fun _ => False
      |    def empty (A: Sort($u)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => False)
      |
      |    // Lean: def inter (s t : Set A) : Set A := fun x => And (s x) (t x)
      |    def inter (s: Set($A))(t: Set(A)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => And(s(x), t(x)))
      |
      |    // Lean: def union (s t : Set A) : Set A := fun x => Or (s x) (t x)
      |    def union (s: Set($A))(t: Set(A)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => Or(s(x), t(x)))
      |
      |    // Lean: def compl (s : Set A) : Set A := fun x => Not (s x)
      |    def compl (s: Set($A)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => Not(s(x)))
      |
      |    // Lean: def diff (s t : Set A) : Set A := inter s (compl t)
      |    def diff (s: Set($A))(t: Set(A)): Set(A) :=
      |      Set.inter(s, Set.compl(t))
      |
      |    // Lean: def singleton (a : A) : Set A := fun x => Eq x a
      |    def singleton (a: $A in Sort($u)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => Eq(A, x, a))
      |
      |    // Lean: def preimage (f : A -> B) (s : Set B) : Set A := fun x => s (f x)
      |    def preimage (A: Sort($u))(B: Sort($v))(f: A -> B)(s: Set(B)): Set(A) :=
      |      Set.mk(A, fun (x: A): Prop => s(f(x)))
      |
      |    // Lean: def image (f : A -> B) (s : Set A) : Set B := fun y => Exists fun x => And (s x) (f x = y)
      |    def image (A: Sort($u))(B: Sort($v))(f: A -> B)(s: Set(A)): Set(B) :=
      |      Set.mk(B, fun (y: B): Prop => Exists(A, fun (x: A): Prop => And(s(x), Eq(B, f(x), y))))
      |
      |    // Lean: def Subset (s t : Set A) : Prop := forall x, s x -> t x
      |    struct Subset (s: Set($A))(t: Set(A)) : Prop
      |     | intro (apply: (x: A) -> s(x) -> t(x)) : Subset(s, t)
      |
      |    // Lean: theorem subsetRefl (s : Set A) : Subset s s := fun x hx => hx
      |    def subsetRefl (s: Set($A)): Subset(s, s) :=
      |      Subset.intro(s, s, fun (x: A)(hx: (s(x))): s(x) => hx)
      |
      |    // Lean: theorem subsetTrans (h1 : Subset s t) (h2 : Subset t u) : Subset s u
      |    def subsetTrans (h1: Subset($s, $t))(h2: Subset(t, $u)): Subset(s, u) :=
      |      Subset.intro(s, u, fun (x: A)(hx: (s(x))): u(x) => h2(x, h1(x, hx)))
      |
      |    // Lean: theorem emptySubset (s : Set A) : Subset empty s
      |    def emptySubset (s: Set($A)): Subset(empty(A), s) :=
      |      Subset.intro(empty(A), s, fun (x: A)(hx: (empty(A)(x))): s(x) => falseElim(hx, s(x)))
      |
      |    // Lean: theorem subsetUniv (s : Set A) : Subset s univ
      |    def subsetUniv (s: Set($A)): Subset(s, univ(A)) :=
      |      Subset.intro(s, univ(A), fun (x: A)(hx: (s(x))): univ(A)(x) => True.intro)
      |
      |    // Lean: theorem interSubsetLeft (s t : Set A) : Subset (inter s t) s
      |    def interSubsetLeft (s: Set($A))(t: Set(A)): Subset(inter(s, t), s) :=
      |      Subset.intro(inter(s, t), s, fun (x: A)(hx: (inter(s, t)(x))): s(x) => And.left(hx))
      |
      |    // Lean: theorem interSubsetRight (s t : Set A) : Subset (inter s t) t
      |    def interSubsetRight (s: Set($A))(t: Set(A)): Subset(inter(s, t), t) :=
      |      Subset.intro(inter(s, t), t, fun (x: A)(hx: (inter(s, t)(x))): t(x) => And.right(hx))
      |
      |    // Lean: theorem subsetInter (h1 : Subset u s) (h2 : Subset u t) : Subset u (inter s t)
      |    def subsetInter (h1: Subset($u, $s))(h2: Subset(u, $t)): Subset(u, inter(s, t)) :=
      |      Subset.intro(u, inter(s, t), fun (x: A)(hx: (u(x))): inter(s, t)(x) =>
      |        And.intro(s(x), t(x), h1(x, hx), h2(x, hx)))
      |
      |    // Lean: theorem subsetUnionLeft (s t : Set A) : Subset s (union s t)
      |    def subsetUnionLeft (s: Set($A))(t: Set(A)): Subset(s, union(s, t)) :=
      |      Subset.intro(s, union(s, t), fun (x: A)(hx: (s(x))): union(s, t)(x) => Or.inl(t(x), hx))
      |
      |    // Lean: theorem subsetUnionRight (s t : Set A) : Subset t (union s t)
      |    def subsetUnionRight (s: Set($A))(t: Set(A)): Subset(t, union(s, t)) :=
      |      Subset.intro(t, union(s, t), fun (x: A)(hx: (t(x))): union(s, t)(x) => Or.inr(s(x), hx))
      |
      |    // Lean: theorem unionSubset (h1 : Subset s u) (h2 : Subset t u) : Subset (union s t) u
      |    def unionSubset (h1: Subset($s, $u))(h2: Subset($t, u)): Subset(union(s, t), u) :=
      |      Subset.intro(union(s, t), u, fun (x: A)(hx: (union(s, t)(x))): u(x) =>
      |        Or.elim(hx, u(x), fun (hs: (s(x))): u(x) => h1(x, hs), fun (ht: (t(x))): u(x) => h2(x, ht)))
      |
      |    // Lean: theorem diffSubset (s t : Set A) : Subset (diff s t) s
      |    def diffSubset (s: Set($A))(t: Set(A)): Subset(diff(s, t), s) :=
      |      interSubsetLeft(s, compl(t))
      |
      |    // Lean: theorem memSingletonSelf (a : A) : singleton a a := Eq.refl a
      |    def memSingletonSelf (a: $A in Sort($u)): singleton(a)(a) :=
      |      Eq.refl(a)
      |
      |    // Lean: theorem singletonSubset (h : s a) : Subset (singleton a) s
      |    def singletonSubset (a: $A in Sort($u))(s: Set(A))(h: (s(a))): Subset(singleton(a), s) :=
      |      Subset.intro(singleton(a), s, fun (x: A)(hx: (singleton(a)(x))): s(x) =>
      |        Eq.subst(Eq.symm(hx), Level.zero, fun (z: A): Prop => s(z), h))
      |
      |    // Lean: theorem imageIntro (hx : s x) : image f s (f x)
      |    def imageIntro (A: Sort($u))(B: Sort($v))(f: A -> B)(s: Set(A))(x: A)(hx: (s(x))): image(A, B, f, s)(f(x)) :=
      |      Exists.intro(
      |        A,
      |        fun (w: A): Prop => And(s(w), Eq(B, f(w), f(x))),
      |        x,
      |        And.intro(s(x), Eq(B, f(x), f(x)), hx, Eq.refl(f(x)))
      |      )
      |
      |    // Lean: theorem ext (h : forall x, Iff (s x) (t x)) : Eq s t
      |    def ext (s: Set($A))(t: Set(A))(h: (x: A) -> Iff(s(x), t(x))): Eq(Set(A), s, t) :=
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
      |
      |    // Lean: theorem subsetAntisymm (h1 : Subset s t) (h2 : Subset t s) : Eq s t
      |    def subsetAntisymm (h1: Subset($s, $t))(h2: Subset(t, s)): Eq(Set(A), s, t) :=
      |      ext(s, t, fun (x: A): Iff(s(x), t(x)) =>
      |        Iff.intro(
      |          s(x),
      |          t(x),
      |          fun (hs: (s(x))): t(x) => h1(x, hs),
      |          fun (ht: (t(x))): s(x) => h2(x, ht)
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
          |  // Lean: def natZeros : Set Nat := singleton Nat.zero
          |  def natZeros : Set(Nat) := Set.singleton(Nat.zero)
          |
          |  // Lean: def natZerosMem (x : Nat) : Prop := natZeros x
          |  def natZerosMem (x: Nat): Prop := natZeros(x)
          |
          |  // Lean: def idNat (n : Nat) : Nat := n
          |  def idNat (n: Nat): Nat := n
          |
          |  // Lean: def natUniverseContainsZero : Set.mem Set.univ Nat.zero := True.intro
          |  def natUniverseContainsZero : Set.mem(Set.univ(Nat), Nat.zero) := True.intro
          |
          |  // Lean: def singletonIsNonempty : Exists natZerosMem := Exists.intro Nat.zero ...
          |  def singletonIsNonempty : Exists(Nat, natZerosMem) :=
          |    Exists.intro(Nat, natZerosMem, Nat.zero, Set.memSingletonSelf(Nat.zero))
          |
          |  // Lean: def zerosSubsetUniverse : Subset natZeros Set.univ := subsetUniv natZeros
          |  def zerosSubsetUniverse : Set.Subset(natZeros, Set.univ(Nat)) :=
          |    Set.subsetUniv(natZeros)
          |
          |  // Lean: def zerosSubsetUnion (s : Set Nat) : Subset natZeros (union natZeros s)
          |  def zerosSubsetUnion (s: Set(Nat)): Set.Subset(natZeros, Set.union(natZeros, s)) :=
          |    Set.subsetUnionLeft(natZeros, s)
          |
          |  // Lean: def interZerosLeft (s : Set Nat) : Subset (inter natZeros s) natZeros
          |  def interZerosLeft (s: Set(Nat)): Set.Subset(Set.inter(natZeros, s), natZeros) :=
          |    Set.interSubsetLeft(natZeros, s)
          |
          |  // Lean: def preimageContainsZero : Set.mem (preimage idNat natZeros) Nat.zero
          |  def preimageContainsZero : Set.mem(Set.preimage(Nat, Nat, idNat, natZeros), Nat.zero) :=
          |    Set.memSingletonSelf(Nat.zero)
          |
          |  // Lean: def imageContainsZero : Set.mem (image idNat natZeros) Nat.zero
          |  def imageContainsZero : Set.mem(Set.image(Nat, Nat, idNat, natZeros), Nat.zero) :=
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
          |  // Lean: def sameSingletons : Eq (singleton Nat.zero) (singleton Nat.zero)
          |  def sameSingletons : Eq(Set(Nat), Set.singleton(Nat.zero), Set.singleton(Nat.zero)) :=
          |    Set.subsetAntisymm(
          |      Set.subsetRefl(Set.singleton(Nat.zero)),
          |      Set.subsetRefl(Set.singleton(Nat.zero))
          |    )
          |}
          |""".stripMargin
    )
  }
}
