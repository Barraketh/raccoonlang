package com.raccoonlang

/** C11 structure eta. Implicit-parameter and Prop/proof cases are deferred to later stages. */
class StructEtaTests extends munit.FunSuite {
  private val eq = "inductive Eq (A: Type) indices (a: A)(b: A) : Type\n | refl (x: A) : Eq(A, x, x)\n\n"
  private val pair = "struct Pair (A: Type)(B: Type) : Type\n | mk (fst: A)(snd: B) : Pair(A, B)\n\n"
  private val nat = "inductive Nat : Type\n | zero : Nat\n | succ (n: Nat) : Nat\n\n"

  test("binder eta expands to constructor of projections") {
    val src = eq + nat + pair +
      "def eta (p: Pair(Nat, Nat)): Eq(Pair(Nat, Nat), p, Pair.mk(p.fst, p.snd)) := Eq.refl(p)\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("plain one-constructor inductive eta uses explicit match accessors") {
    val src = eq + nat +
      "inductive Plain (A: Type)(B: Type) : Type\n | mk (left: A)(right: B) : Plain(A, B)\n\n" +
      "def getLeft (p: Plain(Nat, Nat)): Nat := { match p returning Nat with\n | Plain.mk left right => left\n}\n" +
      "def getRight (p: Plain(Nat, Nat)): Nat := { match p returning Nat with\n | Plain.mk left right => right\n}\n" +
      "def eta (p: Plain(Nat, Nat)): Eq(Plain(Nat, Nat), p, Plain.mk(getLeft(p), getRight(p))) := Eq.refl(p)\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("dependent fields preserve the dependent eta view") {
    val src = eq +
      "axiom A : Type\naxiom B : A -> Type\n\n" +
      "struct Sig (A: Type)(B: A -> Type) : Type\n | mk (fst: A)(snd: B(fst)) : Sig(A, B)\n\n" +
      "def eta (s: Sig(A, B)): Eq(Sig(A, B), s, Sig.mk(B, s.fst, s.snd)) := Eq.refl(s)\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("opaque constant eta") {
    val src = eq + nat + pair +
      "opaque def c : Pair(Nat, Nat) := Pair.mk(Nat.zero, Nat.zero)\n" +
      "def eta : Eq(Pair(Nat, Nat), c, Pair.mk(c.fst, c.snd)) := Eq.refl(c)\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("axiom eta") {
    val src = eq + nat + pair +
      "axiom a : Pair(Nat, Nat)\n" +
      "def eta : Eq(Pair(Nat, Nat), a, Pair.mk(a.fst, a.snd)) := Eq.refl(a)\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("unit-like eta makes all values equal") {
    val src = eq +
      "struct One : Type\n | mk : One\n\n" +
      "def unique (a: One)(b: One): Eq(One, a, b) := Eq.refl(a)\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("blocked struct-valued match eta") {
    val src = eq + nat + pair +
      "opaque def step (n: Nat): Nat := n\n" +
      "def pick (n: Nat): Pair(Nat, Nat) := { match step(n) returning Pair(Nat, Nat) with\n" +
      " | Nat.zero => Pair.mk(Nat.zero, Nat.zero)\n" +
      " | Nat.succ k => Pair.mk(k, n)\n}\n" +
      "def eta (n: Nat): Eq(Pair(Nat, Nat), pick(n), Pair.mk(pick(n).fst, pick(n).snd)) := Eq.refl(pick(n))\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("matching a struct binder fires with virtual projected fields") {
    val src = eq + nat + pair +
      "def swap (p: Pair(Nat, Nat)): Pair(Nat, Nat) := { match p returning Pair(Nat, Nat) with\n" +
      " | Pair.mk fst snd => Pair.mk(snd, fst)\n}\n" +
      "def eta (p: Pair(Nat, Nat)): Eq(Pair(Nat, Nat), swap(p), Pair.mk(p.snd, p.fst)) := Eq.refl(swap(p))\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("nested structure fields expand recursively") {
    val src = eq + nat + pair +
      "struct Box (A: Type) : Type\n | mk (inner: A) : Box(A)\n\n" +
      "def eta (b: Box(Pair(Nat, Nat))): Eq(Pair(Nat, Nat), b.inner, Pair.mk(b.inner.fst, b.inner.snd)) := Eq.refl(b.inner)\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("concrete constructor evaluation is unchanged") {
    val src = nat + pair +
      "def pick (n: Nat): Pair(Nat, Nat) := { match n returning Pair(Nat, Nat) with\n" +
      " | Nat.zero => Pair.mk(Nat.zero, Nat.succ(Nat.zero))\n" +
      " | Nat.succ k => Pair.mk(k, n)\n}\n"
    val value = TestSupport.eval(src + "\n{ let p := pick(Nat.zero) p.snd }\n")
    assertEquals(PrettyPrinter.print(value), "Nat.succ(Nat.zero())")
  }

  test("recursive structures are not eta-eligible") {
    val src = eq + "struct Wrap : Type\n | mk (w: Wrap) : Wrap\n\n" +
      "def eta (x: Wrap): Eq(Wrap, x, Wrap.mk(x.w)) := Eq.refl(x)\n"
    val error = intercept[TypeMismatch](TypeChecker.checkProgram(TestSupport.core(src)))
    assert(error.getMessage.contains("Type mismatch"))
  }

  test("indexed structures are not eta-eligible") {
    val src = eq + nat + "struct Indexed indices (n: Nat) : Type\n | mk (k: Nat) : Indexed(k)\n\n" +
      "def eta (n: Nat)(x: Indexed(n)): Eq(Indexed(n), x, Indexed.mk(x.k)) := Eq.refl(Indexed(n), x)\n"
    val error = intercept[TypeMismatch](TypeChecker.checkProgram(TestSupport.core(src)))
    assert(error.getMessage.contains("Type mismatch"))
  }

  test("user selectors equal canonical kernel projections") {
    val src = eq + nat + pair +
      "axiom p : Pair(Nat, Nat)\n" +
      "def selector (p: Pair(Nat, Nat)): Eq(Nat, Pair.fst(p), p.fst) := Eq.refl(p.fst)\n" +
      "def eta : Eq(Pair(Nat, Nat), p, Pair.mk(p.fst, p.snd)) := Eq.refl(p)\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("a variable refined to a structure gets eta in its branch") {
    val src = eq + nat + pair +
      "inductive Tag indices (A: Type) : Type\n | isPair : Tag(Pair(Nat, Nat))\n\n" +
      "def refined (A: Type)(x: A)(t: Tag(A)): Nat := { match t returning Nat with\n" +
      " | Tag.isPair => { let same : Eq(Pair(Nat, Nat), x, Pair.mk(x.fst, x.snd)) := Eq.refl(x) x.fst }\n}\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("dependent selectors agree with branch pattern variables") {
    val src =
      "struct Sig (A: Type)(B: A -> Type) : Type\n | mk (fst: A)(snd: B(fst)) : Sig(A, B)\n\n" +
        "axiom A : Type\naxiom B : A -> Type\n\n" +
        "def use (s: Sig(A, B)): B(s.fst) := { match s returning B(s.fst) with\n | Sig.mk a b => b\n}\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("termination measure decreases through a projected field") {
    val src = nat + pair +
      "def countdown (p: Pair(Nat, Nat)): Nat decreases measure(p.fst) := { match p.fst returning Nat with\n" +
      " | Nat.zero => Nat.zero\n" +
      " | Nat.succ k => countdown(Pair.mk(k, p.snd))\n}\n"
    TypeChecker.checkProgram(TestSupport.core(src))
  }

  test("distinct flat struct neutrals remain unequal") {
    val src = eq + nat + pair +
      "def bad (a: Pair(Nat, Nat))(b: Pair(Nat, Nat)): Eq(Pair(Nat, Nat), a, b) := Eq.refl(a)\n"
    intercept[TypeMismatch](TypeChecker.checkProgram(TestSupport.core(src)))
  }

  test("distinct nested struct neutrals remain unequal and terminate") {
    val src = eq + nat + pair +
      "def bad (a: Pair(Pair(Nat, Nat), Nat))(b: Pair(Pair(Nat, Nat), Nat)): Eq(Pair(Pair(Nat, Nat), Nat), a, b) := Eq.refl(a)\n"
    intercept[TypeMismatch](TypeChecker.checkProgram(TestSupport.core(src)))
  }
}
