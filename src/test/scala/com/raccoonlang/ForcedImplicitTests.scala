package com.raccoonlang

class ForcedImplicitTests extends munit.FunSuite {
  private def checked(src: String): Value = TestSupport.check(src)._2.map(_.value).getOrElse(fail("Expected result"))
  test("level implicits are projected through sort levels") {
    val src = "\n" + """
                       |inductive Nat : Type
                       | | zero : Nat
                       |
                       |def idUp {u: Level}(A: Sort(Level.succ(u)))(x: A): A := x
                       |{ idUp(Type, Nat) }
                       |""".stripMargin
    checked(src)
  }

  test("constructor family parameters are inferred when forced by a field") {
    val src = "\n" + """
                       |inductive Nat : Type
                       | | zero : Nat
                       |
                       |inductive Box (A: Type) : Type
                       | | mk (x: A) : Box(A)
                       |{ Box.mk(Nat.zero) }
                       |""".stripMargin
    assert(checked(src).toString.contains("Box.mk"))
  }

  test("Pi domain and codomain positions force implicits") {
    val src =
      "inductive Peano : Type\n | zero : Peano\n | succ (n: Peano) : Peano\n\n" +
        "def compose {A: Type}{B: Type}{C: Type} (f: B -> C)(g: A -> B)(x: A): C := f(g(x))\n" +
        "{ compose(Peano.succ, Peano.succ, Peano.zero) }\n"
    assert(TestSupport.eval(src).toString.contains("Peano.succ"))
  }

  test("per-constructor demotion keeps forced family parameters implicit") {
    val src =
      "inductive Peano : Type\n | zero : Peano\n | succ (n: Peano) : Peano\n\n" +
        "inductive Either (A: Type)(B: Type) : Type\n" +
        " | inl (left: A) : Either(A, B)\n" +
        " | inr (right: B) : Either(A, B)\n\n" +
        "def swap (A: Type)(B: Type)(e: Either(A, B)): Either(B, A) := {\n match e returning Either(B, A) with\n | Either.inl x => Either.inr(B, x)\n | Either.inr y => Either.inl(A, y)\n}\n" +
        "{ swap(Peano, Peano, Either.inl(Peano, Peano.zero)) }\n"
    assert(TestSupport.eval(src).toString.contains("Either.inr"))
  }

  test("demoted family parameters cannot be omitted") {
    val src =
      "inductive Peano : Type\n | zero : Peano\n | succ (n: Peano) : Peano\n\n" +
        "inductive Either (A: Type)(B: Type) : Type\n" +
        " | inl (left: A) : Either(A, B)\n" +
        " | inr (right: B) : Either(A, B)\n\n" +
        "{ Either.inl(Peano.zero) }\n"
    intercept[ArityMismatch](TestSupport.check(src))
  }

  test("residual evaluation reconstructs constructor implicits") {
    val src =
      "inductive Peano : Type\n | zero : Peano\n | succ (n: Peano) : Peano\n\n" +
        "inductive Box {u: Level}(A: Sort(u)) : Sort(u)\n | mk (a: A) : Box(A)\n\n" +
        "def unbox {u: Level}{A: Sort(u)} (b: Box(A)): A := {\n match b returning A with\n | Box.mk a => a\n}\n" +
        "def twice (b: Box(Peano)): Peano := Peano.succ(Peano.succ(unbox(b)))\n" +
        "{ twice(Box.mk(Peano.zero)) }\n"
    assert(TestSupport.eval(src).toString.contains("Peano.succ"))
  }

  test("generated selectors reconstruct implicit non-Level family parameters") {
    val src =
      "inductive Peano : Type\n | zero : Peano\n | succ (n: Peano) : Peano\n\n" +
        "struct S {A: Type}(x: A) : Type\n | mk (y: A) : S(x)\n" +
        "{ S.y(S.mk(Peano.zero, Peano.succ(Peano.zero))) }\n"
    assert(TestSupport.eval(src).toString.contains("Peano.succ"))
  }

  test("expected Pi adaptation is available only from literal Pi syntax") {
    val literal =
      "inductive Peano : Type\n | zero : Peano\n | succ (n: Peano) : Peano\n\n" +
        "def idL {u: Level}{A: Sort(u)} (x: A): A := x\n" +
        "def idPeano : (x: Peano) -> Peano := idL\n{ idPeano(Peano.zero) }\n"
    assert(TestSupport.eval(literal).toString.contains("Peano.zero"))
    val argument =
      "inductive Peano : Type\n | zero : Peano\n\n" +
        "def idL {u: Level}{A: Sort(u)} (x: A): A := x\n" +
        "def apply1 {A: Type}(a: A)(f: (x: A) -> A): A := f(a)\n" +
        "{ apply1(Peano.zero, idL) }\n"
    intercept[TypeMismatch](TestSupport.check(argument))
    val alias =
      "inductive Peano : Type\n | zero : Peano\n\n" +
        "def idL {u: Level}{A: Sort(u)} (x: A): A := x\n" +
        "{ let t : Type := (x: Peano) -> Peano\n let f : t := idL\n f(Peano.zero) }\n"
    intercept[TypeMismatch](TestSupport.check(alias))
  }

  test("expected Pis retain forced implicit binders") {
    val src =
      "inductive Peano : Type\n | zero : Peano\n | succ (n: Peano) : Peano\n\n" +
        "def idL {u: Level}{A: Sort(u)} (x: A): A := x\n" +
        "{ let f : {A: Type} -> (x: A) -> A := idL f(Peano.succ(Peano.zero)) }\n"
    assert(TestSupport.eval(src).toString.contains("Peano.succ"))
  }

  test("recursive calls reconstruct implicit arguments") {
    val src =
      "inductive Peano : Type\n | zero : Peano\n | succ (n: Peano) : Peano\n\n" +
        "def loop {A: Type}(n: Peano)(x: A): Peano decreases structural(n) := {\n" +
        " match n returning Peano with\n | Peano.zero => Peano.zero\n | Peano.succ k => Peano.succ(loop(k, x))\n}\n" +
        "{ loop(Peano.succ(Peano.zero), Peano.zero) }\n"
    assert(TestSupport.eval(src).toString.contains("Peano.succ"))
  }

  test("Pi groups are consumed one call at a time, including dependent codomains") {
    val src =
      "inductive Peano : Type\n | zero : Peano\n\n" +
        "def make {A: Type}(x: A): (y: A) -> A := fun (y: A): A => x\n" +
        "{ make(Peano.zero)(Peano.zero) }\n"
    assert(TestSupport.eval(src).toString.contains("Peano.zero"))
    val valueDependent =
      "inductive Bool : Type\n | true : Bool\n | false : Bool\n\n" +
        "inductive Peano : Type\n | zero : Peano\n | succ (n: Peano) : Peano\n\n" +
        "def F (b: Bool): Type := match b returning Type with\n" +
        " | Bool.true => (n: Peano) -> Peano\n" +
        " | Bool.false => Peano\n\n" +
        "def g (b: Bool): F(b) := match b returning F(b) with\n" +
        " | Bool.true => fun (n: Peano): Peano => Peano.succ(n)\n" +
        " | Bool.false => Peano.zero\n" +
        "{ g(Bool.true)(Peano.zero) }\n"
    val valueResult = TestSupport.eval(valueDependent).toString
    assert(valueResult.contains("Peano.succ"), valueResult)
    intercept[ArityMismatch](
      TestSupport.check(valueDependent.replace("g(Bool.true)(Peano.zero)", "g(Bool.true, Peano.zero)"))
    )
    val nestedWrong =
      "axiom nested : (A: Type)(x: A) -> ((y: A) -> A)\n{ nested(Type, Type, Type) }\n"
    intercept[ArityMismatch](TestSupport.check(nestedWrong))
    val wrong =
      "inductive Peano : Type\n | zero : Peano\n\n" +
        "def grouped (A: Type)(x: A)(y: A): A := x\n{ grouped(Nat.zero) }\n"
    intercept[ArityMismatch](TestSupport.check(wrong.replace("Nat.zero", "Peano.zero")))
  }

  test("differently grouped function types are not convertible") {
    val src =
      "axiom curried : (A: Type)(x: A) -> ((y: A) -> A)\n" +
        "axiom grouped : (A: Type)(x: A)(y: A) -> A\n"
    val (env, _) = TestSupport.check(src)
    assert(!ValueEquivalence.defEq(env("curried").tpe, env("grouped").tpe))
  }

  test("structure eta still checks through an implicit reconstruction") {
    val src =
      "inductive Eq (A: Type) indices (a: A)(b: A) : Type\n | refl (x: A) : Eq(A, x, x)\n\n" +
        "struct Pair (A: Type)(B: Type) : Type\n | mk (fst: A)(snd: B) : Pair(A, B)\n\n" +
        "def eta {A: Type}{B: Type} (p: Pair(A, B)): Eq(Pair(A, B), p, Pair.mk(p.fst, p.snd)) := Eq.refl(p)\n"
    TestSupport.check(src)
  }
}
