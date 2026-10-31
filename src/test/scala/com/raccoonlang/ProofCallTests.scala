package com.raccoonlang

import com.raccoonlang.ProgramFixtures.Programs

/**
 * Proof calls (docs/kernel.md, "Proof calls"): a call to a checked lambda whose function type is a proposition is a
 * suspension, run once, when something reads the proof's form. These programs check, or fail, as they did when every
 * call ran at once, except where a test says the proof match rule changed it: a match from a suspended proof into a
 * proposition reads it by its proposition, so it needs every case its type allows. The first one only checks because an
 * undemanded proof never runs.
 */
class ProofCallTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = true)
  import programs._

  /** `pick(n)`, whose forced value is `Or.inl`, and `idp`, a proof call that returns its argument. */
  private val lib =
    """
      |def pick (n: Nat) : Or(Eq(Nat, n, n), False) := Or.inl(False, Eq.refl(n))
      |
      |def idp (p: Prop)(h: p) : p := h
      |
      |""".stripMargin

  test("a proof nothing demands never runs, so one too deep for the stack checks") {
    assertEquals(
      result(
        """
          |def deep (n: Nat) : True decreases structural(n) := {
          |  match n returning True with
          |  | Nat.zero => True.intro
          |  | Nat.succ k => {
          |    let h := deep(k)
          |    h
          |  }
          |}
          |
          |def t : True := deep(1000000)
          |
          |Nat.zero
          |""".stripMargin
      ),
      "0"
    )
  }

  test("a match into a proposition leaves a proof call suspended, so the checker reads it by its proposition") {
    // Changed by proof match suspension: the forced value, `Or.inl`, made `Or.inr` unreachable, and the first program
    // checked with its one case. Now every case its type allows is required, and printing runs the match.
    intercept[MissingCase](
      runChecked(
        lib +
          """
            |def f : True := {
            |  match pick(3) returning True with
            |  | Or.inl h => True.intro
            |}
            |""".stripMargin
      )
    )
    assertEquals(
      result(
        lib +
          """
            |def f : True := {
            |  match pick(3) returning True with
            |  | Or.inl h => True.intro
            |  | Or.inr h => True.intro
            |}
            |
            |f
            |""".stripMargin
      ),
      "True.intro"
    )
  }

  test("forcing follows proof calls that return proof calls to the end") {
    // Printing forces the match, which forces its scrutinee through both `idp` calls to `pick(3)` 's `Or.inl`.
    assertEquals(
      result(
        lib +
          """
            |def f (n: Nat) : True := {
            |  match idp(Or(Eq(Nat, n, n), False), idp(Or(Eq(Nat, n, n), False), pick(n))) returning True with
            |  | Or.inl h => True.intro
            |  | Or.inr h => False.elimProp(h, True)
            |}
            |
            |f(3)
            |""".stripMargin
      ),
      "True.intro"
    )
  }

  test("a proof call materialized in a refined branch forces to the refined value") {
    val lem =
      """
        |def lem (n: Nat) : Or(Eq(Nat, n, 0), True) := {
        |  match n returning Or(Eq(Nat, n, 0), True) with
        |  | Nat.zero => Or.inl(True, Eq.refl(0))
        |  | Nat.succ k => Or.inr(Eq(Nat, Nat.succ(k), 0), True.intro)
        |}
        |
        |""".stripMargin
    // The zero branch's cases follow the margin-stripped text, so their own `|` stay.
    def program(zeroCases: String) =
      lem +
        """
          |def f (m: Nat) : True := {
          |  let h := lem(m)
          |  match m returning True with
          |  | Nat.zero => {
          |    match h returning True with
          |""".stripMargin + zeroCases +
        """
          |  }
          |  | Nat.succ k => True.intro
          |}
          |
          |f(0)
          |""".stripMargin
    // Changed by proof match suspension: the zero branch's match read the materialized call's forced value, `Or.inl`,
    // so it needed that case alone. Now it needs both, and running f(0) forces the call materialized at zero.
    intercept[MissingCase](runChecked(program("    | Or.inl e => True.intro")))
    assertEquals(result(program("    | Or.inl e => True.intro\n    | Or.inr t => t")), "True.intro")
  }

  test("applying a proof of a function proposition leaves it suspended, and printing forces the application") {
    val src =
      """
        |def allRefl (u: Unit) : (n: Nat) -> Eq(Nat, n, n) := fun (n: Nat): Eq(Nat, n, n) => Eq.refl(n)
        |
        |def t : Eq(Nat, 5, 5) := allRefl(Unit.unit)(5)
        |
        |t
        |""".stripMargin
    assert(declsEnv(src).apply("t").isInstanceOf[Value.VProofApply])
    assertEquals(result(src), "Eq.refl(5)")
  }

  test("the program's result is a forced proof, and printing forces the proof calls in data") {
    val lem = "def lem (n: Nat) : Eq(Nat, Nat.add(n, 0), n) := Eq.refl(n)\n\n"
    assertEquals(result(lem + "Eq.trans(lem(3), Eq.symm(lem(3)))"), "Eq.refl(3)")
    assertEquals(result(lem + "Fact.mk(Eq.symm(lem(3)))"), "Fact.mk(Eq.refl(3))")
    assertEquals(
      result(
        """
          |def lemAnd (n: Nat) : And(Eq(Nat, n, n), True) := And.intro(Eq(Nat, n, n), True, Eq.refl(n), True.intro)
          |
          |(lemAnd(4)).left
          |""".stripMargin
      ),
      "Eq.refl(4)"
    )
  }

  test("termination compares a proof call by its forced value's key") {
    val acc =
      """
        |inductive Acc2 : Prop
        | | step (h: Acc2) : Acc2
        |
        |""".stripMargin
    run(
      acc + lib +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => walk(idp(Acc2, h1))
          |}
          |
          |// The root rebuilt around a proof call of its field: unchanged, so the next component decides.
          |def walk2 (h: Acc2)(n: Nat) : True decreases lexicographic(h, n) := {
          |  match n returning True with
          |  | Nat.zero => True.intro
          |  | Nat.succ k => {
          |    match h returning True with
          |    | Acc2.step h1 => walk2(Acc2.step(idp(Acc2, h1)), k)
          |  }
          |}
          |""".stripMargin
    )
    val src =
      acc + lib +
        """
          |def walk (h: Acc2) : True decreases structural(h) := {
          |  match h returning True with
          |  | Acc2.step h1 => walk(idp(Acc2, h))
          |}
          |""".stripMargin
    assertErrorAt[NonDecreasingRecursiveCall](src, "(idp(Acc2, h))")
  }

  test("an occurs check reads a proof call's forced value, so the index links as before") {
    // The constructor's index holds `trivB(b)` at the parameter `m`, which is also the index: `m` occurs in the
    // call's argument but not in its forced value, `True.intro`, so `m` links and the branch sees the refinement.
    assertEquals(
      result(
        """
          |inductive Box : Type
          | | mk (n: Nat)(h: True) : Box
          |
          |def trivB (b: Box) : True := True.intro
          |
          |inductive Foo (b: Box) indices (c: Box) : Type
          | | mk {b: Box} (k: Nat) : Foo(b, Box.mk(k, trivB(b)))
          |
          |def f (m: Box)(x: Foo(m, m)) : Nat := {
          |  match x returning Nat with
          |  | Foo.mk k => {
          |    let e : Eq(Box, m, Box.mk(k, True.intro)) := Eq.refl(m)
          |    k
          |  }
          |}
          |
          |Nat.zero
          |""".stripMargin
      ),
      "0"
    )
  }

  test("positivity reads a proof call's forced value") {
    run(
      """
        |inductive Q (h: True) : Type
        | | mk {h: True} : Q(h)
        |
        |def triv (A: Type) : True := True.intro
        |
        |inductive T : Type
        | | leaf : T
        | | node (q: Q(triv(T))) : T
        |""".stripMargin
    )
  }

  test("a proof call whose codomain does not fit reports its forced value's type") {
    val error = assertErrorAt[TypeMismatch](
      """
        |inductive All (xs: List(Nat))(p: Nat -> Prop) : Prop
        | | mk {xs: List(Nat)}{p: Nat -> Prop} : All(xs, p)
        |
        |def lem (P: Prop)(h: P) : P := h
        |
        |def bad (xs: List(Nat))(h: All(xs, fun (a: Nat): Prop => True)) : All(xs, fun (c: Nat): Prop => False) :=
        |  lem(All(xs, fun (b: Nat): Prop => True), h)
        |""".stripMargin,
      "(All(xs, fun (b: Nat): Prop => True), h)"
    )
    assert(error.getMessage.contains("actual: All(xs#"), error.getMessage)
    assert(error.getMessage.contains("fun (a: Nat) => True)"), error.getMessage)
  }

  test("the Abel-Coquand example is accepted") {
    // main-new ConsistencyTests "Abel-Coquand Omega": with propext, acDelta(acOmega) must not loop.
    assertEquals(
      result(
        """
          |axiom acPropext (a: Prop)(b: Prop)(h: Iff(a, b)): Eq(Prop, a, b)
          |
          |def acTautext (A: Prop)(B: Prop)(a: A)(b: B): Eq(Prop, A, B) :=
          |  acPropext(A, B, Iff.intro(A, B, fun (x: A): B => b, fun (y: B): A => a))
          |
          |def ACTrue : Prop := (A: Prop) -> (a: A) -> A
          |def ACEndo : Prop := (x: ACTrue) -> ACTrue
          |def acId (x: ACTrue): ACTrue := x
          |def acDelta (z: ACTrue): ACTrue := z(ACEndo, acId)(z)
          |def acOmega (A: Prop)(a: A): A := Eq.mp(acTautext(ACEndo, A, acId, a), acDelta)
          |def acOmegaClosed : ACTrue := acDelta(acOmega)
          |
          |Nat.zero
          |""".stripMargin
      ),
      "0"
    )
  }
}
