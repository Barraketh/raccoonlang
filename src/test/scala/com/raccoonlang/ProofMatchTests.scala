package com.raccoonlang

import com.raccoonlang.ProgramFixtures.Programs

/**
 * Proof matches (docs/kernel.md, "Proof calls"): a match from a suspended proof into a proposition does not force its
 * scrutinee, and applying a suspended proof of a function proposition does not force it. The checker reads such a
 * scrutinee by its proposition, whether or not something forced it earlier; a match into a type that is no proposition
 * forces it and sees its forced value, as before.
 */
class ProofMatchTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = true)
  import programs._

  /** `big(n)` computes `2^n`, `NatValueTooLarge` beyond an Int exponent, so a run of `big(2^32)` shows a demand. */
  private val lib =
    """
      |def big (n: Nat) : True := {
      |  let x := Nat.pow(2, n)
      |  True.intro
      |}
      |
      |def pick (n: Nat) : Or(Eq(Nat, n, n), False) := Or.inl(False, Eq.refl(n))
      |
      |""".stripMargin

  private val tooLarge = "4294967296"

  // Rule 1: a match from a suspended proof into a proposition is a proof match, run only on demand.

  test("a match into a proposition on a proof call is a suspension, which nothing demands") {
    val src =
      lib +
        s"""
           |def t : True := {
           |  match big($tooLarge) returning True with
           |  | True.intro => True.intro
           |}
           |
           |Nat.zero
           |""".stripMargin
    assert(declsEnv(src).apply("t").isInstanceOf[Value.VProofMatch])
    assertEquals(result(src), "0")
  }

  test("a match into a proposition on a constructor value or a variable is evaluated as before") {
    val src =
      """
        |def k : True := {
        |  match Or.inl(False, True.intro) returning True with
        |  | Or.inl h => h
        |}
        |def v (p: Or(True, True)) : True := {
        |  match p returning True with
        |  | Or.inl h => h
        |  | Or.inr h => h
        |}
        |""".stripMargin
    val env = declsEnv(src)
    assertEquals(PrettyPrinter.print(env("k")), "True.intro")
    assert(!env("k").isInstanceOf[Value.VSuspendedProof])
  }

  test("a demanded proof match forces its scrutinee and takes its branch, to a constructor or a stuck value") {
    // Printing the result demands it.
    assertEquals(
      result(
        lib +
          """
            |def t : Eq(Nat, 3, 3) := {
            |  match pick(3) returning Eq(Nat, 3, 3) with
            |  | Or.inl e => e
            |  | Or.inr f => False.elimProp(f, Eq(Nat, 3, 3))
            |}
            |
            |t
            |""".stripMargin
      ),
      "Eq.refl(3)"
    )
    intercept[NatValueTooLarge](
      runChecked(lib + s"{\n  match big($tooLarge) returning True with\n  | True.intro => True.intro\n}\n")
    )
  }

  test("a proof match nested in a suspended call's run stays suspended, and the chain forces through it") {
    // `step` runs on demand; its own match is on its argument, a suspension from outside the run.
    assertEquals(
      result(
        """
          |def step (h: And(True, True)) : And(True, True) := {
          |  match h returning And(True, True) with
          |  | And.intro a b => And.intro(True, True, b, a)
          |}
          |def two : And(True, True) := step(step(And.intro(True, True, True.intro, True.intro)))
          |two
          |""".stripMargin
      ),
      "And.intro(True.intro, True.intro)"
    )
  }

  test("a proof field's projection out of a proof call is a proof match, which nothing demands") {
    val src =
      s"""
         |inductive Both : Prop
         | | mk (a: True)(b: True) : Both
         |
         |def both (n: Nat) : Both := {
         |  let x := Nat.pow(2, n)
         |  Both.mk(True.intro, True.intro)
         |}
         |
         |def t : True := both($tooLarge).b
         |
         |Nat.zero
         |""".stripMargin
    val t = declsEnv(src).apply("t")
    assert(t.isInstanceOf[Value.VProofMatch])
    // A failed run prints as its computation, the projection.
    assertEquals(PrettyPrinter.print(t), s"both($tooLarge).b")
    assertEquals(result(src), "0")
    intercept[NatValueTooLarge](runChecked(src.replace("Nat.zero", "t")))
  }

  test("a data field's projection out of a proof call demands it, as a large elimination") {
    val src =
      """
        |inductive IsN indices (n: Nat) : Prop
        | | mk (n: Nat) : IsN(n)
        |
        |def isN (k: Nat)(n: Nat) : IsN(n) := {
        |  let x := Nat.pow(2, k)
        |  IsN.mk(n)
        |}
        |
        |def three : Nat := isN(0, 3).n
        |
        |three
        |""".stripMargin
    assertEquals(result(src), "3")
    intercept[NatValueTooLarge](runChecked(src.replace("isN(0, 3)", s"isN($tooLarge, 3)")))
  }

  // Rule 2: applying a suspended proof of a function proposition is a proof application.

  test("applying a suspended proof of a function proposition does not demand it") {
    val src =
      s"""
         |def allBig (k: Nat) : (n: Nat) -> True := {
         |  let x := Nat.pow(2, k)
         |  fun (n: Nat): True => True.intro
         |}
         |
         |def t : True := allBig($tooLarge)(5)
         |
         |Nat.zero
         |""".stripMargin
    assert(declsEnv(src).apply("t").isInstanceOf[Value.VProofApply])
    assertEquals(result(src), "0")
    intercept[NatValueTooLarge](runChecked(src.replace("Nat.zero", "t")))
  }

  // Rule 3: a match into a type that is no proposition forces its scrutinee, and reduces at a constructor.

  test("a large elimination forces a proof call and reduces at its forced constructor") {
    intercept[NatValueTooLarge](
      runChecked(lib + s"def n : Nat := {\n  match big($tooLarge) returning Nat with\n  | True.intro => 3\n}\n")
    )
    assertEquals(
      result(
        """
          |def lemT (n: Nat) : True := True.intro
          |def three : Nat := {
          |  match lemT(0) returning Nat with
          |  | True.intro => 3
          |}
          |def ok : Eq(Nat, three, 3) := Eq.refl(3)
          |three
          |""".stripMargin
      ),
      "3"
    )
  }

  // Rule 4: the checker's known-constructor view needs a constructor value, or a large elimination.

  test("a match into a proposition on a proof call is checked by type: every case it allows, and only those") {
    intercept[MissingCase](
      runChecked(lib + "def t : True := {\n  match pick(3) returning True with\n  | Or.inl h => True.intro\n}\n")
    )
    runChecked(
      lib +
        """
          |def t : True := {
          |  match pick(3) returning True with
          |  | Or.inl h => True.intro
          |  | Or.inr h => True.intro
          |}
          |""".stripMargin
    )
    // The index refutes `Le.s` by type.
    val le =
      """
        |inductive Le indices (n: Nat) : Prop
        | | z : Le(0)
        | | s (n: Nat)(h: Le(n)) : Le(Nat.succ(n))
        |def lemZ (u: Unit) : Le(0) := Le.z
        |""".stripMargin
    intercept[UnreachableCase](
      runChecked(
        le + "def t : True := {\n  match lemZ(Unit.unit) returning True with\n  | Le.z => True.intro\n" +
          "  | Le.s m h => True.intro\n}\n"
      )
    )
    runChecked(le + "def t : True := {\n  match lemZ(Unit.unit) returning True with\n  | Le.z => True.intro\n}\n")
  }

  test("the view of a proof call matched into a proposition does not depend on an earlier demand of it") {
    // `h` is forced by the large elimination `k`, a subsingleton elimination of `And`, in the first program of each
    // pair and by nothing in the second. Its forced value's first field is `Or.inl`, so a view of the forced value
    // would need the `Or.inl` case alone; by type, `a` is a fresh proof of `Or(True, False)`, so both are needed.
    val lemA =
      """
        |def lemA (k: Nat) : And(Or(True, False), True) := {
        |  let x := Nat.pow(2, k)
        |  And.intro(Or(True, False), True, Or.inl(False, True.intro), True.intro)
        |}
        |""".stripMargin
    val demand = "  let k : Nat := {\n    match h returning Nat with\n    | And.intro a b => 0\n  }\n"
    def program(exponent: String, demanded: Boolean, cases: String) =
      lemA + s"def t : True := {\n  let h := lemA($exponent)\n" + (if (demanded) demand else "") +
        "  match h returning True with\n  | And.intro a b => {\n    match a returning True with\n" + cases +
        "  }\n}\nNat.zero\n"
    val one = "    | Or.inl t => t\n"
    val both = one + "    | Or.inr f => False.elimProp(f, True)\n"
    // The demand runs h: at a run that fails, only the program that demands it fails.
    intercept[NatValueTooLarge](runChecked(program(tooLarge, demanded = true, both)))
    assertEquals(result(program(tooLarge, demanded = false, both)), "0")
    for (demanded <- Seq(true, false)) {
      intercept[MissingCase](runChecked(program("3", demanded, one)))
      assertEquals(result(program("3", demanded, both)), "0")
    }
  }

  test("a large elimination of a proof call keeps the forced view: its constructor's fields are the forced ones") {
    // The forced field `a` is `Or.inl`, a constructor value, so the inner match into a proposition needs that case
    // alone, and `Or.inr` is unreachable there.
    val src =
      """
        |def lemA (n: Nat) : And(Or(True, False), True) :=
        |  And.intro(Or(True, False), True, Or.inl(False, True.intro), True.intro)
        |def n : Nat := {
        |  match lemA(0) returning Nat with
        |  | And.intro a b => {
        |    let t : True := {
        |      match a returning True with
        |      | Or.inl x => x
        |    }
        |    7
        |  }
        |}
        |n
        |""".stripMargin
    assertEquals(result(src), "7")
    intercept[UnreachableCase](
      runChecked(
        src.replace("      | Or.inl x => x\n", "      | Or.inl x => x\n      | Or.inr y => False.elimProp(y, True)\n")
      )
    )
  }

  test("with an inferred motive, a match on a proof call is checked by type, and its universe decides its value") {
    // Into a proposition: a proof match, which nothing demands.
    val prop =
      lib +
        s"""
           |def t : True := {
           |  let x := {
           |    match big($tooLarge) with
           |    | True.intro => True.intro
           |  }
           |  True.intro
           |}
           |Nat.zero
           |""".stripMargin
    assertEquals(result(prop), "0")
    intercept[MissingCase](
      runChecked(
        lib + "def t : True := {\n  let x := {\n    match pick(3) with\n    | Or.inl h => True.intro\n  }\n  x\n}\n"
      )
    )
    // Into data: a large elimination, checked by type, whose value forces the scrutinee and reduces.
    assertEquals(
      result(
        """
          |def lemT (n: Nat) : True := True.intro
          |def three : Nat := {
          |  let x := {
          |    match lemT(0) with
          |    | True.intro => 3
          |  }
          |  x
          |}
          |def ok : Eq(Nat, three, 3) := Eq.refl(3)
          |three
          |""".stripMargin
      ),
      "3"
    )
  }
}
