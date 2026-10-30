package com.raccoonlang

import com.raccoonlang.ProgramFixtures._

/**
 * A match that names its equation, `match h : e returning M with …` (docs/kernel.md, "Match equations";
 * KERNEL_FOLLOWUPS 2.7): in the case of constructor `C` with fields `x̄`, `h : Eq(T, e, C(x̄))`.
 */
class MatchEquationTests extends munit.FunSuite {
  private val programs = new Programs(Prelude.default, allowUserAxioms = false)
  import programs._

  private val needs =
    """
      |def needs (a: Nat)(b: Nat)(fits: Eq(Bool, Nat.ble(a, b), Bool.true)) : Nat := a
      |""".stripMargin

  test("a case passes its equation on as evidence, in a structural recursion, and evaluates") {
    val src =
      needs +
        """
          |def sumFitting (a: Nat)(b: Nat)(left: Nat) : Nat decreases structural(left) := {
          |  match left returning Nat with
          |  | Nat.zero => 0
          |  | Nat.succ more => {
          |    match fits : Nat.ble(a, b) returning Nat with
          |    | Bool.true => Nat.add(needs(a, b, fits), sumFitting(a, b, more))
          |    | Bool.false => sumFitting(a, b, more)
          |  }
          |}
          |""".stripMargin
    assertEquals(result(src + "\nNat.add(sumFitting(2, 5, 3), sumFitting(7, 5, 3))\n"), "6")
    // Without it, nothing proves the fact at a variable.
    assertErrorAt[TypeMismatch](
      needs +
        """
          |def tryNeeds (a: Nat)(b: Nat) : Nat := {
          |  match Nat.ble(a, b) returning Nat with
          |  | Bool.true => needs(a, b, Eq.refl(Bool.true))
          |  | Bool.false => 0
          |}
          |""".stripMargin,
      "(a, b, Eq.refl(Bool.true))"
    )
  }

  test("a proof by cases on a computed value, with the equation as the hypothesis of each") {
    run(
      """
        |def Zero (n: Nat) : Prop := Eq(Bool, Nat.isZero(n), Bool.true)
        |def NotZero (n: Nat) : Prop := Eq(Bool, Nat.isZero(n), Bool.false)
        |
        |def byCases (n: Nat) : Or(Zero(n), NotZero(n)) := {
        |  match h : Nat.isZero(n) returning Or(Zero(n), NotZero(n)) with
        |  | Bool.true => Or.inl(NotZero(n), h)
        |  | Bool.false => Or.inr(Zero(n), h)
        |}
        |
        |def twice (n: Nat) : And(Zero(0), Zero(0)) := {
        |  match h : Nat.isZero(0) returning And(Zero(0), Zero(0)) with
        |  | Bool.true => And.intro(Zero(0), Zero(0), h, h)
        |}
        |""".stripMargin
    )
  }

  test("a variable scrutinee's equation is at its refined value, and a lambda may capture it") {
    run(
      """
        |def pred (n: Nat) : Nat := {
        |  match e : n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => (fun (p: Eq(Nat, n, Nat.succ(k))): Nat => k)(e)
        |}
        |
        |def three : Eq(Nat, pred(4), 3) := Eq.refl(3)
        |""".stripMargin
    )
  }

  private val vec =
    """
      |inductive Vec (A: Type) indices (n: Nat) : Type
      | | nil {A: Type} : Vec(A, Nat.zero)
      | | cons {A: Type} (tail: Vec(A, $n)) (head: A) : Vec(A, Nat.succ(n))
      |""".stripMargin

  test("an indexed family: the equation needs the case's refinement to equate the indices") {
    run(
      vec +
        """
          |def len (A: Type)(n: Nat)(v: Vec(A, n)) : Nat := {
          |  match h : v returning Nat with
          |  | Vec.nil => 0
          |  | Vec.cons tail head => 1
          |}
          |
          |def tailOf (A: Type)(n: Nat)(v: Vec(A, Nat.succ(n))) : Vec(A, n) := {
          |  match h : v returning Vec(A, n) with
          |  | Vec.cons tail head => tail
          |}
          |""".stripMargin
    )
    assertErrorAt[MatchEquationIndexed](
      vec +
        """
          |def stuck (A: Type)(f: (m: Nat) -> Nat)(n: Nat)(v: Vec(A, f(n))) : Nat := {
          |  match h : v returning Nat with
          |  | Vec.nil => 0
          |  | Vec.cons tail head => 1
          |}
          |""".stripMargin,
      "h",
      "h : v"
    )
  }

  test("the scrutinee must be copyable data: Eq has no linear carrier and ranges over no proofs") {
    assertErrorAt[MatchEquationUnavailable](
      lnats +
        """
          |def f (xs: LNats) : Nat := {
          |  match h : xs returning Nat with
          |  | LNats.nil => 0
          |  | LNats.cons a rest => 1
          |}
          |""".stripMargin,
      "h",
      "h : xs"
    )
    assertErrorAt[MatchEquationUnavailable](
      """
        |def f (A: Univ($k, $u))(o: Option(A)) : Nat := {
        |  match h : o returning Nat with
        |  | Option.none => 0
        |  | Option.some a => 1
        |}
        |""".stripMargin,
      "h",
      "h : o"
    )
    assertErrorAt[MatchEquationUnavailable](
      """
        |def f (p: Or(True, True)) : True := {
        |  match h : p returning True with
        |  | Or.inl a => a
        |  | Or.inr b => b
        |}
        |""".stripMargin,
      "h",
      "h : p"
    )
  }

  test("the equation's Eq must be exactly the equality family") {
    val noPrelude = new Programs(Prelude.none, allowUserAxioms = true)
    val program =
      """
        |def f (n: Nat) : Nat := {
        |  match h : n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => 1
        |}
        |""".stripMargin
    intercept[MatchEquationUnavailable](noPrelude.runChecked(program))
    // An `Eq` with a second constructor would make every equation provable.
    intercept[MatchEquationUnavailable](
      noPrelude.runChecked(
        """
          |inductive Eq (A: Sort($u)) indices (x: A)(y: A) : Prop
          | | refl (x: $A in Sort($u)) : Eq(A, x, x)
          | | any (x: $A in Sort($u))(y: A) : Eq(A, x, y)
          |""".stripMargin + program
      )
    )
    // One that ranges over `Type` only would leave larger scrutinees without an equation.
    intercept[MatchEquationUnavailable](
      noPrelude.runChecked(
        """
          |inductive Eq (A: Type) indices (x: A)(y: A) : Prop
          | | refl (x: $A in Type) : Eq(A, x, x)
          |""".stripMargin + program
      )
    )
    // The prelude's own form, declared anywhere, is the equality family.
    noPrelude.run(
      """
        |inductive Eq (A: Sort($u)) indices (x: A)(y: A) : Prop
        | | refl (x: $A in Sort($u)) : Eq(A, x, x)
        |""".stripMargin + program
    )
  }

  private val color =
    """
      |inductive Color : Type
      | | red : Color
      | | green : Color
      | | blue : Color
      |
      |def noted (p: Eq(Color, $c, $d)) : Nat := 1
      |def greenOnly (p: Eq(Color, Color.green, Color.green)) : Nat := 2
      |""".stripMargin

  test("with a wildcard, each expanded case binds the equation at its own constructor") {
    run(
      color +
        """
          |def which (c: Color) : Nat := {
          |  match h : c returning Nat with
          |  | Color.red => 0
          |  | _ => noted(h)
          |}
          |
          |def one : Eq(Nat, which(Color.blue), 1) := Eq.refl(1)
          |""".stripMargin
    )
    assertErrorAt[TypeMismatch](
      color +
        """
          |def which (c: Color) : Nat := {
          |  match h : c returning Nat with
          |  | Color.red => 0
          |  | _ => greenOnly(h)
          |}
          |""".stripMargin,
      "(h)",
      "greenOnly(h)"
    )
  }

  test("an equation's name is a local of every case, apart from the fields, and the residual keeps it") {
    intercept[AlreadyDefined](
      runChecked(
        "def f (n: Nat) : Nat := {\n  match h : n returning Nat with\n  | Nat.zero => 0\n  | Nat.succ h => 1\n}\n"
      )
    )
    // Not in the scrutinee or the motive.
    intercept[NotFound](runChecked("def f (n: Nat) : Nat := {\n  match h : h returning Nat with\n  | _ => 0\n}\n"))
    val env = declsEnv(
      needs +
        """
          |def tryNeeds (a: Nat)(b: Nat) : Nat := {
          |  match fits : Nat.ble(a, b) returning Nat with
          |  | Bool.true => needs(a, b, fits)
          |  | Bool.false => 0
          |}
          |""".stripMargin
    )
    env("tryNeeds") match {
      case Value.VLam(_, _, Value.LamBody.Core(term, _)) =>
        assert(PrettyPrinter.printElabTerm(term).contains("match fits : "), PrettyPrinter.printElabTerm(term))
      case other => fail(s"tryNeeds is $other")
    }
  }

  test("a blocked match binds nothing, and a structure eta match runs its case with the equation") {
    run(
      """
        |def swap (p: Prod(Nat, Nat)) : Prod(Nat, Nat) := {
        |  match h : p returning Prod(Nat, Nat) with
        |  | Prod.mk a b => Prod.mk(Nat, Nat, b, a)
        |}
        |
        |def swapTwice (p: Prod(Nat, Nat)) : Eq(Prod(Nat, Nat), swap(swap(p)), p) := Eq.refl(p)
        |
        |def pred (n: Nat) : Nat := {
        |  match e : n returning Nat with
        |  | Nat.zero => 0
        |  | Nat.succ k => k
        |}
        |
        |def stuck (n: Nat) : Eq(Nat, pred(n), pred(n)) := Eq.refl(pred(n))
        |""".stripMargin
    )
  }
}
