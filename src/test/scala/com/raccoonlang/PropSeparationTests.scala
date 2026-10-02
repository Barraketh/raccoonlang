package com.raccoonlang

/** Soundness regressions use the final Type syntax, so rejection tests sort separation. */
class PropSeparationTests extends munit.FunSuite with TestSupport {
  test("the polymorphic Option discriminator cannot instantiate at a proposition") {
    val definitions =
      """
        |def someTrue {u: Level}{A: Type { level = u }}(a: A): Eq(Bool, Option.isSome(Option.some(a)), Bool.true) := Eq.refl(Bool.true)
        |def noneFalse {u: Level}(A: Type { level = u }): Eq(Bool, Option.isSome(Option.none(A)), Bool.false) := Eq.refl(Bool.false)
        |""".stripMargin
    typecheckDecls(definitions)
    expectOnly[ImplicitReconstructionFailed](typecheckDecls(definitions + "def bad : Type := Option(True)\n"))
    expectOnly[ImplicitReconstructionFailed](
      typecheckDecls(definitions + "def bad : Eq(Bool, Bool.true, Bool.true) := someTrue(True.intro)\n")
    )
    expectOnly[ImplicitReconstructionFailed](
      typecheckDecls(definitions + "def bad : Eq(Bool, Bool.false, Bool.false) := noneFalse(True)\n")
    )
  }

  test("the polymorphic Sum clash refutation cannot instantiate at a proposition") {
    val definitions =
      """
        |def refuteClash {u: Level}(A: Type { level = u })(x: A)(h: Eq(Sum(A, A), Sum.inl(A, x), Sum.inr(A, x))): False := {
        |  match h returning False with
        |}
        |""".stripMargin
    typecheckDecls(definitions)
    expectOnly[ImplicitReconstructionFailed](
      typecheckDecls(
        definitions + "def boom : False := refuteClash(True, True.intro, Eq.refl(Sum.inl(True, True.intro)))\n"
      )
    )
    expectOnly[ImplicitReconstructionFailed](typecheckDecls("def bad : Type := Sum(True, True)\n"))
  }

  test("equality cannot quantify over erased proofs") {
    expectOnly[ImplicitReconstructionFailed](typecheckDecls("def bad (P: Prop)(h: P): Eq(P, h, h) := Eq.refl(h)\n"))
    typecheckDecls("def irrel (P: Prop)(Q: P -> Prop)(h1: P)(h2: P)(q: Q(h1)): Q(h2) := q\n")
  }

  test("implicit constructor projections cannot receive erased data instances") {
    val definitions = """
                        |struct Box {u: Level}(A: Type { level = u }) : Type { level = u }
                        | | mk (x: A) : Box(A)
                        |def extract {u: Level}{A: Type { level = u }}(box: Box(A)): A := box.x
                        |""".stripMargin
    typecheckDecls(definitions)
    expectOnly[ImplicitReconstructionFailed](
      typecheckDecls(definitions + "def bad (box: Box(True)): True := extract(box)\n")
    )
    expectOnly[ImplicitReconstructionFailed](typecheckDecls("def bad : Option(Nat) := Option.some(True.intro)\n"))
  }

  test("a proposition field fits a data family at level zero") {
    typecheckDecls(
      "struct Box (P: Prop) : Type\n | mk (proof: P) : Box(P)\ndef good : Box(True) := Box.mk(True.intro)\n"
    )
  }
}
